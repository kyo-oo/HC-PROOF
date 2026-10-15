#!/usr/bin/env python3
"""GST repository-wide source and dependency census.

READ-ONLY: enumerate every tracked repository file, read all decodable source
files, and record proof-declaration/import dependencies and lexical proof escapes.
A lexical census is NOT a Lean kernel proof audit.
"""
from __future__ import annotations

import collections
import datetime
import hashlib
import json
import pathlib
import re
import subprocess

ROOT = pathlib.Path(__file__).resolve().parents[1]
OUT = ROOT / "gst_universe_census"
OUT.mkdir(exist_ok=True)
files = subprocess.check_output(
    ["git", "-C", str(ROOT), "ls-files", "-z"]
).decode("utf-8").split("\0")
paths = [p for p in files if p]
lean_files = {p[:-5].replace("/", "."): p for p in paths if p.endswith(".lean")}
decl_pat = re.compile(r"^\s*(?:private\s+|protected\s+|noncomputable\s+|unsafe\s+)?"
                      r"(theorem|lemma|def|structure|class|axiom|constant|opaque|instance|abbrev)\s+"
                      r"([a-zA-Z0-9_.']+)", re.MULTILINE)
imp_pat = re.compile(r"^\s*import\s+([^\r\n]+)", re.MULTILINE)
escape_pat = re.compile(r"\b(sorry|admit|sorryAx|native_decide|unsafe)\b")
axiom_pat = re.compile(r"^\s*(axiom|constant)\s+([a-zA-Z0-9_.']+)", re.MULTILINE)


def strip_lean_comments_and_strings(source: str) -> str:
    """Keep exact offsets/newlines while masking nested Lean comments and strings.

    Lexical (not elaborating) pass. Lean block comments /- ... -/ are nested,
    line comments start --, and double-quoted string literals can contain escapes.
    The resulting code preserves line and column positions for proof-marker reports.
    """
    chars = list(source)
    n = len(chars)
    i = 0
    block_depth = 0
    line_comment = False
    quoted_string = False
    string_escape = False

    def erase(start: int, length: int = 1) -> None:
        for j in range(start, min(n, start + length)):
            if chars[j] != "\n":
                chars[j] = " "

    while i < n:
        pair = source[i:i + 2]
        char = source[i]
        if line_comment:
            if char == "\n":
                line_comment = False
            else:
                erase(i)
            i += 1
            continue
        if block_depth:
            if pair == "/-":
                block_depth += 1
                erase(i, 2)
                i += 2
            elif pair == "-/":
                block_depth -= 1
                erase(i, 2)
                i += 2
            else:
                erase(i)
                i += 1
            continue
        if quoted_string:
            erase(i)
            if string_escape:
                string_escape = False
            elif char == "\\":
                string_escape = True
            elif char == '"':
                quoted_string = False
            i += 1
            continue
        if pair == "--":
            line_comment = True
            erase(i, 2)
            i += 2
        elif pair == "/-":
            block_depth = 1
            erase(i, 2)
            i += 2
        elif char == '"':
            quoted_string = True
            erase(i)
            i += 1
        else:
            i += 1
    return "".join(chars)


items: list[dict] = []
errors: list[dict] = []
all_imports: dict[str, list[str]] = {}
all_decls: collections.Counter = collections.Counter()
markers = []
total_bytes = 0
for path in paths:
    fp = ROOT / path
    try:
        raw = fp.read_bytes()
    except (OSError, PermissionError) as exc:
        errors.append({"path": path, "error": str(exc)})
        continue
    total_bytes += len(raw)
    is_binary = b"\x00" in raw[:8192]
    if is_binary:
        items.append({"path": path, "bytes": len(raw), "binary": True,
                      "sha256": hashlib.sha256(raw).hexdigest()})
        continue
    try:
        source = raw.decode("utf-8")
    except UnicodeDecodeError:
        items.append({"path": path, "bytes": len(raw), "binary": True,
                      "sha256": hashlib.sha256(raw).hexdigest()})
        continue
    code = strip_lean_comments_and_strings(source) if path.endswith(".lean") else source
    decs = [{"kind": m.group(1), "name": m.group(2)} for m in decl_pat.finditer(code)]
    imp = []
    if path.endswith(".lean"):
        imp = [token for m in imp_pat.finditer(code) for token in m.group(1).split()]
        all_imports[path] = imp
    for d in decs:
        all_decls[d["kind"]] += 1
    found = [{"line": source.count("\n", 0, m.start()) + 1, "token": m.group(1)}
             for m in escape_pat.finditer(code)] if path.endswith(".lean") else []
    if found:
        markers.append({"path": path, "occurrences": found})
    axioms = [{"line": source.count("\n", 0, m.start()) + 1,
               "kind": m.group(1), "name": m.group(2)}
              for m in axiom_pat.finditer(code)] if path.endswith(".lean") else []
    items.append({
        "path": path, "bytes": len(raw), "binary": False,
        "sha256": hashlib.sha256(raw).hexdigest(),
        "lines": source.count("\n") + 1,
        "imports": imp, "declarations": decs,
        "axiom_declarations": axioms,
        "executable_proof_markers": found,
    })

local_graph = {
    p: [lean_files[mod] for mod in imps if mod in lean_files]
    for p, imps in all_imports.items()
}
local_nodes = list(local_graph)
external_imports = collections.Counter(
    mod for imps in all_imports.values()
    for mod in imps if mod not in lean_files
)
missing_nonmathlib = sorted(
    (name, count) for name, count in external_imports.items()
    if not (name == "Mathlib" or name.startswith("Mathlib.")
            or name.startswith("Lean") or name.startswith("Batteries")
            or name.startswith("Aesop") or name.startswith("Qq")
            or name.startswith("Init"))
)
# Tarjan strongly connected components for circular local-import detection.
index = 0
stack = []
on_stack = set()
indices = {}
low = {}
cycles = []
def visit(node):
    global index
    indices[node] = index
    low[node] = index
    index += 1
    stack.append(node)
    on_stack.add(node)
    for target in local_graph[node]:
        if target not in indices:
            visit(target)
            low[node] = min(low[node], low[target])
        elif target in on_stack:
            low[node] = min(low[node], indices[target])
    if low[node] == indices[node]:
        component = []
        while True:
            n = stack.pop()
            on_stack.remove(n)
            component.append(n)
            if n == node:
                break
        if len(component) > 1 or node in local_graph[node]:
            cycles.append(component)
for node in local_nodes:
    if node not in indices:
        visit(node)
fan_in = collections.Counter(q for deps in local_graph.values() for q in deps)
heavy_roots = [{"path": p, "imported_by": n} for p,n in fan_in.most_common(25)]
report = {
    "generated_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "commit": subprocess.check_output(["git", "-C", str(ROOT), "rev-parse", "HEAD"]).decode().strip(),
    "total_tracked_files": len(paths),
    "total_bytes_read": total_bytes,
    "read_failures": errors,
    "lean_files": len(local_nodes),
    "text_files": sum(not f["binary"] for f in items),
    "binary_files": sum(f["binary"] for f in items),
    "declarations_by_kind": dict(all_decls),
    "local_import_edges": sum(len(x) for x in local_graph.values()),
    "import_cycles": cycles,
    "suspect_nonmathlib_external_imports": missing_nonmathlib,
    "most_imported_local_modules": heavy_roots,
    "executable_proof_marker_files": markers,
    "executable_axiom_declarations": [
        {"path": item["path"], "declarations": item["axiom_declarations"]}
        for item in items if item.get("axiom_declarations")
    ],
    "all_files": items,
}
(OUT / "census.json").write_text(json.dumps(report, indent=2), encoding="utf-8")
summary = [
    "# GST full repository source census",
    "",
    f"Commit: `{report['commit']}`",
    f"Tracked files read: **{len(paths)}**; total bytes: **{total_bytes}**.",
    f"Lean modules: **{len(local_nodes)}**; text files: **{report['text_files']}**.",
    f"Local Lean import edges: **{report['local_import_edges']}**.",
    f"Local import cycles: **{len(cycles)}**.",
    f"Files with executable 'sorry/admit/sorryAx/native_decide/unsafe' markers: **{len(markers)}**.",
    f"Read failures: **{len(errors)}**.",
    "",
    "## Executable axiom declarations",
    *[f"- {entry['path']}: " + ', '.join(x['name'] for x in entry['declarations'])
      for entry in report["executable_axiom_declarations"]],
    "",
    "## Important scope",
    "All tracked files are byte-read and all UTF-8 text files parsed for source-level metadata. "
    "The scanner does **not** elaborate every theorem, or determine if a token is semantically active inside "
    "a comment, or establish Hodge cycle-class surjectivity. Only exact Lean kernel "
    "builds establish the module-level formal validity of theorem statements.",
    "",
    "## Most imported local Lean modules",
]
summary += [f"- `{x['path']}`: {x['imported_by']} dependents" for x in heavy_roots]
summary += ["", "## Executable proof markers (comments and strings masked)"]
summary += [f"- `{x['path']}`: " +
            ", ".join(f"{z['token']}@{z['line']}" for z in x["occurrences"][:15])
            for x in markers[:90]]
summary += ["", "## Non-Mathlib imports worth checking", ""]
summary += [f"- {name}: {n} occurrence(s)" for name,n in missing_nonmathlib[:40]]
(OUT / "summary.md").write_text("\n".join(summary) + "\n", encoding="utf-8")
print(json.dumps({k:report[k] for k in [
    "commit", "total_tracked_files", "total_bytes_read", "lean_files",
    "text_files", "binary_files", "declarations_by_kind", "local_import_edges",
    "import_cycles", "suspect_nonmathlib_external_imports",
]}, indent=2))
print("Executable proof-marker files:", len(markers))
print("Executable axiom declarations:", json.dumps(report["executable_axiom_declarations"]))
print("Wrote gst_universe_census/census.json and summary.md")
