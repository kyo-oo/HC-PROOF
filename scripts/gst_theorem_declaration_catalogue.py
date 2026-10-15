#!/usr/bin/env python3
"""Build a searchable declaration and import catalogue of every GST/HC Lean source.

This reads EVERY Lean file at the checked-out revision, records genuine source
locations and declaration headings, and distinguishes a repository-wide
mechanical inventory from substantive proof review. It does NOT assert that
any theorem is mathematically valid or that transitive proof obligations
have been discharged. Run with the existing dependency-graph workflow.
"""
from __future__ import annotations
import collections
import json
import pathlib
import re

ROOT = pathlib.Path(__file__).resolve().parents[1]
DECL = re.compile(r"^\s*(?:private\s+|protected\s+|noncomputable\s+|unsafe\s+)*"
                  r"(theorem|lemma|def|structure|class|axiom|opaque|abbrev|instance)\s+"
                  r"([\w.']+)")
IMPORT = re.compile(r"^\s*import\s+([^\r\n]+)")
HEADING = re.compile(r"^\s*#\s+(.*)")
INCLUDED = ("GST", "Hodge", "Cardinal", "Comparator", "Main", "Information", "Origin")
MARKERS = ("sorry", "sorryAx", "admit", "native_decide")
DATA = {}
AGG = collections.Counter()

for f in sorted(ROOT.rglob("*.lean")):
    if any(x in {".lake", ".git", "build", ".elan", ".venv"} for x in f.parts):
        continue
    path = f.relative_to(ROOT).as_posix()
    text = f.read_text(encoding="utf-8")
    rows = text.splitlines()
    imports, decls = [], []
    for n,line in enumerate(rows,1):
        if mat := IMPORT.match(line):
            imports += mat.group(1).split()
        if mat := DECL.match(line):
            k,name = mat.groups()
            d = {"kind":k,"name":name,"line":n,
                 "header":line.strip()[:400]}
            decls.append(d)
            AGG[k]+=1
    mark={m:sum(1 for line in rows if re.search(r"\b"+re.escape(m)+r"\b",line))
          for m in MARKERS}
    DATA[path]={
       "lines":len(rows),"imports":imports,"declarations":decls,
       "marker_line_counts_unclassified":mark,
       "headline":next((HEADING.match(line).group(1) for line in rows[:65]
                        if HEADING.match(line)),""),
    }

report={"root":"HC-PROOF","files_read":len(DATA),
        "declaration_counts":dict(AGG),
        "marker_caution":"Markers include comments, do not assert proof dependency audit",
        "modules":DATA}
path=ROOT/"lean-declaration-catalogue.json"
path.write_text(json.dumps(report,indent=2)+"\n",encoding="utf-8")
print(f"CATALOGUE: {len(DATA)} Lean files, {sum(AGG.values())} declarations")
print("DECLARATION_COUNTS",json.dumps(dict(AGG),sort_keys=True))
print("CM_NM_FILE_COUNT",sum("CM" in p or "NumberManipulation" in p for p in DATA))
for path, info in DATA.items():
    for d in info["declarations"]:
        if d["kind"]=="axiom":
            print("AXIOM_DECLARATION",path,d["line"],d["name"])

