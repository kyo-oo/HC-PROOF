#!/usr/bin/env python3
"""Static integrity audit of the task modules (tasks 1-7) at HEAD 8dcb746.
Checks: file existence, zero sorry/admit/native_decide, declaration counts."""
import re, os, glob

REPO = "/home/z/hc-repo"
TASKS = {
    "TASK 1 (honest prime lattice — point algebra)": ["GSTFiniteLinePointAlgebra.lean"],
    "TASK 2 (chart classification — analytification bridge)": ["GSTFiniteLineRiemann.lean", "GSTFiniteLineAnalytification.lean"],
    "TASK 3+4 (canonical cycle-class maps + two M-cycle letters)": [
        "GSTFiniteLineCycleCorrespondenceBasic.lean", "GSTFiniteLineCycleCorrespondenceAction.lean",
        "GSTFiniteLineCycleCorrespondenceOperators.lean", "GSTFiniteLineCycleCorrespondence.lean"],
    "TASK 5 (honest Hodge data)": ["GSTFiniteLineHonestHodgeData.lean"],
    "TASK 6 (THE UNCONDITIONAL LAW)": ["GSTFiniteLinePointsGateCoreBasic.lean", "GSTFiniteLinePointsGateCoreTransport.lean",
        "GSTFiniteLinePointsGateCore.lean", "GSTFiniteLinePointsGateDischargeBridges.lean",
        "GSTFiniteLinePointsGateDischargeInverseA.lean", "GSTFiniteLinePointsGateDischargeInverseB.lean",
        "GSTFiniteLinePointsGateDischarge.lean", "GSTFiniteLineUnconditionalSource.lean"],
    "TASK 7 (universal primitive-X source)": ["GSTFiniteLinePrimitiveXSourceFamilies.lean", "GSTFiniteLinePrimitiveXSource.lean"],
}

BANNED = re.compile(r"\b(sorry|admit|native_decide)\b")

total_all = 0
for task, files in TASKS.items():
    print(f"\n=== {task} ===")
    for f in files:
        path = os.path.join(REPO, f)
        if not os.path.exists(path):
            path = os.path.join(REPO, "GSTFiniteLineLanePieces", f)
        if not os.path.exists(path):
            # search
            hits = glob.glob(os.path.join(REPO, "**", f), recursive=True)
            path = hits[0] if hits else None
        if path is None or not os.path.exists(path):
            print(f"  MISSING: {f}")
            continue
        txt = open(path, encoding="utf-8").read()
        lines = txt.splitlines()
        # strip comments and strings for banned check (rough but effective: Lean sorry appears in code or doc)
        code_lines = [l for l in lines if not l.strip().startswith("--")]
        body = "\n".join(code_lines)
        bad = []
        for m in BANNED.finditer(body):
            ln = body[:m.start()].count("\n") + 1
            ctx = code_lines[ln-1].strip()[:80] if ln-1 < len(code_lines) else ""
            bad.append((ln, m.group(0), ctx))
        n_thm = len(re.findall(r"^\s*(?:private\s+)?(?:noncomputable\s+)?(?:theorem|def|lemma|instance|abbrev)\b", txt, re.M))
        total_all += len(lines)
        status = "CLEAN" if not bad else f"BANNED TOKENS x{len(bad)}"
        print(f"  {os.path.basename(path):58s} {len(lines):5d} lines  {n_thm:3d} decls  {status}")
        for ln, tok, ctx in bad[:6]:
            print(f"      !! line ~{ln}: {tok} | {ctx}")
print(f"\nTOTAL lines across audited modules: {total_all}")
