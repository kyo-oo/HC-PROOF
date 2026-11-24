#!/usr/bin/env python3
"""Fetch axiom receipts from green CI runs for tasks 1/2/5."""
import json, subprocess, sys, re

TOKEN = open("/home/z/bag/downloaded/extracted/erdos-zipbag/secrets/ghtoken.txt").read().strip()
REPO = "kyo-oo/HC-PROOF"

def api(url):
    out = subprocess.run(
        ["curl", "-sL", "-H", f"Authorization: Bearer {TOKEN}",
         "-H", "Accept: application/vnd.github+json", url],
        capture_output=True, text=True, timeout=120)
    return json.loads(out.stdout)

GREEN = {
    "TASK 1 — Point Algebra": 45453375773,
    "TASK 2 — Analytification (incl. Riemann)": 45453375682,
    "TASK 5 — Honest Hodge Data": 45453375810,
}

for label, run_id in GREEN.items():
    jobs = api(f"https://api.github.com/repos/{REPO}/actions/runs/{run_id}/jobs?per_page=5")
    for j in jobs.get("jobs", []):
        jid = j["id"]
        log = subprocess.run(
            ["curl", "-sL", "-H", f"Authorization: Bearer {TOKEN}",
             f"https://api.github.com/repos/{REPO}/actions/jobs/{jid}/logs"],
            capture_output=True, text=True, timeout=180).stdout
        receipts = re.findall(r"'[^']*' (?:does not (?:depend on|use)|depends only on)[^\n]*axioms[^\n]*", log)
        receipts += re.findall(r"\[propext, [^\]]*\]", log)
        sorry_hits = re.findall(r"declaration uses 'sorry'", log)
        err_hits = len(re.findall(r"^.*error:.*$", log, re.M))
        print(f"\n=== {label} — job {jid} concl={j['conclusion']} ===")
        print(f"  sorry-declarations: {len(sorry_hits)}   error lines: {err_hits}")
        seen = set()
        for r in receipts[:25]:
            r = r.strip()
            if r not in seen:
                seen.add(r)
                print(f"  AXIOM RECEIPT: {r[:160]}")
