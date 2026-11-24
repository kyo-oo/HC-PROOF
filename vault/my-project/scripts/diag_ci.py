#!/usr/bin/env python3
"""Diagnose the 9-H cycle-2 failures: bank landed? pieces completed? real errors?"""
import json, subprocess, sys

TOKEN = open("/home/z/bag/downloaded/extracted/erdos-zipbag/secrets/ghtoken.txt").read().strip()
REPO = "kyo-oo/HC-PROOF"

def api(url):
    out = subprocess.run(
        ["curl", "-sL", "-H", f"Authorization: Bearer {TOKEN}",
         "-H", "Accept: application/vnd.github+json", url],
        capture_output=True, text=True, timeout=120)
    return json.loads(out.stdout)

RUNS = {
    "cycle-corr (TASKS 3+4)": 45456987892,
    "discharge (TASK 6)": 45456987872,
    "primitive-x (TASK 7)": 45456988043,
}

for label, run_id in RUNS.items():
    print(f"\n######## {label} — run {run_id} ########")
    jobs = api(f"https://api.github.com/repos/{REPO}/actions/runs/{run_id}/jobs?per_page=10")
    for j in jobs.get("jobs", []):
        print(f"  JOB: {j['name']}  status={j['status']} concl={j['conclusion']} started={j['started_at']} ended={j.get('completed_at')}")
        steps = j.get("steps", [])
        for s in steps:
            print(f"    step: {s['name']:45s} {s['status']}/{s['conclusion']}")
