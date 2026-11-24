#!/usr/bin/env python3
"""Check live CI status of HC-PROOF lanes for tasks 3,4,6,7."""
import json, subprocess, sys

TOKEN = open("/home/z/bag/downloaded/extracted/erdos-zipbag/secrets/ghtoken.txt").read().strip()
REPO = "kyo-oo/HC-PROOF"
BRANCH = "research/gpt6-gst-hypothesis-part1-chow-square-20261110"

def api(url):
    out = subprocess.run(
        ["curl", "-sL", "-H", f"Authorization: Bearer {TOKEN}",
         "-H", "Accept: application/vnd.github+json", url],
        capture_output=True, text=True, timeout=60)
    return json.loads(out.stdout)

runs = api(f"https://api.github.com/repos/{REPO}/actions/runs?branch={BRANCH}&per_page=40")
runs = runs.get("workflow_runs", [])
print(f"total runs fetched: {len(runs)}")
lanes = {}
for r in runs:
    name = r["name"]
    if name not in lanes:
        lanes[name] = []
    lanes[name].append(r)

for name, rs in sorted(lanes.items()):
    r = rs[0]  # newest
    print(f"\n=== {name} (newest of {len(rs)}) ===")
    print(f"  run_id: {r['id']}  status: {r['status']}  conclusion: {r['conclusion']}")
    print(f"  head_sha: {r['head_sha'][:7]}  created: {r['created_at']}  attempt: {r['run_attempt']}")
    # show last 3 attempts summary
    for rr in rs[:3]:
        print(f"    - {rr['id']} sha {rr['head_sha'][:7]} {rr['status']}/{rr['conclusion']} attempt {rr['run_attempt']} @ {rr['created_at']}")
