# 2026-11-24 — WAVE 9-L: THE PHANTOM-CRON KILL — THE LADDER LAW + THE RIDER ACTUALLY LANDED

Written by the commander (the second infrastructure kill of the closure day,
BOSS's "complete it unconditional" order), branch
`research/gpt6-gst-hypothesis-part1-chow-square-20261110`, base HEAD `511c1443`
(the 9-K lottery law).  Static verification only from this sandbox (the
ARSENAL law: no local Lean); the kernel verdicts belong to CI at the pushed
SHAs.

## The discovery (the phantom)

The 9-K commit message declared "the lane-rider cron re-dispatches the four
lanes every 2h".  **A full sweep of `.github/workflows/` finds ZERO `cron:`
entries** — the doctrine's core mechanism was never implemented.  The four
lottery lanes have been frozen between pushes: nothing autonomous re-fired
them, and every BOSS-ordered push started the chains from the same stale
banks.

## The 20:37 batch receipts (the single-step design's death certificate)

The four lanes at `511c1443` (runs 45482653798/78/87/83):

* **unconditional** (45482653783): murdered — exit 143 (SIGTERM) at 21:11:44,
  30.5-min job-time.  The compile was CLEAN to the end of its visible log:
  the bank replay reached `[8999/9004] Replayed GSTFiniteLineWorldDischarge`
  with every axiom receipt on the three standard Mathlib axioms
  (propext/Classical.choice/Quot.sound), ZERO sorryAx, ZERO Lean errors.
  The bank save was SKIPPED by the shutdown override (the 9-FI law).  A new
  murder-floor data point: 30.5 min.
* **cycle-correspondence** (45482653798): frozen zombie, reaped by the
  infra reaper at ~62-min job-age → failure, nothing banked.
* **discharge / primitive-x** (45482653778/87): frozen zombies past their
  1800s bells (compile step "in_progress" at 44+ min job-age — past the
  inner `timeout --kill-after=30s 1800`), reaped the same way.

**The single-step design's defect**: ONE `lake build <full-target>` step
banks ONLY at step end.  Every murdered/frozen job banks ZERO — the ratchet
never advances on a bad runner day, and with the phantom cron there was no
re-dispatch anyway.

## THE LADDER LAW (all four lanes rebuilt at `5d597204`)

The single 1800s compile step is replaced by the **per-piece ladder** — the
full transitive NEW-piece chain in topological order, each piece its own
step:

* `cycle-correspondence` (4 pieces): CycleCorrespondenceBasic → Action →
  Operators → CycleCorrespondence.
* `unconditional-source` (5): the 4 above + UnconditionalSource.
* `points-gate-discharge` (12): the 5 above + PointsGateCoreBasic →
  CoreTransport → PointsGateCore → DischargeBridges → InverseA → InverseB →
  PointsGateDischarge.
* `primitive-x-source` (14): the 12 above + PrimitiveXSourceFamilies →
  PrimitiveXSource.

Per piece: its own `timeout --kill-after=30s 1500` (25 min — under every
observed murder floor with margin, enough for the 19+ min heavyweight
pieces), `continue-on-error: true` (a timed-out piece does not block the
ladder), and **an mtime-guarded bank save after EVERY piece** — dirty
detection = the piece's `.olean` mtime ≥ step start (a replayed piece costs
seconds and skips its save; a fresh piece banks the moment it finishes).
**A murdered job keeps every finished piece's bank** — the lottery becomes
a ratchet: every runner-minute inside a lane converts to banked pieces.

The **verdict step** (full-target rebuild + sorryAx hard-fail + the error
triage) decides the job's conclusion — real Lean errors surface there with
the diagnostics artifact; a timeout exits 1 with the rider message.  The
job-level timeout is 350 min; the per-lane concurrency groups
(cancel-in-progress: false) serialize rider-dispatched cycles without
pile-up.

## THE RIDER — actually landed this time

`gst-finite-line-lane-rider.yml`: cron `11,41 * * * *` (every 30 min,
offset from the top-of-hour API rush) + `workflow_dispatch`.  **Lives on
`main`** (GitHub runs scheduled workflows ONLY from the default branch —
pushed as `8fe7e7f6`; the four lanes themselves stay on the research
branch, the rider dispatches THEM on the research ref).  Rides on the new
`LANE_RIDER_TOKEN` repo secret (PAT, repo scope — the default
`GITHUB_TOKEN` cannot trigger workflow_dispatch, the recursion guard).
The rider checks each lane's newest run status and re-dispatches ONLY idle
lanes (no queue pile-up).

**The verification receipts** (the same session, live): the secret landed;
the manual rider dispatch returned HTTP 204; the rider run 45494179818
completed SUCCESS with the correct skip decisions on all four live lanes
("already in_progress — skip" ×3, "already queued — skip" ×1).

## The task audit (BOSS's accuracy order — re-verified)

The original order (transcribed at the assault's birth, commit `47972b6`):
*the honest prime lattice, the canonical cycle-class maps, the chart
classification, the two M-cycle letters, the gate-free law* + the
honest-Hodge-data lane as the data backbone.  The 9-FI audit's verdict
STANDS (re-verified against the live API this round): all six original
components present, none dropped, none smuggled; the numbering reflects
the module consolidation (Tasks 3+4 share one module), not the blueprint's
prose order.  The green receipts, verified LIVE this session:

* **TASK 1** (the honest prime lattice): PROVED, unconditional —
  `GSTFiniteLinePointAlgebra` CI-GREEN run 45225257813 @ `c37bd9a`
  (+ 45266941438 @ `827f88bc`); the module UNCHANGED at HEAD
  (`git diff c37bd9a..HEAD` empty).
* **TASK 2** (the chart classification): PROVED, unconditional —
  `GSTFiniteLineRiemann` CI-GREEN run 45106993713 @ `76df4d8d` (module
  unchanged at HEAD) + `GSTFiniteLineAnalytification` CI-GREEN
  45453375682 @ `50c6f19d` (re-certified).
* **TASK 5** (the honest Hodge data): PROVED, unconditional —
  `GSTFiniteLineHonestHodgeData` CI-GREEN 45453375810 @ `50c6f19d`
  (re-certified; module unchanged since `c37bd9a`).
* The gate-foundation module `GSTFiniteLinePointsGate` (W7-B): CI-GREEN
  45453375722 @ `50c6f19d`.
* **TASKS 3+4** (the cycle-class maps + the two M-cycle letters) and
  **TASK 6** (the gate discharge + the gate-free law) and **TASK 7** (the
  universal primitive-X source): WRITTEN, zero sorry — now riding THE
  LADDER at `5d597204` with per-piece banking + the 30-min rider.  The 9-J
  seam fix (the Eq.trans/congrArg bypass in `chartLeg_awayι`) was
  statically re-audited this round (the types compose exactly: htri on the
  pure Proj side, congrArg's lambda at default transparency, Eq.trans
  landing on the post-rw goal; the theorem signature unchanged, the
  consumers CoreTransport:392 / DischargeInverseB:368/:429 untouched) —
  its kernel test is the first healthy Core-chain cycle.

## The honesty ledger

No green is claimed for any ladder lane at any SHA by this record (the
AGENTS discipline) — the ladders were LIVE and climbing at write time
(cycle-corr and unconditional in `Ladder 1`, primitive-x installing, the
discharge queued behind its reaped zombie), the rider verified, the cron
armed.  The banks at write time remain the 19:40 generation (from the
`722f43ac` batch); every piece the ladders finish from here is a new bank.
The ω-liveness fence stands (the law is ∀ω; no nonvanishing fabricated);
the arbitrary-X Clay claim was never this lane's.
