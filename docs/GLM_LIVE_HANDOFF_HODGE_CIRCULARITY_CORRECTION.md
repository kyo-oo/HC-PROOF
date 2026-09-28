# GLM LIVE HANDOFF — circularity correction after Burst 2

Target branch: `sol/hodge-single-separator-successor`
Corrected receipt head: `7e77257db9f6eb2fd323df9c6d48d7ac461f1293`

IMPORTANT: This supersedes the old Burst-1/Burst-2 signatures where `ProjectiveOrbitIrreducibility` was embedded inside `GenuineCycleClassGeometry`.

## Mathematical correction

`GSTClassicalHodgeVisibilityEquivalenceAudit` proves that universal `ProjectiveDetectorVisible` for omniversal ghosts is equivalent to `BigradedBettiHodgeStatement` under the native-mass bridge.

Therefore `ProjectiveOrbitIrreducibility`, which specializes to universal detector visibility, must NOT be treated as an independently available field of genuine geometry.

The source has been corrected:

- `GenuineCycleClassGeometry` now extends ONLY
  - `GeometricCycleClassSpine`
  - `ProjectiveDegreeTraceSemantics`
- `ProjectiveOrbitIrreducibility V H J` is a separate explicit conditional closure certificate.
- every downstream theorem that consumes it now has an explicit `R : ProjectiveOrbitIrreducibility V H J` argument.
- `GSTClassicalHodgeProjectiveOrbitIrreducibilityAudit.lean` proves that `R` implies universal projective visibility and hence Hodge.

Do not repair the code by moving `R` back into `GenuineCycleClassGeometry` or by synthesizing it from Hodge/basis-cycle assumptions.

## Corrected files to repair

1. `GSTClassicalHodgeGenuineCycleClassGeometry.lean`
2. `GSTClassicalHodgeProjectiveTomographyReadout.lean`
3. `GSTClassicalHodgeProjectiveVisibilitySeparation.lean`
4. `GSTClassicalHodgeTomographyVisibilityCrown.lean`
5. `GSTClassicalHodgeGenuineSemanticClosure.lean`
6. `GSTClassicalHodgeProjectiveOrbitIrreducibilityAudit.lean`
7. `GSTClassicalHodgeTwoBurstClosureReceipt.lean`

## Intended theorem signatures

- `exists_nonzero_projectiveDetectorReadout J R ...`
- `exists_projectiveDetectorVisible J R M E`
- `omniversalGhost_false J R M E`
- `bigradedBettiHodge_of_projectiveOrbitIrreducibility J R M`
- `projectiveOrbitIrreducibility_implies_hodge J R M`

The independent geometry currently proven is the degree-rigid layer; the assistant is continuing mathematics below `R` to look for a genuinely independent construction or a sharper obstruction theorem.

Compiler/API/tactic fixes only. No `sorry`, no hidden basis bridge, no exact matrix-unit assumption, no rerouting through `source_action`.
