# GLM LIVE HANDOFF — Hodge two-burst execution

Target branch: `sol/hodge-single-separator-successor`

## Current mathematical route

Do NOT revive the old projective-detector-visibility route as an unconditional theorem. The branch now proves that ordinary cycle-natural projective correspondence outputs remain algebraic and are therefore annihilated by an omniversal separator ghost. `ProjectiveOrbitIrreducibility` is retained only as a conditional/audit certificate and is Hodge-strength.

The active noncircular route is now:

1. `GenuineCycleClassGeometry` excludes the Stage-2G zero-cycle-class countermodel using positive projective-degree trace semantics.
2. A hypothetical Hodge failure gives an `OmniversalSeparatorGhost`.
3. `GSTClassicalHodgeCohomologicalPairingFrontier` transforms its detector through a perfect rational cohomological pairing into a concrete nonzero `PairingOrthogonalGhost`:
   - nonzero dual cohomology class;
   - orthogonal to the complete atomic/algebraic cycle-class span;
   - still pairs nontrivially with the ghost Hodge direction.
4. Future extinction must use additional independently geometric/GST structure on that pairing-dual class. Do NOT assert `orthogonal complement = 0`, arbitrary basis-cycle representatives, `source_action`, `acts_as_GST`, exact cosmic matrix-unit realization, or universal detector visibility as a free hypothesis.

## Files that must remain intact

- `GSTClassicalHodgeStage2GSemanticRigidity.lean`
- `GSTClassicalHodgeSpineSemanticSeparation.lean`
- `GSTClassicalHodgeGenuineCycleClassGeometry.lean`
- `GSTClassicalHodgeProjectiveTomographyReadout.lean`
- `GSTClassicalHodgeProjectiveVisibilitySeparation.lean`
- `GSTClassicalHodgeProjectiveOrbitIrreducibilityAudit.lean`
- `GSTClassicalHodgeCohomologicalPairingFrontier.lean`
- `GSTClassicalHodgeTwoBurstClosureReceipt.lean`

## GLM lane

Repair parser/elaboration/namespace/Mathlib/tactic/API failures only. Keep theorem statements and the noncircular mathematical route unless a theorem is formally inconsistent. If a proof body needs local API surgery, repair it surgically. Do not replace a difficult theorem with a stronger assumption or a Hodge-equivalent certificate.

The assistant lane is continuing mathematics and higher-level integration in parallel.

## CI target

The push containing this handoff is intended to trigger `.github/workflows/hodge-conjecture.yml` on this same branch. Prioritize failures in the newly imported two-burst/pairing-frontier files and preserve green older modules.
