# GLM LIVE HANDOFF — TWO-BURST FINAL FRONTIER

Target branch: `sol/hodge-single-separator-successor`
Stable assistant integration head before GLM repair: `f675c6414fb13492872574e189ebdcab1d0a5f0f`

## New/active files to compile and repair

- `GSTClassicalHodgeProjectiveVisibilityNoGo.lean`
- `GSTClassicalHodgeCohomologicalPairingFrontier.lean`
- `GSTClassicalHodgePolarizedHodgeGhost.lean`
- `GSTClassicalHodgePolarizedOrthogonalExtinctionAudit.lean`
- `GSTClassicalHodgeAtomicDefectTomographySynchronization.lean`
- `GSTClassicalHodgeTomographySynchronizationAudit.lean`
- `GSTClassicalHodgeMultiplicityForgettingKernel.lean`
- `GSTClassicalHodgeTwoBurstCorrectedFrontier.lean`
- `GSTClassicalHodgeTwoBurstClosureReceipt.lean`

## Stable mathematical result of the two bursts

1. `GenuineCycleClassGeometry` excludes the zero-cycle-class Stage-2G model via
   positive projective-degree semantics.
2. A Hodge failure yields a genuine nonzero atomic quotient defect and a
   nonzero finite GST Lefschetz-tomography moment on the same multiplicity
   sheet.
3. The omniversal separator descends to the atomic defect quotient and can be
   normalized so its value on that defect is exactly the selected GST moment.
4. Existence of this synchronized packet is exactly equivalent to failure of
   `BigradedBettiHodgeStatement`.
5. A perfect Hodge-fiber pairing converts the separator to a nonzero Hodge
   vector orthogonal to every algebraic Hodge vector. Universal algebraic
   pairing separation is audited as Hodge-equivalent, so do not add it as a
   free field.
6. Ordinary cycle-natural/projective operators cannot supply nonzero ghost
   visibility: their outputs remain algebraic and are annihilated by the
   separator.
7. The un-fibered GST base cannot resolve classical multiplicity: two distinct
   sheets above one weight have a nonzero difference in the kernel of
   `forgetMultiplicityToGST`.
8. `GSTClassicalHodgeTwoBurstCorrectedFrontier.corrected_two_burst_crown`
   packages the corrected frontier without claiming an unconditional Hodge
   proof.

## Repair rules

Repair Lean parser/elaboration/namespace/pinned-Mathlib/tactic issues only.
Likely API hotspots:

- `Submodule.liftQ` and quotient simplification in
  `GSTClassicalHodgeAtomicDefectTomographySynchronization`;
- function/linear-map coercions in the perfect-pairing files;
- `map_sub` / `Finsupp` simplification in
  `GSTClassicalHodgeMultiplicityForgettingKernel`.

Do not repair by inserting or strengthening any of the following:

- Hodge surjectivity;
- basis-cycle bridge;
- `ProjectiveOrbitIrreducibility` as automatic geometry;
- arbitrary point-transition kernels for GST matrix units;
- `acts_as_GST`, `source_action`, or `RealizesCosmicOnPoints` fields;
- zero orthogonal complement of algebraic Hodge classes;
- vanishing of the atomic defect quotient.

Those are either formally blocked by the new no-go files or audited as
Hodge-strength.

The assistant lane is now holding source writes stable and will reconcile only
actual CI/compiler feedback against this mathematical route.
