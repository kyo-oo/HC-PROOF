# GLM LIVE HANDOFF — Hodge cycle-class / tomography two-burst repair

Target branch: `sol/hodge-single-separator-successor`
Burst-1 receipt head at handoff: `680b0c8c7c220cab529a20496de656e01984b896`

## Division of labor

GLM lane: Lean parser/elaborator/API/namespace/tactic repair only.
Assistant lane: mathematics, theorem statements, architecture, source writing, integration.

Do **not** reroute the mathematics, replace the new geometry with a Hodge-equivalent basis-cycle assumption, delete semantic-rigidity audits, or reintroduce exact matrix-unit / `source_action` / `acts_as_GST` assumptions.

## Burst-1 source to compile/repair

1. `GSTClassicalHodgeGenuineCycleClassGeometry.lean`
   - `ProjectiveOrbitIrreducibility`
   - `GenuineCycleClassGeometry`
   - `GenuineCycleClassGeometry.point_cycleClass_ne_zero`
   - `GenuineCycleClassGeometry.not_nonempty_zeroCycleClassData`
   - `GenuineCycleClassGeometry.cycleClass_ne_zero`

2. `GSTClassicalHodgeProjectiveTomographyReadout.lean`
   - `projectiveDetectorReadout`
   - `projectiveDetectorReadout_scale`
   - `exists_nonzero_projectiveDetectorReadout`
   - `normalizeProjectiveReadout_spec`
   - `exists_projectiveDetectorReadout_eq`

3. `GSTClassicalHodgeProjectiveVisibilitySeparation.lean`
   - `ghostSpine_cycleClass_ne_zero`
   - `ghost_detector_hodge_visible`
   - `exists_projectiveDetectorVisible`
   - `exists_projectiveDetectorMomentHit`
   - `exists_projectiveKernel_readout_eq_ghostMoment`

4. `GSTClassicalHodgeTwoBurstClosureReceipt.lean`
   - compiler receipt only; keep theorem names synchronized with repaired source.

## Intended mathematics — preserve this route

The current Stage-2G zero-map countermodel survives the old geometric spine, so Burst 1 strengthens semantics in two genuinely different directions:

- positive projective-degree trace excludes the zero cycle-class map;
- `ProjectiveOrbitIrreducibility` is the new broad limitless geometry law: every nonzero algebraic source has a projective orbit detected by every rational detector which sees some Hodge state.

This law is deliberately broader than a basis-cycle bridge and stores no exact target vector or matrix-unit action.

The specialization is:

`nonzero ghost spine cycle class`
→ `ghost detector sees its Hodge basis sheet`
→ projective orbit irreducibility gives one nonzero projective readout
→ `ProjectiveDetectorVisible`
→ existing rational rescaling
→ exact nonzero GST tomography moment hit.

## Likely Lean repair hotspots

- structure-extension projection elaboration for `toGeometricCycleClassSpine` and `toProjectiveDegreeTraceSemantics`;
- namespace visibility for `ProjectiveNativeKernel`, `projectiveCorrespondencePair`, `NativeMassCycleClassBridge`, and `ghostSpineSeed`;
- rewriting `NativeHodgeOrbitSeed.class_eq` under locally defined `S`;
- `Subtype.ext` when converting `S.hodge.1 = 0` to `S.hodge = 0`;
- scalar simplification after `map_smul` in `projectiveDetectorReadout_scale`;
- `field_simp` in `normalizeProjectiveReadout_spec`;
- fully qualified tomography names in the final scalar receipt.

Repair these surgically. If a theorem statement has an actual type mismatch that cannot be repaired without changing mathematics, leave a precise note/commit message rather than replacing the theorem with a stronger assumption.

## Noncircularity constraints

Keep all of these intact:

- `GSTClassicalHodgeStage2GSemanticRigidity`
- `GSTClassicalHodgeSpineSemanticSeparation`
- zero-map exclusion must come from projective degree, not Hodge;
- no `sorry`, `sorryAx`, custom Hodge-surjectivity axiom, basis-cycle bridge, `ProjectiveLiveSourceTarget.source_action`, `RealizesCosmicOnPoints`, or exact GST matrix-unit externalization.

Assistant is continuing Burst 2 in parallel against these intended signatures.
