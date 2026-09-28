# GLM LIVE HANDOFF — Hodge Burst 2 semantic closure

Target branch: `sol/hodge-single-separator-successor`
Integrated Burst-2 head at handoff: `16f55d3686861bf50c25f5dce34c7b97b6af87b7`
Current Hodge CI run: `36488660515`

Burst 1 handoff remains authoritative for the foundation files. This note adds the Burst-2 consumer surface.

## Burst-2 files

### `GSTClassicalHodgeTomographyVisibilityCrown.lean`
Expected public declarations:

- `omniversalGhost_has_projective_visibility`
- `omniversalGhost_has_tomography_moment_hit`
- `omniversalGhost_false`
- `omniversalGhost_false_of_visibility`
- `no_omniversalSeparatorGhost`
- `tomography_visibility_crown`

Mathematical route is fixed:

`GenuineCycleClassGeometry`
→ Burst-1 `exists_projectiveDetectorVisible`
→ existing `ProjectiveDetectorVisible.toMomentHit`
→ existing `no_projectiveDetectorMomentHit`
→ no omniversal ghost.

### `GSTClassicalHodgeGenuineSemanticClosure.lean`
Expected public declarations:

- `not_hodge_impossible`
- `bigradedBettiHodge_of_genuineCycleClassGeometry`
- `counterexample_yields_projective_tomography_contradiction`
- `genuine_semantic_closure_crown`

The public closure is intentionally conditional on:

- `GenuineCycleClassGeometry V H`
- `NativeMassCycleClassBridge V H`

Do not weaken that distinction by rewriting this as an unconditional theorem over arbitrary `HodgeBigradedBettiData`.

### `GSTClassicalHodgeTwoBurstClosureReceipt.lean`
Now imports and checks both Burst 1 and Burst 2. The Hodge workflow explicitly compiles this receipt.

## Repair instructions

Repair only elaboration/import/tactic/API issues while preserving theorem statements when possible. Expected hotspots:

- namespace resolution for `NativeMassCycleClassBridge`;
- namespace resolution for `ProjectiveDetectorVisible` / `ProjectiveDetectorMomentHit`;
- `IsEmpty` constructor syntax and `.false` projection;
- implicit parameters of `not_hodge_iff_nonempty_omniversalSeparatorGhost` and `hodge_iff_no_omniversalSeparatorGhost`;
- fully qualified moment-hit type in `counterexample_yields_projective_tomography_contradiction`;
- any structure projection names from the new `GenuineCycleClassGeometry` extension.

Do **not** replace `ProjectiveOrbitIrreducibility` with basis-cycle surjectivity, exact matrix units, `source_action`, `acts_as_GST`, `RealizesCosmicOnPoints`, or another Hodge-equivalent hypothesis.

No `sorry` / `sorryAx`. Keep all semantic-rigidity and zero-map audits.
