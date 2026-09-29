# GLM live handoff delta — one-ghost polarized / transpose frontier

Target branch: `sol/hodge-single-separator-successor`

This delta continues `docs/GLM_LIVE_HANDOFF_HODGE_FIRST_PRIMITIVE_SECTOR.md`.
Repair/register these files **without strengthening their mathematical
hypotheses**.

## New files after the first primitive-sector handoff

1. `GSTClassicalHodgeFirstGhostCorrespondenceCollision.lean`
   - commit `9e3077c146935e1283c9b4b9cdd0c4c43b5a060c`
   - already registered by GLM repair batch `c3e723fe97d607ab669138d02af88db70ebf0679`.
   - concrete carrier: one actual `FiniteClosedCorrespondence` from `p+1` to
     `p`.
   - only requires Hodge preservation on one ghost and one scaled principal-cut
     roundtrip modulo atomic classes.

2. `GSTClassicalHodgeFirstGhostCorrespondenceFrontier.lean`
   - commit `c11bb5504a43bd3fd37de857b769acd3cdb6ca30`
   - globalizes the previous collision to the least positive defect weight.
   - supplies `bigradedBettiHodge_of_firstGhostCorrespondenceReturns`.

3. `GSTClassicalHodgeFirstGhostPolarizedCorrespondenceCriterion.lean`
   - commit `5ed729f9c4a4d9db0a9fad3967f507320cddd359`
   - replaces direct atomic-span membership of the one-ghost roundtrip error by
     the perfect-pairing criterion

       `P(u, error_E) = 0`

     for every Hodge vector `u` orthogonal to all algebraic Hodge vectors.
   - derives the concrete correspondence-return packet using the existing
     double-orthogonal theorem.

4. `GSTClassicalHodgeFirstGhostAdjointScaledCriterion.lean`
   - commit `776d8c7627afd590513ba0041d55177d64d325e1`
   - splits that one-error pairing equation into two pointwise laws only:
     one-ghost adjointness + one-ghost scaled pairing.
   - does **not** request global adjointness or a whole-fiber Lefschetz inverse.

5. `GSTClassicalHodgeFiniteClosedCorrespondenceTranspose.lean`
   - commit `2a94c7be71237348a4044bdf1461737df6ec8b71`
   - constructs the actual swap automorphism of `X ×_C X`.
   - introduces `BiFiniteClosedCorrespondence`: an existing finite-left-fiber
     correspondence plus finite right fibers.
   - constructs the genuine transpose correspondence and proves exact left/right
     projection reversal.
   - do **not** erase the right-finiteness condition: arbitrary
     `FiniteClosedCorrespondence` does not have a finite transpose.

6. `GSTClassicalHodgeFirstGhostTransposeAdjointGeometry.lean`
   - commit `b114fa1de7db6290b88722acd3dc35f0c9711757`
   - uses one bi-finite `K` and its genuine transpose `Kᵗ`.
   - pointwise naturality is supplied for both directions.
   - transpose/principal-cut agreement is required only on the fixed ghost-down
     state.
   - projection formula is required only against algebraic-orthogonal test
     vectors and the fixed ghost-down state.
   - derives the previous one-ghost adjoint law.
   - adding only the remaining one-ghost nonzero scaled-pairing law yields the
     full contradiction at first failure.

## Current mathematical frontier

For a hypothetical least first defect at `p+1`, all lower realized Hodge-defect
sectors vanish and the complete first defect sector is primitive.  A canonical
trace-zero primitive ghost `E` survives.

The remaining target has now been factored into actual geometry:

1. construct a **bi-finite** closed correspondence `K` from `p+1` to `p`;
2. give point-generator cycle-class naturality for `K` and its actual transpose
   `Kᵗ`;
3. on the single state `E`, identify the transpose return with the existing
   principal-cut return;
4. prove the projection-formula identity only against algebraic-orthogonal
   tests;
5. prove a nonzero scalar pairing law only against that same ghost.

Steps 1–4 manufacture one-ghost adjointness.  Step 5 is now the sharpest
remaining scalar law.

## Firewall

Do not repair by adding any of:

- full Hodge or target-basis algebraicity;
- projective irreducibility;
- arbitrary cosmic matrix-unit realization;
- bare same-weight `L²` naturality;
- global Hard-Lefschetz inverse as an algebraic correspondence;
- global projection formula if a one-ghost formula typechecks;
- global scaled pairing law if the one-ghost law typechecks;
- right-fiber finiteness for all finite correspondences by fiat.

The internal GST files `GSTLefschetzCrown`, `GSTPureHodgeLefschetzKernel`, and
`GSTUniversalLefschetzCausalGeometry` prove strong **internal** Lefschetz laws,
but they do not themselves externalize a classical algebraic inverse.  Do not
bridge that semantic gap by rewriting a theorem statement.

## Likely Lean-sensitive points

- pullback swap equality / `pullback.hom_ext`;
- `IsIso` and `IsClosedImmersion` inference for composition with the swap iso;
- coercions between `BiFiniteClosedCorrespondence` and
  `FiniteClosedCorrespondence`;
- inherited structure-field projections in the transpose file;
- `map_sub`, `map_smul`, and subtype coercions in the polarized error theorem;
- implicit parameters on `principalCutHodgeMap`;
- the exact namespace of `hodge_mem_atomicSpan_iff_pair_orthogonalComplement_zero`.

Repair surgically.  No `sorry`, custom axiom, or stronger semantic assumption.
