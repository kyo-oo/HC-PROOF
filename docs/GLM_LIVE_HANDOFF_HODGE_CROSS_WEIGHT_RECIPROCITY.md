# GLM LIVE HANDOFF — HODGE CROSS-WEIGHT RECIPROCITY

Branch: `sol/hodge-single-separator-successor`

## New mathematics from Sol

### 1. Cross-weight defect descent

Existing commit:

`572eeec867b6f145d91a511843fb2371a6d64ba6`

File:

`GSTClassicalHodgeCrossWeightAtomicDefectDescent.lean`

Core result: every genuine `GradedCycleClassOperatorPair V H p q` descends
canonically to

`AtomicDefectSpace V H p -> AtomicDefectSpace V H q`.

The projective principal-cut pair therefore gives the unconditional defect
ladder `D_p -> D_(p+1)`.

### 2. Generic nonzero-scaled return law

Commit:

`cdb6c24f8b36c04d00bf49b282cf83127255dd88`

File:

`GSTClassicalHodgeCrossWeightDefectRetraction.lean`

Core theorem:

if genuine graded pairs `forward : p -> q` and `backward : q -> p` satisfy

`backward.cohomologyOperator (forward.cohomologyOperator alpha) = scalar • alpha`

for nonzero `scalar`, then the descended forward defect operator is injective.

This is noncircular: no basis-cycle representative, Hodge surjectivity, or
same-weight matrix unit occurs.

### 3. Terminal crown — diagnostic only

Commit:

`c981f2737b0126193f08ff9fc5046f656643afe0`

File:

`GSTClassicalHodgeCrossWeightDefectTerminalCrown.lean`

This proves:

`one-step return family + eventual zero ambient cohomology -> full Hodge`.

**Important: do not treat the one-step return family as the intended geometry
frontier.**  It is stronger than the actual hard-Lefschetz shape and was
written as a generic diagnostic reduction.

### 4. Corrected complementary-power route

Commit:

`7bebd74b756066c73a24ec0f081f78e7b2e8b755`

File:

`GSTClassicalHodgeComplementaryDefectReciprocity.lean`

This is the live target.

It constructs:

- `gradedIdentityPair`
- `principalCutPairIterate G p n`
- exact identification of the iterate's defect action with
  `principalCutDefectIterate G p n`
- Hodge preservation of the entire iterate
- `PrincipalCutPowerReturnLaw G p n`
- injectivity of the n-step defect transport from one nonzero-scaled return
- backward propagation of atomic-defect/Hodge vanishing
- `complementaryExponent d p := d - 2*p`
- `ComplementaryPrincipalCutReturnLaw G d p`
- target arithmetic `p + (d - 2*p) = d-p` in the lower-half range.

## Mathematical firewall

Do NOT repair this route by introducing any of the following as hypotheses:

- basis cycles for arbitrary Hodge directions;
- bare same-weight `L^2` native realization;
- `ProjectiveOrbitIrreducibility`;
- projective visibility of a separator ghost;
- an operator that is already equivalent to target-sheet algebraicity.

Those interfaces have already been audited as Hodge-strength/circular.

## Current independent geometry frontier

The desired classical/native theorem is now sharply localized:

For each relevant lower-half weight `p`, construct a genuine native graded
return operator for the **whole complementary principal-cut power**

`p -> d-p`

whose cycle-class action satisfies a nonzero-scaled round trip on ambient
cohomology.

This is the correct hard-Lefschetz/Poincare-shaped externalization target.
It should be attacked using the repo's genuine principal-section geometry,
Poincare reciprocity, projective correspondences, and GST dual/recoordination
laws — but the final return must be an actual `GradedCycleClassOperatorPair`,
not merely an internal GST address involution.

## Separate analytic frontier

`HodgeBigradedBettiData` uses actual Mathlib singular cohomology of a supplied
`AnalytificationData`, but that structure does not itself encode finite
complex dimension or top-degree vanishing.

Therefore any terminal-cohomology argument must first prove, independently,
that the supplied analytification of the smooth projective scheme has the
expected finite-dimensional cohomological vanishing.  Do not insert this as a
silent field into Hodge data.

## GLM task

1. Register `GSTClassicalHodgeComplementaryDefectReciprocity` in the lake root
   set/workflow.
2. Repair syntax/elaboration only; preserve all theorem statements unless a
   statement is formally ill-typed.
3. Keep the mathematical distinction above: the complementary-power law is
   the live route; the one-step family is diagnostic.
4. Report exact compile failures and repairs without replacing the route with a
   Hodge-equivalent interface.
