# GLM LIVE HANDOFF — HODGE CROSS-WEIGHT RECIPROCITY

Branch: `sol/hodge-single-separator-successor`

## Foundation already present

### Cross-weight defect descent

Commit `572eeec867b6f145d91a511843fb2371a6d64ba6`

`GSTClassicalHodgeCrossWeightAtomicDefectDescent.lean`

Every genuine `GradedCycleClassOperatorPair V H p q` descends to the atomic
defect quotient. The genuine principal-cut spine therefore gives an
unconditional defect ladder `D_p -> D_(p+1)`.

### Generic exact return — diagnostic

Commit `cdb6c24f8b36c04d00bf49b282cf83127255dd88`

`GSTClassicalHodgeCrossWeightDefectRetraction.lean`

A nonzero-scaled exact round trip makes the descended forward defect map
injective.

### One-step terminal crown — diagnostic only

Commit `c981f2737b0126193f08ff9fc5046f656643afe0`

`GSTClassicalHodgeCrossWeightDefectTerminalCrown.lean`

Do **not** chase a return for every one-step principal cut. That condition is
stronger than the correct hard-Lefschetz geometry.

## Correct complementary-power hierarchy

### Complementary power

Commit `7bebd74b756066c73a24ec0f081f78e7b2e8b755`

`GSTClassicalHodgeComplementaryDefectReciprocity.lean`

Builds the genuine n-fold principal-cut operator pair, proves its defect action
is the existing defect iterate, proves Hodge preservation, and isolates one
return for the whole complementary power `n = d - 2*p`.

### Preferred modulo-atomic return

Commit `6081815f4443d674f99e13113e5981800228aa83`

`GSTClassicalHodgeDefectModuloAtomicReciprocity.lean`

Preferred over exact inversion. It is enough that

`R (L^n alpha) - scalar • alpha ∈ AtomicSpanAt H p`

for Hodge inputs and `scalar != 0`.

### Genuine graded finite closed correspondence carrier

Commit `137cf68f6e85e90e1be2950290c104dbff906533`

`GSTClassicalHodgeGradedFiniteClosedCorrespondence.lean`

This unlocks arbitrary source/target codimensions for the existing genuine
finite closed correspondence geometry:

- `gradedTransition`
- `gradedNativePointImage`
- `gradedPresentationOperator`
- `gradedNativeCycleOperator : cycles_p -> cycles_q`
- point-generator formula
- `GradedCorrespondencePointNaturality`
- pointwise naturality -> full `GradedCycleClassOperatorPair` by compact point
  normal form.

This file is important: the complementary return no longer needs an abstract
native cycle operator.

### Annihilator reduction

Commit `330897dd331ee84eb9c3c579fa8258f1175d8db1`

`GSTClassicalHodgeDefectAnnihilatorReciprocity.lean`

Proves atomic membership iff every atomic annihilator kills the class, then
reduces the modulo-atomic return law to detector identities. Also specializes
the return carrier to an actual graded finite closed correspondence.

### Polarized double-orthogonal reduction

Commit `b8e4fc0026901408c04ddcefa486047f99c8769c`

`GSTClassicalHodgePolarizedDefectReciprocity.lean`

For a perfect Hodge-fiber pairing:

`alpha ∈ AtomicSpan`

iff

`pair u alpha = 0` for every Hodge vector `u` orthogonal to all algebraic Hodge
vectors.

Defines a Hodge-stable graded return and turns an orthogonal-pairing roundtrip
law into modulo-atomic reciprocity.

### Adjointness + scaled pairing

Commit `a4f99a284a7a4da62d1e3526738f196761ff5452`

`GSTClassicalHodgePolarizedAdjointReciprocity.lean`

Shows the orthogonal roundtrip law follows from two operator identities:

1. projection-formula adjointness
   `P(u, R beta) = Q(F u, beta)`;
2. scaled Lefschetz pairing
   `Q(F u, F alpha) = scalar * P(u, alpha)`.

These imply zero pairing with the roundtrip error for **every** Hodge vector,
therefore in particular the algebraic orthogonal complement.

### Concrete complementary transport crown

Commit `0dc13922a79d0a729d35a1419d89dd9ca18a0639`

`GSTClassicalHodgePolarizedGradedCorrespondenceCrown.lean`

Forward = genuine iterated principal cut.
Backward = actual graded finite closed correspondence.

Under:

- return Hodge preservation,
- pairing adjointness,
- nonzero-scaled Lefschetz pairing,
- forward Hodge surjectivity,

it proves

`atomicDefectLinearMap V H p = 0 ↔ atomicDefectLinearMap V H (p+n) = 0`.

This cleanly separates complementary transport from the remaining primitive
Hodge obstruction.

## Mathematical firewall

Do NOT repair any file by introducing:

- basis cycles for arbitrary Hodge directions;
- bare same-weight `L^2` native realization;
- `ProjectiveOrbitIrreducibility`;
- projective visibility of a separator ghost;
- universal algebraic pairing separation;
- an operator statement already equivalent to target-sheet algebraicity.

Those have been formally audited as Hodge-strength/circular.

Internal GST Poincare reversal is **not** by itself a classical native return.
The actual backward operator must remain an honest graded native/cycle-class
operator, preferably through the new finite closed correspondence carrier.

## Correct live geometry target

For the complementary power `F = L^(d-2p)`, construct an actual graded finite
closed correspondence return `R` and prove geometric identities such as:

1. pointwise Betti/cycle-class naturality;
2. return Hodge preservation;
3. projection-formula adjointness;
4. nonzero-scaled polarized Lefschetz pairing;
5. hard-Lefschetz surjectivity of `F` on the Hodge fibers.

These are operator/pairing statements, not algebraicity statements. They are
the intended noncircular frontier.

## Primitive residual

Even perfect complementary transport does **not** solve the primitive/middle
Hodge defect. Do not claim otherwise. The next mathematical burst must attack
that residual with the repo's primitive GST cosmology without reintroducing a
same-weight Hodge-equivalent externalization hypothesis.

## GLM task

Register and compile, preserving mathematical strength/direction:

- `GSTClassicalHodgeComplementaryDefectReciprocity`
- `GSTClassicalHodgeDefectModuloAtomicReciprocity`
- `GSTClassicalHodgeGradedFiniteClosedCorrespondence`
- `GSTClassicalHodgeDefectAnnihilatorReciprocity`
- `GSTClassicalHodgePolarizedDefectReciprocity`
- `GSTClassicalHodgePolarizedAdjointReciprocity`
- `GSTClassicalHodgePolarizedGradedCorrespondenceCrown`

Repair syntax/elaboration only. Do not replace a weakened quotient/pairing law
with a stronger Hodge-equivalent interface.
