# Mathbox research route — HC-PROOF base bd23bac6

Base commit: `bd23bac6ee8c81c45b71881666a898af093c9046`.
Isolated research branch: `mathbox/bd23-single-operator-charge-wedge`.
Primary Lean file: `GSTClassicalHodgeSingleCorrespondenceRankTwo.lean`.
CI workflow: `.github/workflows/gst-single-correspondence-charge-wedge.yml`.

## Precise original missing implication

The source's genuinely realized finite-closed correspondence expression algebra produces native rational algebraic cycles, but it does **not** prove that the Hodge classes of its outputs span a general rational Hodge fiber. Its finite geometric power-orbit and noncommutative word-frame reconstruction theorems explicitly assume a nonzero determinant / full-rank matrix. No general theorem at the requested base supplies such a matrix on every smooth projective complex variety.

Moreover, `HodgeBigradedBettiData` stores the cycle class as an arbitrary linear map, and `GSTClassicalHodgeStage2GSemanticRigidity.lean` constructs the zero-map countermodel. Thus enlarging the GST abstract matrix-unit algebra, or asserting determinant nonvanishing as a new law, does not itself produce the genuine native geometric cycles demanded by the original Hodge claim.

## Executed route: weight-local charge wedge

At a fixed weight p, choose the native spine cycle `Z = spineNativeTower G p` and its Hodge class `s = spineHodgeSeed G p`. Let `T` be a genuinely realized correspondence expression, and choose one rational **weight-local** functional

```lean
ell : ClassicalHodgeFiber V H p →ₗ[ℚ] ℚ
```

with `ell s != 0`. Define `t = T.cohomologyOperator s`, an algebraic Hodge class because it is the class of `T.cycleOperator Z`.

The following is an actual native algebraic cycle:

```text
DeltaNative(T) = ell(s) • T.native(Z) - ell(t) • Z.
```

By exact native/cohomological naturality, its class is the Hodge-fiber vector

```text
delta(T) = ell(s) • t - ell(t) • s.
```

The charge cancellation is exact:

```text
ell(delta(T)) = ell(s)*ell(t) - ell(t)*ell(s) = 0.
```

If `delta(T) != 0`, it is independent of `s`, since `ell(s) != 0`. When the rational Hodge fiber has dimension exactly 2, the two algebraic classes form a basis. The existing atomic-span/range identity then represents any rational Hodge class with an actual codimension-p rational algebraic cycle.

This route needs **one** genuinely realized correspondence with transverse movement, rather than the earlier two correspondences whose nonzero commutator must also satisfy global charge-eigenfunctional laws.

## Corrected semantic issue in the older route

The older `SpineTowerConservedCharge G` assumes one nonzero base charge transported across **all** natural-number weights. Its theorems imply a nonzero cycle class at **every** such weight. For a genuinely finite-dimensional smooth projective complex variety the rational cohomology eventually vanishes in high degree, so that global premise cannot be offered as a universally inhabited geometric input. The new route uses only a linear readout on the single active Hodge fiber, allowing all other weights to be zero. This correction changes the proof hypotheses rather than declaring incompatible laws universally true.

## Evidence and limitations

- The Lean file contains `movedSpine`, `nativeChargeWedge`, `hodgeChargeWedge`, `nativeChargeWedge_cycleClass`, `hodgeChargeWedge_charge_zero`, `spine_chargeWedge_linearIndependent`, and `every_rank_two_hodge_class_of_one_transverse_correspondence`.
- **Mathematical claim:** an exact rank-two reduction conditional on `ell(s) != 0` and `delta(T) != 0`, not a solution of the unconditional Hodge conjecture.
- **Unproved geometric existence input:** produce such a genuinely realized correspondence with nonzero transverse action on an arbitrary rank-two Hodge fiber, or produce sufficiently many independent genuine algebraic directions in arbitrary rank.
- **Separate semantic input:** identify the cohomology and cycle-class map with the authentic geometric cohomological construction, not an unconstrained record field.
- **Verification:** check the corresponding GitHub Actions kernel compilation and sorry audit. Until a completed green run is observed for the revised commit, label the Lean file *written, verification pending*.

## Smallest decisive mathematical test

For a concrete smooth projective complex variety X with a two-dimensional rational (p,p) Hodge fiber and an independently constructed genuine nonzero algebraic spine Z, exhibit an actual finite closed correspondence T whose action on cl(Z) is not proportional to cl(Z). If none can be produced by the presently supported correspondence algebra, the limitation is geometric (not a missing polynomial-calculus theorem). No unverified universal nonvanishing is promoted to a law.
