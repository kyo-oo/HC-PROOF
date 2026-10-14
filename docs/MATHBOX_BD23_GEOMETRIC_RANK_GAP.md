# Mathbox route: one-correspondence GST charge-wedge rank gain

- **Parent:** `bd23bac6ee8c81c45b71881666a898af093c9046`
- **Working branch:** `mathbox/bd23-single-operator-charge-wedge`
- **Target:** Independently generate a second genuine algebraic Hodge direction without postulating arbitrary matrix units or a target-cycle preimage.
- **Outcome:** Explicit rank-two criterion obtained; universal existence of a nonzero transverse class remains unproved.
- **Evidence:** `GSTClassicalHodgeSingleCorrespondenceRankTwo.lean`, with dedicated GitHub workflow `gst-single-correspondence-charge-wedge.yml`.

## Construction

Let `G : GeometricCycleClassSpine V H`, let `D : SpineTowerConservedCharge G`, and let `E : RealizedCorrespondenceExpr V H p`.

Take the actual native spine cycle `Z = spineNativeTower G p`, and its Betti class `s = spineHodgeSeed G p`. Write the linear conserved-charge functional as `ell = D.cohomologyRead p`, and `d = ell(s)`. The existing theorem `actualSpine_betti_charge_nonzero` establishes `d != 0`.

Define an explicit new *native algebraic cycle* by

```text
Delta(E) = d • E.cycleOperator Z - ell(E.cohomologyOperator s) • Z
```

and its Betti realization as

```text
delta(E) = d • E.cohomologyOperator s - ell(E.cohomologyOperator s) • s.
```

Cycle-class naturality proves `cycleClass(Delta(E)) = delta(E)`.
Linear charge cancellation proves `ell(delta(E)) = 0` exactly, with **no charge-eigenoperator hypothesis**.

If `delta(E) != 0`, the pair `s, delta(E)` is linearly independent: applying `ell` to a relation `a*s+b*delta(E)=0` forces `a=0` because `ell(s)!=0`; nonvanishing then forces `b=0`. Both vectors have actual native-cycle representatives. If the rational Hodge fiber has dimension 2, they span it, so every rational (p,p) class at that weight is algebraic.

## What this changes

The older `GSTClassicalHodgeActualCommutatorRankGain` route requires two realized correspondences, scalar-eigenfunctional laws for both, and a **nonzero commutator**. The charge wedge needs only one realized correspondence with a nonzero transverse output. The explicit charge cancellation requires neither a second operator nor an eigenfunctional law.

The geometric challenge is now one sharply falsifiable statement:

```text
For a specified rank-two Hodge fiber, is there an actual realized E such
that bettiChargeWedge G D E != 0?
```

This is **not** proved universally. The criterion is sufficient, not known necessary, and it does not itself address rank greater than 2. No new axiom, arbitrary Hodge target preimage, or fake "universal nonvanishing" is introduced.

## Adversarial interpretation

The source's existing `zeroCycleClassSpine` countermodel shows why compatible operator laws alone cannot force a genuine cycle-class map to hit every Hodge class. Separately, the parent branch's one-operator power-orbit theorem requires a nonzero determinant; that determinant's universal existence cannot be inferred merely from a computed polynomial expression.

For higher rank, the next independent GST geometric task is to construct **multiple provably independent transverse directions in the kernel of the conserved-charge functional**, or to use multiple native seeds not generated from the same orbit. Rewriting formal laws to assert nonvanishing would merely change the target instead of proving it.

## Verification contract

- Compile: `lake build GSTClassicalHodgeSingleCorrespondenceRankTwo` using GitHub Actions and the pinned toolchain.
- Audit: no `sorry`, `admit`, or custom assumption inserted into the proof.
- Mathematical evidence label: **conditional rank-two theorem**, with an explicit native construction.
- Original unconditional all-varieties rational Hodge target: **not established** by this route.
