# GLM live handoff — transpose cycle correction

Target branch: `sol/hodge-single-separator-successor`

New mathematics commit:

`7a530fe47ac04ba80c36d1e0367e6f49b35f0724`

File:

`GSTClassicalHodgeFirstGhostTransposeCycleCorrection.lean`

## Mathematical change

The previous frontier supplied `ghost_scaled` as a scalar pairing identity.
This file removes that functional law from the interface.

It introduces one actual codimension-`p+1` cycle `Z` and the concrete Hodge
fiber equation

```text
L(K(E)) = scalar • E + cycleClass(Z)
```

with `scalar ≠ 0`.

Using `smoothProjective_cycleClass_range_eq_atomic_span`, the correction class
is automatically algebraic.  Hence every `OrthogonalToAlgebraicHodge` test
kills it.  Combining this with the already-repaired transpose projection law
proves `ghost_scaled` automatically and packages the result into
`FirstGhostTransposeAdjointScaledGeometry`.

The final theorem is:

`FirstGhostTransposeCycleCorrectionGeometry.firstFailure_forbids_transpose_cycleCorrection`

## Repair instructions

Repair syntax/coercions only.  Do **not** strengthen any mathematical field.
In particular do not add:

- Hodge surjectivity;
- projective irreducibility;
- a global matrix-unit realization;
- a global scaled pairing law;
- a global Hard-Lefschetz inverse.

Likely sensitive points:

- subtype equality in `ghost_roundtrip_cycle_correction`;
- `rw [map_add, map_smul]` for the curried perfect pairing;
- the namespace/coercion of `IsAlgebraicHodge`;
- the pipeline call to `firstFailure_forbids_transpose_adjoint_scaled_geometry`.

Register the file in the active Hodge build only after it compiles.  No `sorry`
or custom axiom.
