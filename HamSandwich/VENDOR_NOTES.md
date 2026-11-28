# THE HAMSANDWICH VENDOR TREE — provenance and port notes (wave 13)

## Origin

- Upstream: https://github.com/akopjan/HamSandwich (Apache-2.0; the license
  is preserved verbatim as `LICENSE.HamSandwich` in this directory).
- Vendored revision: `76202db` (2026-07-06, the repository's `main` HEAD).
- Upstream toolchain: Lean `v4.28.0`, Mathlib `v4.28.0`.
- This repo's toolchain: Lean `v4.33.0-rc2`, Mathlib pin
  `51e6992efd06126df61a496bebf8f49482a4e129` — a FORWARD port (everything
  the cone needs exists at the pin modulo the edits below).

## What was vendored

The complete dependency cone of `sphereTopHomologyIso_unconditional`
(65 files, ~12.2k lines): the barycentric subdivision machine (the affine
layer, the operator, the boundary cancellation, the cone, the homotopy
operator and formula, the chain homotopy `Sd ≃ id`, the iteration, the
diameter/mesh contraction), the small-chains theory (open covers, Lebesgue
numbers, subordination, the quasi-isomorphism), the Mayer-Vietoris short
exact sequence and step isomorphism, the singular H₀ layer, and the sphere
suspension tower (the S¹ base case, the MV step, the tower assembly, the
unconditional isomorphism `H_n(S^n;ℤ) ≅ ℤ` on Mathlib's own
`singularChainComplexFunctor`).

The cone is upstream's CI axiom-audited spine (their CI greps
`#print axioms` output for `sorryAx`; the whole repo builds with zero
`sorry`/`admit`/`axiom`).

## The port edits (the complete list)

1. `SphereOddDegree/AlgebraicTopology/BarycentricSubdivisionDiameter.lean:110`
   — the one rename the 2026-06-03 `sdiff` migration forced:
   `Finset.sum_eq_sum_diff_singleton_add` → `Finset.sum_eq_sum_sdiff_singleton_add`
   (verified present at the pin: `Mathlib/Algebra/BigOperators/Group/Finset/Piecewise.lean`,
   the `to_additive` image of `prod_eq_prod_sdiff_singleton_mul`).
2. `H2SphereAudit.lean` — NEW (this campaign's audit target file; not upstream).

Everything else is byte-identical to upstream `76202db`.  The deprecated
alias `SSet.singularChainComplexFunctor` (4 use sites, renamed upstream
Mathlib-side to `SSet.chainComplexFunctor` since 2026-04-05) still resolves
at the pin — deprecation warnings only, no elaboration failure; the
cleanup passes to `chainComplexFunctor` happen in the trim wave after the
first green build.

## Why this tree exists (the campaign role)

FENCE-Ω (`∃ ω : singularCohomologyOf (TopCat.of unitSphereType) 2, ω ≠ 0`)
is the single hypothesis the kernel-certified wave-9 apex package carries
(the exists-flip master `GSTFiniteLineFenceDischarge`).  The pinned Mathlib
carries no sphere homology, no subdivision, no Mayer-Vietoris — the
wave-12 record reduced the fence to FENCE-S (the separator at the
fundamental cycle), whose mathematical content is exactly this machine.
Wave 13's design: the port supplies `H₂(S²;ℤ) ≅ ℤ` (and, at the next
strike round, the ℚ-instantiated form), the corpus-side composition
(the field-duality replay of the wave-12 realization machinery) turns the
nonvanishing into `∃ ω ≠ 0`, and the already-certified fence discharge
closes the wave-9 package's independence conjunct — the last subcase of
the X-audit.  See `research/records/2026-11-28-gst-wave13-hamsandwich-port.md`.

## Upstream credit

All mathematical content in this tree is the work of the HamSandwich
authors (akopjan), Apache-2.0.  The campaign's contribution is the port,
the ℚ endpoint, and the corpus-side composition — recorded in the wave-13
record.
