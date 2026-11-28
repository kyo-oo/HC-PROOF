import HamSandwich.SphereOddDegree.AlgebraicTopology.SubChainSubspaceBridge
import HamSandwich.SphereOddDegree.AlgebraicTopology.SingularHomologyQ
import Mathlib

/-!
# The rational subspace bridge: subordinate chains ≅ singular chains of `S`

The vendored `SubChainSubspaceBridge.lean` proves, for an arbitrary commutative
ring `R`, that the subordinate-chain complex `subChainComplex R X S` (singular
chains of `X` supported in `S ⊆ X`) is isomorphic, on homology, to the singular
chains of the subspace `S` (`subspaceHomologyIso`).  Its two *specialization*
exports are however ℤ-hardwired:

* `subspaceHomologyIsoℤ` — the bridge at `ℤ`;
* `isZero_subChainComplex_homology_of_contractible` — contractible vanishing of
  the subordinate-chain homology at `ℤ`.

This file adds the matching ℚ exports (the duplication route: no vendored file
is modified):

* `subspaceHomologyIsoQ` — the bridge at `ℚ`, identifying the subordinate-chain
  homology with `Hₙ(S; ℚ)`;
* `isZero_subChainComplex_homology_of_contractibleQ` — for a contractible
  subspace `S` and `n ≥ 1`, the rational subordinate-chain homology vanishes.

The underlying `subspaceHomologyIso` is `[CommRing R]`-generic, so these are
pure instantiations plus the ℚ contractible-vanishing theorem
(`isZero_singularHomologyQ_of_contractibleSpace`).
-/

open CategoryTheory AlgebraicTopology Limits
open SphereOddDegree.AffineBarycentricSubdivision

noncomputable section
namespace SphereOddDegree

/-- **Rational bridge on homology.** The subordinate-chain homology of
`S ⊆ X` (at rational coefficients) is isomorphic to `Hₙ(S; ℚ)`, the rational
singular homology of the subspace.  (Mirror of `subspaceHomologyIsoℤ`.) -/
noncomputable def subspaceHomologyIsoQ (X : TopCat.{0}) (S : Set X) (n : ℕ) :
    (subChainComplex ℚ X S).homology n ≅ (singularHomologyQ n).obj (TopCat.of S) :=
  subspaceHomologyIso S n

/-- **Rational vanishing for contractible subspaces.** If `S ⊆ X` is
contractible and `n ≥ 1`, then the rational subordinate-chain homology
vanishes.  (Mirror of `isZero_subChainComplex_homology_of_contractible`.) -/
theorem isZero_subChainComplex_homology_of_contractibleQ
    (X : TopCat.{0}) (S : Set X) [ContractibleSpace S] (n : ℕ) (hn : 1 ≤ n) :
    IsZero ((subChainComplex ℚ X S).homology n) :=
  IsZero.of_iso (isZero_singularHomologyQ_of_contractibleSpace n hn S)
    (subspaceHomologyIsoQ X S n)

end SphereOddDegree

/-! ## PORT NOTES (the commander's CI-repair map)

Seams adapted in this file (ℚ duplication of the subspace bridge):

1. `subspaceHomologyIso` (SubChainSubspaceBridge.lean) is `[CommRing R]`-generic
   including the `subChainCorestrict` isomorphism machinery beneath it; the ℚ
   export `subspaceHomologyIsoQ` is a pure instantiation, accepted by the same
   defeq (`(singularHomologyQ n).obj (TopCat.of S)` vs. the raw
   `(((singularChainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)).obj
   (TopCat.of S)).homology n`) that the vendored ℤ wrapper
   `subspaceHomologyIsoℤ` already relies on.
2. `isZero_subChainComplex_homology_of_contractibleQ` replaces the ℤ-only
   `isZero_singularHomologyℤ_of_contractibleSpace` by the ℚ version
   `isZero_singularHomologyQ_of_contractibleSpace` (SingularHomologyQ.lean),
   whose own proof instantiates Mathlib's coefficient-generic totally
   disconnected vanishing at `ModuleCat ℚ`.
-/
