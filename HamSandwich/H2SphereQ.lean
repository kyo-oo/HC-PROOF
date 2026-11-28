import HamSandwich.SphereOddDegree.AlgebraicTopology.SphereSuspensionTowerFromMVQ
import GSTSphereUnionComponents
import GSTSingularCohomologyMaps
import Mathlib

/-
Copyright (c) 2026. The HC-PROOF campaign. All rights reserved.

# THE ℚ-INSTANTIATED SPHERE ENDPOINT (wave 13-E1)

`Nontrivial ((singularChainsOf (TopCat.of unitSphereType)).homology 2)` —
the degree-2 rational singular homology of the honest 2-sphere is NONZERO,
in the corpus's exact spelling (`singularChainsOf` from
`GSTSingularCohomologyMaps.lean`, `unitSphereType` from
`GSTSphereUnionComponents.lean`).

The engine is the vendored HamSandwich sphere-homology machine
(`HamSandwich/SphereOddDegree/`, upstream akopjan/HamSandwich @ 76202db,
Mathlib v4.28 code on this repo's pin v4.33.0-rc2), which proves
`Hₙ(Sⁿ; ℤ) ≅ ℤ` via subdivision → small chains → Mayer–Vietoris →
suspension tower.  That machine is ℤ-hardwired at five spots (the homology
functor abbreviations, the augmentation layer, the contractible vanishing,
the S¹-base finrank helpers, the tower instantiations); this wave's
duplication route re-derives each of them at ℚ in NEW files (suffix `Q`),
importing — never modifying — the vendored modules:

* `AlgebraicTopology/SingularHomologyQ.lean` — the ℚ functors, homotopy
  invariance (via the vendored coefficient-generic prism
  `singularChainHomotopyOfHomotopyModule`), contractible vanishing;
* `AlgebraicTopology/SubChainSubspaceBridgeQ.lean` — the rational subspace
  bridge;
* `AlgebraicTopology/SingularH0Q.lean` — the rational augmentation layer
  (`augQ`, `H0augQ`, `subH0augQ`, naturality);
* `AlgebraicTopology/SphereHomologyQ.lean` — the ℚ abbreviations, the model
  bridge, the tower type `SphereSuspensionTowerQ`;
* `AlgebraicTopology/SphereHomologyMVStepQ.lean` — the rational MV step
  `Hₙ₊₁(Sⁿ⁺¹; ℚ) ≅ Hₙ(Sⁿ; ℚ)`;
* `AlgebraicTopology/SphereHomologyS1BaseMVQ.lean` — the rational MV base
  case `H₁(S¹; ℚ) ≅ ℚ`;
* `AlgebraicTopology/SphereSuspensionTowerFromMVQ.lean` — the assembled
  tower and `sphereTopHomologyIso_unconditional_Q n hn : Hₙ(Sⁿ; ℚ) ≅ ℚ`.

This file transports the `n = 2` instance onto the corpus carrier
(`unitSphereType` IS the vendored `Sphere 2` — `Fin (2 + 1) = Fin 3` by
kernel literal reduction, `rfl`-certified below) and reads off the
nontriviality of `H₂` from the nontriviality of `ModuleCat.of ℚ ℚ`.

Universe discipline: Type-0 throughout (`TopCat.{0}`, `ModuleCat.{0}`).

The expected axiom set of every endpoint below is the standard three
(`propext`, `Classical.choice`, `Quot.sound`) — anything else, and in
particular `sorryAx`, red-flags the lane.
-/

set_option maxHeartbeats 4000000

noncomputable section

open CategoryTheory AlgebraicTopology Limits
open GSTSphereUnionComponents
open GSTSingularCohomologyMaps

namespace SphereOddDegree

/-! ## §1 The carrier bridge: `Sphere 2` IS `unitSphereType` -/

/-- **The two sphere models are the same type.** The vendored
`Sphere 2 = ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (2 + 1))) 1)` and the
corpus's `unitSphereType = ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)`
are definitionally equal (`Fin (2 + 1)` kernel-reduces to `Fin 3`). -/
theorem sphere2_eq_unitSphereType :
    Sphere 2 = unitSphereType :=
  rfl

/-- **Defeq identification of the corpus chain complex with the port's.** The
corpus's `singularChainsOf (TopCat.of unitSphereType)` (the spelling of the
FENCE-Ω discharge) is definitionally the vendored
`singularChainComplex ℚ (TopCat.of (Sphere 2))` — the same
`singularChainComplexFunctor (ModuleCat ℚ)`, the same coefficient object
`rationalCoefficient = ModuleCat.of ℚ ℚ`, at the same (definitionally equal)
carrier. -/
theorem singularChainsOf_unitSphereType_eq :
    singularChainsOf (TopCat.of unitSphereType)
      = singularChainComplex ℚ (TopCat.of (Sphere 2)) :=
  rfl

/-! ## §2 The tower at `n = 2` -/

/-- **The rational top-homology of the 2-sphere over `TopCat.sphere 2`:**
`H₂(S²; ℚ) ≅ ℚ`, the `n = 2` instance of the unconditional rational
suspension tower. -/
noncomputable def sphereTopHomologyIsoQ_two : SphereTopHomologyIsoQ 2 :=
  sphereTopHomologyIso_unconditional_Q 2 (by norm_num)

/-- **The rational second homology of the raw 2-sphere carrier** (the port's
`Sphere 2`), obtained by transporting `sphereTopHomologyIsoQ_two` across the
rational model bridge `sphereModelHomologyIsoQ`. -/
noncomputable def h2SphereHomologyIsoQ :
    (singularChainComplex ℚ (TopCat.of (Sphere 2))).homology 2 ≅ ModuleCat.of ℚ ℚ :=
  (sphereModelHomologyIsoQ 2 2).symm ≪≫ sphereTopHomologyIso_unconditional_Q 2 (by norm_num)

/-- **The same isomorphism in the corpus spelling** — the carrier is
`unitSphereType` and the chain complex is `singularChainsOf`.  The body is the
port-side iso; the identification is the `rfl` of
`singularChainsOf_unitSphereType_eq`. -/
noncomputable def h2SphereHomologyIsoQ_corpus :
    (singularChainsOf (TopCat.of unitSphereType)).homology 2 ≅ ModuleCat.of ℚ ℚ :=
  h2SphereHomologyIsoQ

/-! ## §3 Nontriviality transport -/

/-- The rational coefficient object is a nontrivial module
(`↥(ModuleCat.of ℚ ℚ)` is definitionally `ℚ`). -/
theorem nontrivial_rat_object : Nontrivial ↥(ModuleCat.of ℚ ℚ) :=
  nontrivial_of_ne (0 : ℚ) 1 one_ne_zero

/-- **Nontriviality transports backwards along a `ModuleCat` isomorphism.**
If `A ≅ B` in `ModuleCat.{0} ℚ` and `B` is nontrivial, then `A` is nontrivial
(pull two distinct elements of `B` back through the isomorphism). -/
theorem nontrivial_of_iso_Q {A B : ModuleCat.{0} ℚ} (e : A ≅ B)
    (h : Nontrivial ↥B) : Nontrivial ↥A := by
  obtain ⟨x, y, hxy⟩ := h
  refine ⟨e.toLinearEquiv.symm x, e.toLinearEquiv.symm y, fun hc => hxy ?_⟩
  exact e.toLinearEquiv.symm.injective hc

/-! ## §4 THE ENDPOINT -/

/-- **THE ℚ-INSTANTIATED SPHERE ENDPOINT (corpus spelling).** The degree-2
rational singular homology of the honest 2-sphere
`unitSphereType = ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)` is
nontrivial:

```text
Nontrivial ((singularChainsOf (TopCat.of unitSphereType)).homology 2).
```

Proof: the rational suspension tower gives
`H₂(S²; ℚ) ≅ ModuleCat.of ℚ ℚ` (`h2SphereHomologyIsoQ_corpus`, on the corpus
carrier by the `rfl` carrier identification), and nontriviality transports
backwards along the isomorphism from `nontrivial_rat_object`. -/
theorem nontrivial_sphereHomology_two :
    Nontrivial ((singularChainsOf (TopCat.of unitSphereType)).homology 2) :=
  nontrivial_of_iso_Q h2SphereHomologyIsoQ_corpus nontrivial_rat_object

end SphereOddDegree

/-! ## §5 Receipts (the audit pattern of `H2SphereAudit.lean`) -/

#check @SphereOddDegree.sphere2_eq_unitSphereType
#check @SphereOddDegree.singularChainsOf_unitSphereType_eq
#check @SphereOddDegree.sphereTopHomologyIsoQ_two
#check @SphereOddDegree.h2SphereHomologyIsoQ
#check @SphereOddDegree.h2SphereHomologyIsoQ_corpus
#check @SphereOddDegree.nontrivial_sphereHomology_two
#check @SphereOddDegree.sphereTopHomologyIso_unconditional_Q

/- The expected axiom set of each endpoint is the standard three:
`propext`, `Classical.choice`, `Quot.sound`. -/
#print axioms SphereOddDegree.sphere2_eq_unitSphereType
#print axioms SphereOddDegree.singularChainsOf_unitSphereType_eq
#print axioms SphereOddDegree.sphereTopHomologyIsoQ_two
#print axioms SphereOddDegree.h2SphereHomologyIsoQ
#print axioms SphereOddDegree.h2SphereHomologyIsoQ_corpus
#print axioms SphereOddDegree.nontrivial_sphereHomology_two
#print axioms SphereOddDegree.sphereTopHomologyIso_unconditional_Q

/-! ## PORT NOTES (the commander's CI-repair map)

Every seam adapted on the way to `nontrivial_sphereHomology_two` (all ℚ
duplication lives in NEW files; NO vendored file is touched):

1. **The five ℤ-hardwired spots of the vendored machine** and their ℚ
   replacements (duplication route):
   - `singularChainℤ` / `singularHomologyℤ` / `sphereHomologyℤ` /
     `sphereTopHomologyℤ` (HomotopyToChainHomotopy.lean,
     SphereTopHomology.lean) → `singularChainQ` / `singularHomologyQ` /
     `sphereHomologyQ` / `sphereTopHomologyQ` at `ModuleCat.{0} ℚ`,
     coefficient `ModuleCat.of ℚ ℚ` (SingularHomologyQ.lean,
     SphereHomologyQ.lean).
   - `aug` / `H0aug` / `subH0aug` + naturality (SingularH0.lean,
     SingularH0PathConnected.lean) → `augQ` / `H0augQ` / `subH0augQ` +
     naturality (SingularH0Q.lean).  ℚ-specific simplification: the ℤ
     `AddSubgroup.closure` detour of `sub_aug_smul_basept_mem_range`
     (module-instance diamond) is replaced by a plain `Submodule.span ℚ`
     induction; the ℤ `Subsingleton.elim` fix of `reducedH0_sphere0_iso` is
     dropped (no ℤ-module diamond at a field).
   - `isZero_subChainComplex_homology_of_contractible` /
     `isZero_singularHomologyℤ_of_contractibleSpace`
     (SubChainSubspaceBridge.lean, BallBoundaryLES.lean) → the `Q` versions;
     the underlying Mathlib lemma
     `isZero_singularHomologyFunctor_of_totallyDisconnectedSpace` is
     coefficient-category-generic at the pin and instantiates at
     `ModuleCat ℚ / ModuleCat.of ℚ ℚ` exactly as at ℤ.
   - `linearEquiv_int_of_finrank_one` / `ker_linearEquiv_int_of_finrank_two`
     (SphereHomologyS1BaseMV.lean, ℤ-specific: `Module.finBasis ℤ` +
     instance-diamond `Subsingleton.elim`) →
     `ker_linearEquiv_rat_of_finrank_two` over the field ℚ:
     `Submodule.finrank_quotient_add_finrank` (via
     `DivisionRing.hasRankNullity`) + `quotKerEquivOfSurjective` + `omega`,
     then `LinearEquiv.ofFinrankEq` (Free automatic at a field, Finite via
     hypothesis / `Module.Finite.self` / `finiteDimensional_submodule`).
   - `mvHomologyIso_succ ℤ …` / `mvShortExact ℤ …` tower instantiations →
     the `ℚ` instantiations (the MV machinery in MayerVietorisSES.lean /
     MayerVietoris.lean / SmallChainsQuasiIso.lean is `[CommRing R]`-generic
     throughout).
2. **Homotopy invariance at ℚ**: the vendored ℤ chain routes through
   `SingularPrismOperator` → `singularChainHomotopyOfHomotopy` (ℤ-only
   wrapper); the ℚ route uses the vendored coefficient-generic
   `singularChainHomotopyOfHomotopyModule ℚ (ModuleCat.of ℚ ℚ)` directly
   (Backports/PrismSimplicialHomotopy.lean) — no new prism content.
3. **Carrier identification seams (both `rfl`, live-certified in §1)**:
   - `Sphere 2 = unitSphereType` — `Fin (2 + 1)` vs `Fin 3`: kernel literal
     reduction; the `TopologicalSpace`/`MetricSpace` instance paths on the
     two type expressions are the same TC products at definitionally equal
     types.
   - `singularChainsOf (TopCat.of unitSphereType) = singularChainComplex ℚ
     (TopCat.of (Sphere 2))` — both unfold to
     `((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj
     (ModuleCat.of ℚ ℚ)).obj X` at the same `X`; the corpus's own
     `singularChainsOf_eq` (rfl-pattern) is the precedent.  Universe note:
     `singularChainsOf` is universe-polymorphic in the `TopCat` universe with
     an auto-bound `HasCoproducts.{u} (ModuleCat.{0} ℚ)` instance; at
     `TopCat.of unitSphereType : TopCat.{0}` it lands on the same
     `HasCoproducts.{0}` instance as the vendored `TopCat.{0}`-fixed
     `singularChainComplex`.
4. **Nontriviality transport**: Mathlib at the pin has NO
   `Nontrivial.of_equiv`; the transport `nontrivial_of_iso_Q` is proved by
   pulling a witnessing pair back through `e.toLinearEquiv.symm`
   (`LinearEquiv.injective` at the pin).  `Nontrivial ↥(ModuleCat.of ℚ ℚ)`
   is `nontrivial_of_ne (0 : ℚ) 1 one_ne_zero`, accepted by the definitional
   unfolding of the `ModuleCat.of` carrier (repair point if CI disagrees:
   `show Nontrivial ℚ; exact ⟨0, 1, one_ne_zero⟩`).
5. **Not duplicated** (not needed for the ℚ endpoint): the ℤ degree/orientation
   consumer layer (`SphereOrientation` / `SphereOrientationPos`,
   `degreeOfIso`), `BallBoundaryLES.lean`'s disk layer, and the ℤ-only
   `Sphere 0` obstruction analysis of `SphereTopHomologyReduction.lean`.
6. **Residual risk flagged for CI** (in decreasing order):
   - the verbatim-mirrored `simp +decide` / `grind` / `aesop` fragments inside
     `SingularH0Q.lean` and `SphereHomologyS1BaseMVQ.lean` (copied from the
     CI-green ℤ file; ℚ-arithmetic is at least as decidable as ℤ-arithmetic,
     but grind/aesop search is not fully deterministic);
   - the instance-composition `ModuleCat.kernelIsoKer _ ≪≫
     LinearEquiv.toModuleIso e` of `reducedH0_sphere0_isoQ` (no diamond at ℚ
     expected; if CI reports an instance mismatch, insert an `eqToIso`
     bridge exactly as the ℤ original's `Subsingleton.elim` spot);
   - the `h0_sphere0Q_finite_finrank` TC searches
     (`Module.Finite ℚ ↥(∐ _)` through the DirectSum instances — the same
     search that succeeds at ℤ);
   - the two `rfl` carrier identifications of §1 (if the second one fails,
     bridge through `sphere2_eq_unitSphereType` with
     `congrArg`/`eqRec` instead).
-/
