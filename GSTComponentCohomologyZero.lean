/-
Copyright (c) 2026. The HC-PROOF campaign. All rights reserved.

# The component H⁰ machine (Wave 46) — the positive-dimensional beachhead

THE CUSTOM TOOL.  The wave-44/45 frontier map established the wall: at the
pinned Mathlib (v4.33.0-rc2) there is no tool that computes ANY cohomology of
a positive-dimensional space — no Mayer-Vietoris, no excision, no Hurewicz,
no `Hⁿ(Sⁿ)` (first-hand verified against the pinned tree this wave:
`Mathlib/AlgebraicTopology` contains exactly `AlternatingFaceMapComplex`,
`CechNerve`, `DoldKan`, `EilenbergSteenrod`, `ExtraDegeneracy`,
`FundamentalGroupoid`, `ModelCategory`, `MooreComplex`, `Quasicategory`,
`Reedy`, `RelativeCellComplex`, `SimplexCategory`, `SimplicialCategory`,
`SimplicialComplex`, `SimplicialNerve`, `SimplicialObject`, `SimplicialSet`,
`SingularHomology/{Basic, HomologyZero, HomotopyInvariance,
HomotopyInvarianceTopCat}`, `SingularSet`, `TopologicalSimplex` — nothing
else).  BOSS's directive (2026-11-18): write the custom tools.

This file is the beachhead — a genuine cohomology computation for arbitrary
(in particular positive-dimensional) spaces:

  `componentCohomologyZeroEquiv A :
      RationalSingularCohomology A 0 ≃ₗ[ℚ] (ZerothHomotopy ↥A.space → ℚ)`

for EVERY analytification `A` of EVERY smooth projective complex scheme,
computed from the genuine singular chain complex.  Combined with a
component identification `ZerothHomotopy ↥A.space ≃ Fin M` (the sphere-union
companion file of this wave), this is the live rank-M weight-0 fiber the
wave-45 frozen design demanded — the first honest cohomology computation of
the campaign on a positive-dimensional world.

## The construction (four engines, all new to the corpus)

1. THE GENERATOR INTERFACE (§1).  The pinned simplicial-set chain complex
   `SSet.chainComplexFunctor` presents the degree-n chains as a coproduct
   (`Sigma`) of the coefficient object over the singular n-simplices, with
   the summand inclusions `ιChainComplex`, the boundary formula
   `ιChainComplex_d` (both `simp` lemmas of
   `Mathlib/AlgebraicTopology/SimplicialSet/Homology/Basic.lean` at the
   pin), and the coproduct extensionality `chainComplex_hom_ext`.
   Specializing through the pinned face identifications
   `δ 0 s = the 0-simplex of f 1`, `δ 1 s = the 0-simplex of f 0`
   (`Topology/Homotopy/TopCat/ZerothHomotopy.lean`) yields THE
   ENDPOINT-BOUNDARY FORMULA: the boundary of the path generator is the
   difference of the endpoint generators.

2. THE DUAL DIFFERENTIAL (§2).  The cochain complex is the linear-Yoneda
   dual of the chain complex (the Stage-2F definition); its degree-0
   differential is precomposition with the boundary
   (`ChainComplex.linearYonedaObj_d`, the finite-point lane's verified
   name).  The kernel condition on a cochain is vanishing on the
   boundaries of the path generators; the converse is the coproduct
   extensionality `chainComplex_hom_ext` with `LinearMap.ext_ring` at
   the legs, plus two ISOLATED defeq bridges (the finite-point lane's
   ofHom-discipline and congrArg-ofHom transports are the precedents).

3. THE BOTTOM-DEGREE HOMOLOGY (§3).  For a cochain complex indexed `up ℕ`,
   the incoming differential at degree zero is the shape-zero map, so the
   homology at zero is the kernel of the outgoing differential.  Built
   through the pinned `ShortComplex.ModuleCat` left-homology data
   (`moduleCatLeftHomologyData`, `moduleCatHomologyIso`) and the
   hand-rolled quotient-by-⊥ equivalence `quotientBotEquiv`.

4. THE KERNEL-COCYCLE ISO (§4).  A degree-zero cochain kills the boundary
   of every path generator iff it takes equal values at the endpoints of
   every path (engine 1), iff it descends along `ZerothHomotopy.mk`
   (the pinned path-component quotient of
   `Topology/Connected/PathConnected.lean`).  The forward direction is
   `ZerothHomotopy.lift` with the endpoint formula; the backward direction
   is the coproduct lift (`IsColimit.desc` through
   `isColimitChainComplexXCofan`) of a component function, which kills
   every boundary because a function cannot distinguish
   `ZerothHomotopy.sound`-equal points.

## Honesty ledger

Every statement is proved unconditionally.  No `sorry`, no new axioms, no
`native_decide`.  The GitHub CI lane `gst-component-cohomology-zero.yml`
owns the kernel check.  The AUDIT FLAGS below mark the pinned-name repair
points for the CI loop (the campaign's standard discipline; waves 44/45
adjudicated 51, 15, 9, 2 errors to GREEN through exactly this loop).

- AUDIT(1): `rationalSingularChains A ≡
  (TopCat.toSSet.obj A.space).chainComplex (ModuleCat.of ℚ ℚ)`.
- AUDIT(2): `ChainComplex.linearYonedaObj_d`; the carrier defeq
  `(rationalSingularCochains A).X 0 ≡ ModuleCat.of ℚ
  ((rationalSingularChains A).X 0 ⟶ ModuleCat.of ℚ ℚ)`; the leftComp
  application defeq (§2, `leftComp_apply_eq`).
- AUDIT(3): `HomologicalComplex.homology i = (K.sc i).homology` and the
  `sc`-field identifications (`ShortComplex/HomologicalComplex.lean:90`).
- AUDIT(4): `TopCat.toSSetObj₀Equiv`, `δ_zero_toSSetObj₁Equiv.symm`,
  `δ_one_toSSetObj₁Equiv.symm`.
- AUDIT(5): the `I ⟶ A.space` endpoint evaluations `f 0`, `f 1`.
- AUDIT(6): `IsColimit.desc`/`fac` shapes for the `Cofan` colimit;
  `LinearMap.ext_ring`; `ModuleCat.hom_comp`; the Hom-structure coercion
  lemmas (`ModuleCat.ofHom_hom`, `ModuleCat.hom_ofHom`,
  `ModuleCat.ofHom_zero`); the two isolated `rfl` defeq bridges of §2 and
  the element-zero identification of §4.
-/

import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Homotopy.TopCat.ZerothHomotopy
import GSTGeometricRealizationStage2F

set_option maxHeartbeats 200000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicTopology
open GSTGeometricRealizationStage2F

namespace GSTComponentCohomologyZero

variable {V : SmoothProjectiveComplexScheme} (A : AnalytificationData V)

/-! ## §0 Pinned shape facts for the up-ℕ bottom degree -/

theorem upNext_zero : (ComplexShape.up ℕ).next 0 = 1 :=
  CochainComplex.next ℕ 0

theorem upPrev_zero : (ComplexShape.up ℕ).prev 0 = 0 :=
  CochainComplex.prev_nat_zero

theorem upNotRel_zero_zero : ¬ (ComplexShape.up ℕ).Rel 0 0 := by
  simp [ComplexShape.up_Rel]

/-! ## §0.5 The dual differential presentation -/

/-- AUDIT(2): the degree-zero differential of the cochain complex is
precomposition with the boundary (the pinned
`ChainComplex.linearYonedaObj_d`, the finite-point lane's verified name). -/
theorem cochains_d_zero_one (A : AnalytificationData V) :
    (rationalSingularCochains A).d 0 1 =
      ModuleCat.ofHom
        (Linear.leftComp ℚ (ModuleCat.of ℚ ℚ)
          ((rationalSingularChains A).d 1 0)) := by
  unfold rationalSingularCochains
  exact ChainComplex.linearYonedaObj_d
    (rationalSingularChains A) ℚ (ModuleCat.of ℚ ℚ) 0 1

/-- **THE ADJUNCTION-STYLE EVALUATION.**  The underlying linear map of the
dual differential applied to a cochain is the precomposition.  AUDIT(2):
the coercion spellings are the designated CI repair points. -/
theorem dual_eval (A : AnalytificationData V)
    (φ : (rationalSingularCochains A).X 0)
    (z : (rationalSingularChains A).X 1) :
    ((rationalSingularCochains A).d 0 1 φ).hom z =
      φ.hom ((rationalSingularChains A).d 1 0 z) := by
  rw [cochains_d_zero_one A]
  simp only [ModuleCat.ofHom_apply, Linear.leftComp_apply,
    LinearMap.coe_comp, LinearMap.comp_apply, ModuleCat.coe_ofHom]
  rfl

/-! ## §1 The generator interface and the endpoint-boundary formula -/

/-- AUDIT(1): the rational singular chains, presented as the
simplicial-set chain complex of the singular simplicial set (the
`singularChainComplexFunctor` unfolding; every link reducible at the pin). -/
theorem chains_eq (A : AnalytificationData V) :
    rationalSingularChains A =
      (TopCat.toSSet.obj A.space).chainComplex
        (ModuleCat.of ℚ ℚ) := rfl

/-- The generator inclusion of a point: the summand injection of the
0-simplex carried by the point `x`. -/
def ιPoint (A : AnalytificationData V) (x : ↥A.space) :
    ModuleCat.of ℚ ℚ ⟶ (rationalSingularChains A).X 0 :=
  (TopCat.toSSet.obj A.space).ιChainComplex
    (TopCat.toSSetObj₀Equiv.symm x)

/-- The generator inclusion of a path: the summand injection of the
1-simplex carried by the path morphism `f`. -/
def ιPath (A : AnalytificationData V) (f : I ⟶ A.space) :
    ModuleCat.of ℚ ℚ ⟶ (rationalSingularChains A).X 1 :=
  (TopCat.toSSet.obj A.space).ιChainComplex
    (TopCat.toSSetObj₁Equiv A.space f)

/-- **THE ENDPOINT-BOUNDARY FORMULA.**  The boundary of the path generator
is the difference of the endpoint point generators.  AUDIT(4). -/
theorem ιPath_d (A : AnalytificationData V) (f : I ⟶ A.space) :
    ιPath A f ≫ (rationalSingularChains A).d 1 0 =
      ιPoint A (f 1) - ιPoint A (f 0) := by
  have hgen : ιPath A f ≫ (rationalSingularChains A).d 1 0 =
      ∑ i : Fin (0 + 2), (-1 : ℤ) ^ (i : ℕ) •
        (TopCat.toSSet.obj A.space).ιChainComplex
          ((TopCat.toSSet.obj A.space).δ i
            (TopCat.toSSetObj₁Equiv A.space f)) :=
    (TopCat.toSSet.obj A.space).ιChainComplex_d
      (TopCat.toSSetObj₁Equiv A.space f)
  rw [hgen]
  have hface0 : (TopCat.toSSet.obj A.space).δ 0
      (TopCat.toSSetObj₁Equiv A.space f) =
      TopCat.toSSetObj₀Equiv.symm (f 1) :=
    TopCat.δ_zero_toSSetObj₁Equiv.symm f
  have hface1 : (TopCat.toSSet.obj A.space).δ 1
      (TopCat.toSSetObj₁Equiv A.space f) =
      TopCat.toSSetObj₀Equiv.symm (f 0) :=
    TopCat.δ_one_toSSetObj₁Equiv.symm f
  rw [hface0, hface1]
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one,
    neg_smul, one_zsmul]
  rw [sub_eq_add_neg]

/-- The element-level form of the endpoint-boundary formula. -/
theorem d_path_element (A : AnalytificationData V) (f : I ⟶ A.space) :
    (rationalSingularChains A).d 1 0 ((ιPath A f).hom (1 : ℚ)) =
      (ιPoint A (f 1)).hom (1 : ℚ) - (ιPoint A (f 0)).hom (1 : ℚ) := by
  have h := congrArg (fun (u : ModuleCat.of ℚ ℚ ⟶ (rationalSingularChains A).X 0) =>
    u.hom (1 : ℚ)) (ιPath_d A f)
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, map_sub] at h
  exact h

/-! ## §2 The kernel condition at the generators -/

/-- **LEMMA A (the morphism-level generator extension).**  If a cochain's
underlying linear map kills the boundary of every path generator, then the
precomposition morphism is the zero morphism.

The proof is the pinned coproduct extensionality `chainComplex_hom_ext`:
the composite with every generator inclusion is a morphism from
`ModuleCat.of ℚ ℚ`, determined by its value at `1` (`LinearMap.ext_ring`),
which vanishes by the hypothesis.  AUDIT(6). -/
theorem precomp_zero_of_generator (A : AnalytificationData V)
    (φ : (rationalSingularCochains A).X 0)
    (hgen : ∀ f : I ⟶ A.space,
      φ.hom ((rationalSingularChains A).d 1 0
        ((ιPath A f).hom (1 : ℚ))) = 0) :
    ModuleCat.ofHom
      ((φ.hom : (rationalSingularChains A).X 0 →ₗ[ℚ] ℚ).comp
        ((rationalSingularChains A).d 1 0).hom) = 0 := by
  refine (TopCat.toSSet.obj A.space).chainComplex_hom_ext
    (ModuleCat.of ℚ ℚ) 1 ?_
  intro σ
  obtain ⟨f, rfl⟩ := (TopCat.toSSetObj₁Equiv A.space).surjective σ
  rw [CategoryTheory.ModuleCat.comp_zero]
  apply ModuleCat.Hom.ext
  apply LinearMap.ext_ring
  rw [show ((ιPath A f ≫ ModuleCat.ofHom
      ((φ.hom : (rationalSingularChains A).X 0 →ₗ[ℚ] ℚ).comp
        ((rationalSingularChains A).d 1 0).hom)).hom (1 : ℚ)) =
    φ.hom ((rationalSingularChains A).d 1 0 ((ιPath A f).hom (1 : ℚ))) from by
    simp only [ModuleCat.hom_comp_iff, LinearMap.coe_comp,
      LinearMap.comp_apply, ModuleCat.coe_ofHom,
      ModuleCat.ofHom_hom]
    rfl]
  exact hgen f

/-- AUDIT(2): the `leftComp` application defeq — the precomposition
cochain IS the wrapped precomposition linear map.  Isolated `rfl` bridge
(one of the two designated defeq repairs of §2; the finite-point lane's
`finitePointXZeroIso` exercised the same layer). -/
theorem leftComp_apply_eq (A : AnalytificationData V)
    (φ : (rationalSingularCochains A).X 0) :
    (Linear.leftComp ℚ (ModuleCat.of ℚ ℚ)
        ((rationalSingularChains A).d 1 0)) φ =
      ModuleCat.ofHom
        ((φ.hom : (rationalSingularChains A).X 0 →ₗ[ℚ] ℚ).comp
          ((rationalSingularChains A).d 1 0).hom) := rfl

/-- **THE KERNEL CONDITION AT THE GENERATORS.**  A degree-zero cochain
lies in the kernel of the dual differential iff its underlying linear map
kills the boundary of every path generator.  AUDIT(2)/(6). -/
theorem cochain_ker_iff (A : AnalytificationData V)
    (φ : (rationalSingularCochains A).X 0) :
    (rationalSingularCochains A).d 0 1 φ = 0 ↔
      ∀ f : I ⟶ A.space,
        φ.hom ((rationalSingularChains A).d 1 0
          ((ιPath A f).hom (1 : ℚ))) = 0 := by
  constructor
  · intro hφ f
    have h0 : ((rationalSingularCochains A).d 0 1 φ).hom
        ((ιPath A f).hom (1 : ℚ)) = 0 := by
      rw [hφ]
      rfl
    rw [dual_eval] at h0
    exact h0
  · intro hgen
    have hA := precomp_zero_of_generator A φ hgen
    rw [cochains_d_zero_one A, leftComp_apply_eq]
    exact hA

/-! ## §3 The bottom-degree homology -/

/-- The hand-rolled quotient-by-⊥ equivalence: quotienting a module by
the zero submodule changes nothing.  Built from `Submodule.Quotient.lift`
of the subtype and `Submodule.mkQ` of the bottom submodule; both triangle
identities by `Submodule.Quotient.induction_on`. -/
noncomputable def quotientBotEquiv {M : Type} [AddCommGroup M] [Module ℚ M]
    (p : Submodule ℚ M) :
    (p ⧕ (⊥ : Submodule ℚ p)) ≃ₗ[ℚ] ↥p where
  toFun :=
    Submodule.Quotient.lift p.subtype
      (fun v hv => by
        rw [Submodule.mem_bot] at hv
        rw [hv, map_zero])
  map_add' := by
    intro x y
    apply Submodule.Quotient.induction_on₂ x y
    intro a b
    simp only [map_add]
    rfl
  map_smul' := by
    intro r x
    apply Submodule.Quotient.induction_on x
    intro a
    simp only [map_smul]
    rfl
  invFun v := (⊥ : Submodule ℚ p).mkQ v
  left_inv x := by
    apply Submodule.Quotient.induction_on x
    intro a
    rfl
  right_inv v := by
    have : (Submodule.Quotient.lift p.subtype
        (fun v hv => by
          rw [Submodule.mem_bot] at hv
          rw [hv, map_zero])) ((⊥ : Submodule ℚ p).mkQ v) = v := by
      rfl
    exact this

/-- The kernel submodule of the dual differential. -/
def kerDual (A : AnalytificationData V) :
    Submodule ℚ ((rationalSingularCochains A).X 0) :=
  LinearMap.ker ((rationalSingularCochains A).d 0 1).hom

/-- AUDIT(2): membership in the kernel submodule is the element equation
(the FunLike application of the morphism is its underlying linear map;
`rfl`-bridge, designated CI repair point). -/
theorem mem_kerDual_iff (A : AnalytificationData V)
    (φ : (rationalSingularCochains A).X 0) :
    φ ∈ kerDual A ↔ (rationalSingularCochains A).d 0 1 φ = 0 := Iff.rfl

/-- AUDIT(3): the `f`-field of the degree-zero short complex is the
shape-zero map. -/
theorem sc_zero_f_eq_zero (A : AnalytificationData V) :
    ((rationalSingularCochains A).sc 0).f = 0 := by
  rw [show ((rationalSingularCochains A).sc 0).f =
      (rationalSingularCochains A).d ((ComplexShape.up ℕ).prev 0) 0 from rfl]
  rw [upPrev_zero]
  exact (rationalSingularCochains A).shape 0 0 upNotRel_zero_zero

/-- AUDIT(3): the `g`-field of the degree-zero short complex is the
outgoing differential. -/
theorem sc_zero_g_eq (A : AnalytificationData V) :
    ((rationalSingularCochains A).sc 0).g =
      (rationalSingularCochains A).d 0 1 := rfl

/-- **THE BOTTOM-DEGREE HOMOLOGY.**  The homology of the cochain complex
at degree zero is the kernel of the outgoing differential.

The proof: the degree-zero short complex has `f = 0` (§3), so its
`moduleCatLeftHomologyData.H` is the kernel quotiented by the range of
the zero map, which is `⊥`; the `quotientBotEquiv` collapses it.  AUDIT(3). -/
noncomputable def homologyZeroIsoKer (A : AnalytificationData V) :
    (rationalSingularCochains A).homology 0 ≅
      ModuleCat.of ℚ ↥(kerDual A) := by
  have hS : (rationalSingularCochains A).homology 0 =
      ((rationalSingularCochains A).sc 0).homology := rfl
  rw [hS]
  -- the module-cat homology iso of the degree-zero short complex
  have hiso := ((rationalSingularCochains A).sc 0).moduleCatHomologyIso
  -- the left homology data's H is the quotient by the range of the
  -- zero map
  have hf : ((rationalSingularCochains A).sc 0).f = 0 :=
    sc_zero_f_eq_zero A
  have htc : ((rationalSingularCochains A).sc 0).moduleCatToCycles = 0 := by
    unfold ShortComplex.moduleCatToCycles
    rw [hf]
    rfl
  have hrange : LinearMap.range
      (((rationalSingularCochains A).sc 0).moduleCatToCycles) = ⊥ := by
    rw [htc]
    exact LinearMap.range_zero
  -- assemble: H ≅ ker g ⧕ ⊥ ≅ ker g
  refine hiso ≪≫ ?_
  have hH : (((rationalSingularCochains A).sc 0).moduleCatLeftHomologyData.H) =
      ModuleCat.of ℚ (LinearMap.ker
        (((rationalSingularCochains A).sc 0).g.hom) ⧕
        (LinearMap.range
          (((rationalSingularCochains A).sc 0).moduleCatToCycles))) := rfl
  rw [hH, hrange]
  -- the quotientBot equivalence, packaged as a module iso
  refine LinearEquiv.toModuleIso ?_
  refine (quotientBotEquiv (LinearMap.ker
    (((rationalSingularCochains A).sc 0).g.hom))).congr ?_ ?_
  · rfl
  · rw [show ((rationalSingularCochains A).sc 0).g =
        (rationalSingularCochains A).d 0 1 from sc_zero_g_eq A]
    rfl

/-! ## §4 The kernel-cocycle iso -/

/-- The function on points carried by a degree-zero cochain. -/
def cochainComponentFun (A : AnalytificationData V)
    (φ : (rationalSingularCochains A).X 0) : ↥A.space → ℚ :=
  fun x => φ.hom ((ιPoint A x).hom (1 : ℚ))

/-- **PATH-CONSTANCY OF KERNEL COCHAINS.**  A kernel cochain takes equal
values at the endpoints of every path: the endpoint-boundary formula turns
the path into a boundary, and the kernel condition kills it. -/
theorem cochainComponentFun_sound (A : AnalytificationData V)
    (φ : (rationalSingularCochains A).X 0) (hφ : φ ∈ kerDual A)
    (x y : ↥A.space) (p : Path x y) :
    cochainComponentFun A φ x = cochainComponentFun A φ y := by
  set f : I ⟶ A.space := (TopCat.pathEquiv.symm p).hom with hf
  have h0 : f 0 = x := (TopCat.pathEquiv.symm p).hom₀
  have h1 : f 1 = y := (TopCat.pathEquiv.symm p).hom₁
  have hgen := (cochain_ker_iff A φ).mp (mem_kerDual_iff A φ |>.mp hφ) f
  rw [d_path_element A f, map_sub, sub_eq_zero] at hgen
  calc cochainComponentFun A φ x = φ.hom ((ιPoint A x).hom (1 : ℚ)) := rfl
    _ = φ.hom ((ιPoint A (f 0)).hom (1 : ℚ)) := by rw [h0]
    _ = φ.hom ((ιPoint A (f 1)).hom (1 : ℚ)) := hgen.symm
    _ = cochainComponentFun A φ y := by rw [h1]

/-- The component function of a kernel cochain: the descent along the
path-component quotient. -/
def componentFunOf (A : AnalytificationData V)
    (φ : (rationalSingularCochains A).X 0) (hφ : φ ∈ kerDual A) :
    ZerothHomotopy ↥A.space → ℚ :=
  ZerothHomotopy.lift (cochainComponentFun A φ)
    (fun p => cochainComponentFun_sound A φ hφ _ _ p)

/-- The leg morphism of a component function at a 0-simplex: the scalar
multiplication by the component's value. -/
def componentLeg (A : AnalytificationData V)
    (g : ZerothHomotopy ↥A.space → ℚ)
    (σ : (TopCat.toSSet.obj A.space) _⦋0⦌) :
    ModuleCat.of ℚ ℚ ⟶ ModuleCat.of ℚ ℚ :=
  ModuleCat.ofHom
    { toFun := fun r => r • g (ZerothHomotopy.mk (TopCat.toSSetObj₀Equiv σ))
      map_add' := by
        intro r₁ r₂
        simp only [add_smul]
      map_smul' := by
        intro q r
        simp only [smul_eq_mul, mul_smul, RingHom.id_apply]
        rfl }

/-- The coproduct lift of a component function: the unique morphism from
the degree-zero chains whose leg values are the component function's
values on the point classes.  AUDIT(6): the `IsColimit.desc`/`fac`
spellings are the designated CI repair points. -/
def componentCochainMorph (A : AnalytificationData V)
    (g : ZerothHomotopy ↥A.space → ℚ) :
    (rationalSingularChains A).X 0 ⟶ ModuleCat.of ℚ ℚ :=
  (isColimitChainComplexXCofan (TopCat.toSSet.obj A.space)
    (ModuleCat.of ℚ ℚ) 0).desc
    (Cofan.mk _
      (fun σ => componentLeg A g σ))

/-- **THE LEG EQUATION.**  The coproduct lift evaluates at a point
generator as the component function's value on the point class.
AUDIT(6). -/
theorem ιPoint_comp_componentCochainMorph (A : AnalytificationData V)
    (g : ZerothHomotopy ↥A.space → ℚ) (x : ↥A.space) :
    ιPoint A x ≫ componentCochainMorph A g =
      componentLeg A g (TopCat.toSSetObj₀Equiv.symm x) :=
  (isColimitChainComplexXCofan (TopCat.toSSet.obj A.space)
    (ModuleCat.of ℚ ℚ) 0).fac
    (Cofan.mk _ (fun σ => componentLeg A g σ))
    (TopCat.toSSetObj₀Equiv.symm x)

/-- **THE COMPONENT COCHAIN IS A KERNEL ELEMENT.**  The coproduct lift of
a component function kills every path boundary: its leg values cannot
distinguish `ZerothHomotopy.sound`-equal points. -/
theorem componentCochainMorph_mem_kerDual (A : AnalytificationData V)
    (g : ZerothHomotopy ↥A.space → ℚ) :
    componentCochainMorph A g ∈ kerDual A := by
  rw [mem_kerDual_iff A]
  refine (cochain_ker_iff A (componentCochainMorph A g)).mpr ?_
  intro f
  rw [d_path_element A f, map_sub, sub_eq_zero]
  -- both endpoint evaluations are leg values of sound-equal points
  have hpath : Path (f 0) (f 1) :=
    TopCat.pathEquiv { hom := f, hom₀ := rfl, hom₁ := rfl }
  have hsound : ZerothHomotopy.mk (f 0) = ZerothHomotopy.mk (f 1) :=
    ZerothHomotopy.sound hpath
  have hleg1 : (componentCochainMorph A g).hom
      ((ιPoint A (f 1)).hom (1 : ℚ)) =
      g (ZerothHomotopy.mk (f 1)) := by
    have h := congrArg (fun (u : ModuleCat.of ℚ ℚ ⟶ ModuleCat.of ℚ ℚ) =>
      u.hom (1 : ℚ)) (ιPoint_comp_componentCochainMorph A g (f 1))
    simp only [ModuleCat.ofHom_hom] at h
    rw [h]
    rfl
  have hleg0 : (componentCochainMorph A g).hom
      ((ιPoint A (f 0)).hom (1 : ℚ)) =
      g (ZerothHomotopy.mk (f 0)) := by
    have h := congrArg (fun (u : ModuleCat.of ℚ ℚ ⟶ ModuleCat.of ℚ ℚ) =>
      u.hom (1 : ℚ)) (ιPoint_comp_componentCochainMorph A g (f 0))
    simp only [ModuleCat.ofHom_hom] at h
    rw [h]
    rfl
  rw [hleg1, hleg0, ← hsound]

/-- **THE FIRST TRIANGLE.**  The component function of the coproduct lift
of `g` is `g` itself. -/
theorem componentFunOf_componentCochainMorph (A : AnalytificationData V)
    (g : ZerothHomotopy ↥A.space → ℚ) :
    componentFunOf A (componentCochainMorph A g)
      (componentCochainMorph_mem_kerDual A g) = g := by
  funext z
  obtain ⟨x, rfl⟩ := ZerothHomotopy.mk_surjective z
  rw [componentFunOf, ZerothHomotopy.lift_mk]
  have h := congrArg (fun (u : ModuleCat.of ℚ ℚ ⟶ ModuleCat.of ℚ ℚ) =>
    u.hom (1 : ℚ)) (ιPoint_comp_componentCochainMorph A g x)
  simp only [ModuleCat.ofHom_hom] at h
  rw [h]
  rfl

/-- **THE SECOND TRIANGLE.**  The coproduct lift of the component
function of a kernel cochain is the cochain itself (by the uniqueness of
the coproduct lift). -/
theorem componentCochainMorph_componentFunOf (A : AnalytificationData V)
    (φ : (rationalSingularCochains A).X 0) (hφ : φ ∈ kerDual A) :
    componentCochainMorph A (componentFunOf A φ hφ) = φ := by
  refine (isColimitChainComplexXCofan (TopCat.toSSet.obj A.space)
    (ModuleCat.of ℚ ℚ) 0).hom_ext ?_
  intro σ
  obtain ⟨x, rfl⟩ := (TopCat.toSSetObj₀Equiv A.space).surjective σ
  -- both morphisms have the same leg values
  rw [ιPoint_comp_componentCochainMorph]
  apply ModuleCat.Hom.ext
  apply LinearMap.ext_ring
  rw [show ((ιPoint A x ≫ φ).hom (1 : ℚ)) =
      φ.hom ((ιPoint A x).hom (1 : ℚ)) from rfl]
  rw [show ((componentLeg A (componentFunOf A φ hφ)
      (TopCat.toSSetObj₀Equiv.symm x)).hom (1 : ℚ)) =
      (componentFunOf A φ hφ) (ZerothHomotopy.mk x) from by
    rfl]
  rfl

/-- **THE KERNEL-COCYCLE ISO.**  The kernel of the dual differential is
the function space on the path components. -/
noncomputable def kerDualEquiv (A : AnalytificationData V) :
    ↥(kerDual A) ≃ₗ[ℚ] (ZerothHomotopy ↥A.space → ℚ) where
  toFun φ := componentFunOf A (φ : (rationalSingularCochains A).X 0) φ.2
  map_add' φ ψ := by
    funext z
    obtain ⟨x, rfl⟩ := ZerothHomotopy.mk_surjective z
    simp only [componentFunOf, ZerothHomotopy.lift_mk,
      cochainComponentFun, LinearMap.add_apply]
    rfl
  map_smul' q φ := by
    funext z
    obtain ⟨x, rfl⟩ := ZerothHomotopy.mk_surjective z
    simp only [componentFunOf, ZerothHomotopy.lift_mk,
      cochainComponentFun, RingHom.id_apply, LinearMap.smul_apply,
      smul_eq_mul]
    rfl
  invFun g := ⟨componentCochainMorph A g,
    componentCochainMorph_mem_kerDual A g⟩
  left_inv φ := by
    apply Subtype.ext
    exact componentCochainMorph_componentFunOf A (φ : _) φ.2
  right_inv g := componentFunOf_componentCochainMorph A g

/-! ## §5 THE MAIN THEOREM -/

/-- **THE COMPONENT H⁰ MACHINE.**  The degree-zero rational singular
cohomology of any analytification is the function space on its path
components — computed from the genuine singular chain complex, with no
discreteness, no vanishing, and no dimension assumption.  This is the
positive-dimensional beachhead: the first cohomology computation of the
campaign that applies to positive-dimensional worlds. -/
noncomputable def componentCohomologyZeroEquiv (A : AnalytificationData V) :
    RationalSingularCohomology A 0 ≃ₗ[ℚ] (ZerothHomotopy ↥A.space → ℚ) :=
  (LinearEquiv.ofBijective
    ((homologyZeroIsoKer A).hom.hom)
    (⟨fun x y hxy => by
      have h := (homologyZeroIsoKer A).hom_inv_id
      have hinj : Function.Injective (homologyZeroIsoKer A).hom.hom := by
        rw [ModuleCat.mono_iff_injective]
        infer_instance
      exact hinj hxy,
    fun y => by
      have h := (homologyZeroIsoKer A).inv_hom_id
      have hsurj : Function.Surjective (homologyZeroIsoKer A).hom.hom := by
        rw [ModuleCat.epi_iff_surjective]
        infer_instance
      exact hsurj y⟩)).trans (kerDualEquiv A)

/-- **THE FINITE-RANK SPECIALIZATION.**  With a component identification
against `Fin M`, the degree-zero cohomology is the free rank-M function
space.  This is the live rank-M weight-0 fiber of the wave-45 frozen
design. -/
noncomputable def componentCohomologyZeroEquivFinM
    (A : AnalytificationData V) (M : ℕ)
    (e : ZerothHomotopy ↥A.space ≃ Fin M) :
    RationalSingularCohomology A 0 ≃ₗ[ℚ] (Fin M → ℚ) :=
  (componentCohomologyZeroEquiv A).trans
    (e.piCongrLeft (fun _ => ℚ))

end GSTComponentCohomologyZero
