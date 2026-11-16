/-
Copyright (c) 2026. The HC-Proof owner's GST hypothesis program.
-/
import GSTTwelvePointCohomology
import GSTGeometricRealizationStage2G
import GSTGeometricRealizationStage2D
import GSTNativeCodimensionCyclePresentation
import GSTClassicalHodgeFiberedCosmology

/-!
# GST TWELVE-POINT HODGE DATA

The first genuine `HodgeBigradedBettiData` of the corpus: the twelve-point
world's Hodge structure.

* At weight `p = 0` the honest zero-dimensional bigrading: every class of
  `H⁰` is of type `(0, 0)` — the single component is the whole
  complexification, the rational Hodge fiber is the entire `H⁰` (a LIVE
  rank-12 fiber).
* At weights `p ≥ 1` the fibers are dead by dimension: `H^{2p} = 0` for
  `2p ≥ 2` (the cohomology vanishing of the discrete world), and every
  grading on the zero module is trivially independent and spanning.
* `cycleClass` at weight 0 is the genuine degree map: a zero-cycle
  `Z = Σ aᵢ pᵢ` maps to the multiplicity vector through the pinned H⁰ iso
  `twelvePointCohomologyIso`.  The class of the `i`-th point cycle is the
  indicator vector `Pi.single i 1`.

Contract delivered downstream (`GSTTwelvePointFoldWord` and
`GSTTwelvePointLawLanding`): `twelvePointHodgeData`,
`zeroCycleClass` (with `twelvePointHodgeData.cycleClass 0` definitionally
equal to it), `zeroCycleClass_point`, `zeroFiber_eq_top`, and
`deadFiber_subsingleton`.

No `sorry`, no new axioms, no `native_decide`.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicGeometry
open TensorProduct
open GSTProjectiveOverC
open GSTGeometricRealizationStage2C
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTNativeCodimensionCyclePresentation
open GSTTwelvePointWorldCarrier
open GSTTwelvePointAnalytification
open GSTTwelvePointCohomology

namespace GSTTwelvePointHodgeData

/-! ## §1 SUBSINGLETON HELPERS -/

/-- In a subsingleton module every pair of submodules coincides. -/
theorem subsingleton_submodules_eq {R : Type} [CommSemiring R] {M : Type}
    [AddCommGroup M] [Module R M] [Subsingleton M] (P Q : Submodule R M) :
    P = Q :=
  Submodule.ext fun m => by
    constructor
    · intro _
      have h : m = 0 := Subsingleton.elim m 0
      subst h
      exact Q.zero_mem
    · intro _
      have h : m = 0 := Subsingleton.elim m 0
      subst h
      exact P.zero_mem

/-- The complexification of a subsingleton ℚ-module is subsingleton:
every pure tensor has a zero left factor. -/
theorem subsingleton_complexification {VQ : Type}
    [AddCommGroup VQ] [Module ℚ VQ] [Subsingleton VQ] :
    Subsingleton (Complexification VQ) := by
  -- WAVE 17 (pre-exposure D1): the original induction motive `fun z => z = y`
  -- was unsound in the add-branches (from `x₁ = y` and `x₂ = y` one gets
  -- `y + y = y`, false); everything is zero in a subsingleton module — prove
  -- both sides zero separately.
  constructor
  intro x y
  have hx : x = 0 := by
    induction x using TensorProduct.induction_on with
    | zero => rfl
    | tmul b v =>
      rw [show v = 0 from Subsingleton.elim v 0, TensorProduct.tmul_zero]
    | add x₁ x₂ ih₁ ih₂ => rw [ih₁, ih₂, add_zero]
  have hy : y = 0 := by
    induction y using TensorProduct.induction_on with
    | zero => rfl
    | tmul b v =>
      rw [show v = 0 from Subsingleton.elim v 0, TensorProduct.tmul_zero]
    | add y₁ y₂ ih₁ ih₂ => rw [ih₁, ih₂, add_zero]
  rw [hx, hy]

/-- `Fin 1` is a subsingleton index type. -/
theorem fin1_subsingleton : Subsingleton (Fin 1) :=
  ⟨fun a b => Fin.ext (by have := a.2; have := b.2; omega)⟩

/-! ## §2 THE HONEST (0, 0)-BIGRADING AT WEIGHT ZERO -/

/-- The honest Hodge bigrading of the weight-zero fiber: `H⁰` of a
zero-dimensional analytic space is entirely of type `(0, 0)` — the single
component (the `Fin 1` index is the (0,0)-position itself) is the whole
complexification, the decomposition is trivially independent. -/
noncomputable def zeroBigrading :
    HodgeBigrading (RationalSingularCohomology twelvePointAnalytification 0) 0
    where
  component := fun _ => ⊤
  independent := by
    haveI : Subsingleton (Fin 1) := fin1_subsingleton
    exact iSupIndep_subsingleton _
  spans := by
    refine le_antisymm le_top ?_
    exact le_iSup (f := fun _ : Fin 1 =>
      (⊤ : Submodule ℂ (Complexification
        (RationalSingularCohomology twelvePointAnalytification 0)))) ⟨0, by omega⟩

/-! ## §3 THE TRIVIAL BIGRADING AT THE DEAD WEIGHTS -/

/-- The Hodge bigrading of a dead weight: the module `H^{2p}` is
subsingleton (the cohomology vanishing of the discrete world), so its
complexification lattice collapses — every family of components is
trivially independent and the total supremum is the top. -/
noncomputable def deadBigrading (p : Nat) (hp : 0 < p) :
    HodgeBigrading
      (RationalSingularCohomology twelvePointAnalytification (2 * p)) (2 * p)
    where
  component := fun _ => ⊥
  independent := by
    haveI hsub : Subsingleton
        (RationalSingularCohomology twelvePointAnalytification (2 * p)) :=
      twelvePointCohomology_subsingleton _ (by omega)
    haveI hcomp : Subsingleton (Complexification
        (RationalSingularCohomology twelvePointAnalytification (2 * p))) :=
      subsingleton_complexification
    haveI hlat : Subsingleton (Submodule ℂ (Complexification
        (RationalSingularCohomology twelvePointAnalytification (2 * p)))) :=
      ⟨fun P Q => subsingleton_submodules_eq P Q⟩
    intro i
    have hsup : (⨆ (j) (_ : j ≠ i),
        (fun _ : Fin (2 * p + 1) =>
          (⊥ : Submodule ℂ (Complexification
            (RationalSingularCohomology twelvePointAnalytification (2 * p))))) j) = ⊥ :=
      Subsingleton.elim _ _
    rw [hsup]
    -- WAVE 18 (B4 pin-probe): `disjoint_self`'s `a` is IMPLICIT at the pin
    -- (Order/Disjoint.lean:99-101) — the positional `⊥` is ill-typed; the
    -- named-argument form (or the bare `disjoint_bot_right`) is the fix.
    exact (disjoint_self (a := ⊥)).mpr rfl
  spans := by
    haveI hsub : Subsingleton
        (RationalSingularCohomology twelvePointAnalytification (2 * p)) :=
      twelvePointCohomology_subsingleton _ (by omega)
    haveI hcomp : Subsingleton (Complexification
        (RationalSingularCohomology twelvePointAnalytification (2 * p))) :=
      subsingleton_complexification
    haveI hlat : Subsingleton (Submodule ℂ (Complexification
        (RationalSingularCohomology twelvePointAnalytification (2 * p)))) :=
      ⟨fun P Q => subsingleton_submodules_eq P Q⟩
    exact Subsingleton.elim _ _

/-! ## §4 THE GENUINE DEGREE MAP AT WEIGHT ZERO -/

/-- The genuine cycle-class map at weight zero: the degree map of the
twelve-point world, transporting the multiplicity vector of a zero-cycle
through the pinned H⁰ isomorphism. -/
noncomputable def zeroCycleClass :
    codimensionCycles twelvePointWorld.X 0 →ₗ[ℚ]
      RationalSingularCohomology twelvePointAnalytification 0 :=
  { toFun := fun Z =>
      twelvePointCohomologyIso.symm
        (fun i => (Z : AlgebraicCycle twelvePointWorld.X ℚ) ((twelvePointEquiv i).1))
    map_add' := by
      intro Z W
      -- WAVE 17 (pre-exposure D5): ascribe at the CARRIER level first (the
      -- CI-green PointNormalForm idiom) — the ambient-level `Z + W` show is
      -- not definitional (Submodule.coe_add is propositional).
      show twelvePointCohomologyIso.symm
          (fun i => ((Z + W : codimensionCycles twelvePointWorld.X 0) :
            AlgebraicCycle twelvePointWorld.X ℚ) ((twelvePointEquiv i).1)) =
        twelvePointCohomologyIso.symm
          (fun i => (Z : AlgebraicCycle twelvePointWorld.X ℚ)
            ((twelvePointEquiv i).1)) +
        twelvePointCohomologyIso.symm
          (fun i => (W : AlgebraicCycle twelvePointWorld.X ℚ)
            ((twelvePointEquiv i).1))
      rw [← map_add]
      congr 1
      funext i
      simp [Function.locallyFinsuppWithin.coe_add, Pi.add_apply]
    map_smul' := by
      intro q Z
      -- WAVE 17 (pre-exposure D5): the same carrier-level ascription; the
      -- `Submodule.coe_smul` bridge plus the green reference's simp set.
      show twelvePointCohomologyIso.symm
          (fun i => ((q • Z : codimensionCycles twelvePointWorld.X 0) :
            AlgebraicCycle twelvePointWorld.X ℚ) ((twelvePointEquiv i).1)) =
        q • twelvePointCohomologyIso.symm
          (fun i => (Z : AlgebraicCycle twelvePointWorld.X ℚ)
            ((twelvePointEquiv i).1))
      rw [← map_smul]
      congr 1
      funext i
      rw [Submodule.coe_smul]
      simp [algebraicCycleRatSMul_apply, Pi.smul_apply, smul_eq_mul] }

/-- The `i`-th point cycle as a codimension point of the world. -/
def twelvePointPt (i : Fin 12) : CodimensionPoint twelvePointWorld.X 0 :=
  ⟨(twelvePointEquiv i).1, (twelvePointEquiv i).2⟩

/-- **THE POINT-CLASS EQUATION.**  The class of the `i`-th point cycle is
the `i`-th indicator vector under the H⁰ iso — by construction of the
degree map. -/
theorem zeroCycleClass_point (i : Fin 12) :
    twelvePointCohomologyIso
      (zeroCycleClass (codimensionPointCycle twelvePointWorld.X 0
        (twelvePointPt i))) =
      Pi.single i (1 : ℚ) := by
  show twelvePointCohomologyIso (twelvePointCohomologyIso.symm
      (fun j => (codimensionPointCycle twelvePointWorld.X 0 (twelvePointPt i) :
        AlgebraicCycle twelvePointWorld.X ℚ) ((twelvePointEquiv j).1))) =
    Pi.single i (1 : ℚ)
  rw [LinearEquiv.apply_symm_apply]
  funext j
  have hval : (codimensionPointCycle twelvePointWorld.X 0 (twelvePointPt i) :
      AlgebraicCycle twelvePointWorld.X ℚ) ((twelvePointEquiv j).1) =
      (if (twelvePointEquiv j).1 = (twelvePointEquiv i).1 then (1 : ℚ) else 0) := by
    -- WAVE 17 (pre-exposure D8): the CI-green simp form (PointNormalForm:71)
    -- instead of the term-mode `single_apply _ _ _` arity guess.
    simp [codimensionPointCycle, Function.locallyFinsuppWithin.single_apply]
  rw [hval, Pi.single_apply]
  by_cases hj : j = i
  · subst hj
    simp
  · rw [if_neg (fun hcon =>
        hj (twelvePointEquiv.injective (Subtype.ext hcon))),
      if_neg hj]

/-! ## §5 THE FIBER FACTS -/

/-- The rational Hodge fiber of a grading whose `(p, p)`-component is the
whole space is the whole module. -/
theorem rationalHodgeSubspace_of_top
    {VQ : Type} [AddCommGroup VQ] [Module ℚ VQ] {p : Nat}
    (D : HodgeBigrading VQ (2 * p))
    (htop : D.ppComponent = ⊤) :
    rationalHodgeSubspace D = ⊤ :=
  Submodule.ext fun m => by
    constructor
    · intro _
      exact Submodule.mem_top m
    · intro _
      rw [mem_rationalHodgeSubspace_iff, htop]
      exact Submodule.mem_top _

/-- **THE WEIGHT-ZERO FIBER IS LIVE.**  The rational Hodge fiber of the
twelve-point world at weight zero is the entire `H⁰` — a live rank-12
fiber: the honest Hodge structure of the zero-dimensional world. -/
theorem zeroFiber_eq_top :
    rationalHodgeSubspace (p := 0) zeroBigrading = ⊤ := by
  -- WAVE 17 (pre-exposure D9): force the weight-0 implicit explicitly — the
  -- `2 * ?p =?= 0` nonlinear unification from the literal-0 index is not
  -- solvable; the resulting term is unchanged (tier-6's rw-pattern
  -- `rationalHodgeSubspace zeroBigrading` is preserved).
  have hpp : (HodgeBigrading.ppComponent (p := 0)) zeroBigrading = ⊤ := rfl
  exact rationalHodgeSubspace_of_top (p := 0) zeroBigrading hpp

/-! ## §6 THE ASSEMBLY -/

/-- The genuine cycle-class map at a dead weight: any linear map into the
subsingleton module is the zero map up to subsingleton collapse. -/
noncomputable def deadCycleClass (p : Nat) (hp : 0 < p) :
    codimensionCycles twelvePointWorld.X p →ₗ[ℚ]
      RationalSingularCohomology twelvePointAnalytification (2 * p) :=
  { toFun := fun _ => 0
    map_add' := by
      intro Z W
      haveI hsub : Subsingleton
          (RationalSingularCohomology twelvePointAnalytification (2 * p)) :=
        twelvePointCohomology_subsingleton _ (by omega)
      exact Subsingleton.elim _ _
    map_smul' := by
      intro q Z
      haveI hsub : Subsingleton
          (RationalSingularCohomology twelvePointAnalytification (2 * p)) :=
        twelvePointCohomology_subsingleton _ (by omega)
      exact Subsingleton.elim _ _ }

/-- **THE FIRST GENUINE HODGE DATA.**  The twelve-point world's Hodge
structure: the discrete analytification, the honest `(0, 0)`-bigrading at
weight zero with the dead gradings above, and the genuine degree-map
cycle class. -/
noncomputable def twelvePointHodgeData :
    HodgeBigradedBettiData twelvePointWorld where
  analytification := twelvePointAnalytification
  hodgeBigrading :=
    fun p =>
      match p with
      | 0 => zeroBigrading
      | q + 1 => deadBigrading (q + 1) (by omega)
  cycleClass :=
    fun p =>
      match p with
      | 0 => zeroCycleClass
      | q + 1 => deadCycleClass (q + 1) (by omega)

/-- The weight-`p` rational Hodge fiber of the assembled Hodge data. -/
theorem twelvePointHodgeData_bigrading_zero :
    twelvePointHodgeData.hodgeBigrading 0 = zeroBigrading := rfl

/-- **THE DEAD FIBERS ARE SUBSINGLETONS.**  At every positive weight the
rational Hodge fiber of the twelve-point world is a subsingleton: the
ambient module `H^{2p}` vanishes. -/
theorem deadFiber_subsingleton (p : Nat) (hp : 0 < p) :
    Subsingleton (ClassicalHodgeFiber twelvePointWorld twelvePointHodgeData p) := by
  have hsub : Subsingleton
      (RationalSingularCohomology twelvePointAnalytification (2 * p)) :=
    twelvePointCohomology_subsingleton _ (by omega)
  exact ⟨fun a b => Subtype.ext (@Subsingleton.elim _ hsub a.1 b.1)⟩

theorem twelvePointHodgeData_cycleClass_zero :
    twelvePointHodgeData.cycleClass 0 = zeroCycleClass := rfl

theorem twelvePointHodgeData_analytification_eq :
    twelvePointHodgeData.analytification = twelvePointAnalytification := rfl

theorem twelvePointHodgeData_bigrading_pos (p : Nat) (hp : 0 < p) :
    twelvePointHodgeData.hodgeBigrading p = deadBigrading p hp := by
  -- WAVE 17 (pre-exposure D11): rcases guarantees the dependent-hypothesis
  -- substitution the tactic-position match could not.
  rcases p with _ | q
  · exact absurd hp (by omega)
  · rfl

/-! ## Receipts -/

#check subsingleton_submodules_eq
#check subsingleton_complexification
#check fin1_subsingleton
#check zeroBigrading
#check deadBigrading
#check zeroCycleClass
#check twelvePointPt
#check zeroCycleClass_point
#check rationalHodgeSubspace_of_top
#check zeroFiber_eq_top
#check twelvePointHodgeData_bigrading_zero
#check twelvePointHodgeData_bigrading_pos
#check deadFiber_subsingleton
#check deadCycleClass
#check twelvePointHodgeData
#check twelvePointHodgeData_cycleClass_zero
#check twelvePointHodgeData_analytification_eq

#print axioms subsingleton_submodules_eq
#print axioms subsingleton_complexification
#print axioms fin1_subsingleton
#print axioms zeroCycleClass_point
#print axioms rationalHodgeSubspace_of_top
#print axioms zeroFiber_eq_top
#print axioms deadFiber_subsingleton
#print axioms twelvePointHodgeData_bigrading_pos

end GSTTwelvePointHodgeData

end -- noncomputable section
