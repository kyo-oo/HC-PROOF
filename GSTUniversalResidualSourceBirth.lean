import Mathlib.LinearAlgebra.Dual.Lemmas
import GSTClassicalHodgeGeometricCycleClassSpine
import GSTClassicalHodgeExactClayStatement

/-!
# GST UNIVERSAL DUAL RESIDUAL SOURCE-BIRTH — THE SINGLE CONDITIONAL HODGE TARGET

The native cycle-class image is a subspace of the rational Hodge fiber. The
one remaining source-generation law is that every nonzero linear functional
on that Hodge fiber is detected by an actual native algebraic cycle.

This module proves that this dual source-birth law is EXACTLY equivalent to
surjectivity of the cycle-class map, hence to the Stage-2G elementwise Hodge
target, once finite-dimensionality of the Hodge fiber is supplied.

No positive pairing is needed for the exact dual statement. A GST positive
perfect polarization identifies residual vectors with these dual witnesses,
so the polarized residual-energy formulation is an equivalent coordinate
presentation, not an additional hypothesis.

This is not a proof of the source-birth law. It isolates it as the sole
Hodge-strength target and proves the conditional theorem without F/G/D/R
bundles or a disguised cycle-preimage field.

Semantic boundary: Stage-2G stores the cycle-class map as supplied data.
The theorem applies to that map. It becomes the classical Hodge conjecture
only when that data is instantiated by the canonical geometric cycle-class
map on the actual smooth projective complex scheme.
-/

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeExactClayStatement

namespace GSTUniversalResidualSourceBirth

/-- Every nonzero dual witness detects at least one actual native cycle. -/
def DualResidualSourceBirth
    {N W : Type*}
    [AddCommGroup N] [Module ℚ N]
    [AddCommGroup W] [Module ℚ W]
    (cl : N →ₗ[ℚ] W) : Prop :=
  ∀ ψ : W →ₗ[ℚ] ℚ, ψ ≠ 0 → ∃ z : N, ψ (cl z) ≠ 0

/-- The dual residual source-birth law is equivalent to surjectivity of the
native cycle-class map. The forward implication is exactly injectivity of
the transpose map; finite-dimensionality of the target then forces the
original map to be surjective. -/
theorem dualResidualSourceBirth_iff_surjective
    {N W : Type*}
    [AddCommGroup N] [Module ℚ N]
    [AddCommGroup W] [Module ℚ W]
    [FiniteDimensional ℚ W]
    (cl : N →ₗ[ℚ] W) :
    DualResidualSourceBirth cl ↔ Function.Surjective cl := by
  constructor
  · intro hBirth
    apply (LinearMap.dualMap_injective_iff).mp
    intro φ ψ hEq
    by_contra hne
    have hdiff : φ - ψ ≠ 0 := sub_ne_zero.mpr hne
    obtain ⟨z, hz⟩ := hBirth (φ - ψ) hdiff
    have hEval : φ (cl z) = ψ (cl z) := by
      have hpoint := congrFun hEq z
      simpa only [LinearMap.dualMap_apply', LinearMap.comp_apply] using hpoint
    exact hz (by simp [hEval])
  · intro hsurj ψ hψ
    by_contra hNo
    have hzero : ∀ z : N, ψ (cl z) = 0 := by
      intro z
      by_contra hne
      exact hNo ⟨z, hne⟩
    have hψzero : ψ = 0 := by
      ext w
      rcases hsurj w with ⟨z, rfl⟩
      exact hzero z
    exact hψ hψzero

/-- A perfect pairing identifies residual vectors with dual witnesses. This
is the exact bridge from the polarized residual-energy language to the
dual source-birth law. -/
structure PerfectPairing
    (W : Type*) [AddCommGroup W] [Module ℚ W] where
  toDual : W ≃ₗ[ℚ] (W →ₗ[ℚ] ℚ)

/-- Polarized residual source-birth, expressed using a perfect pairing. -/
def PolarizedResidualSourceBirth
    {N W : Type*}
    [AddCommGroup N] [Module ℚ N]
    [AddCommGroup W] [Module ℚ W]
    (P : PerfectPairing W)
    (cl : N →ₗ[ℚ] W) : Prop :=
  ∀ r : W, r ≠ 0 → ∃ z : N, P.toDual r (cl z) ≠ 0

/-- The polarized residual law and the dual-witness law are equivalent; the
pairing is only a coordinate identification, not extra Hodge content. -/
theorem polarizedResidualSourceBirth_iff_dualResidualSourceBirth
    {N W : Type*}
    [AddCommGroup N] [Module ℚ N]
    [AddCommGroup W] [Module ℚ W]
    (P : PerfectPairing W)
    (cl : N →ₗ[ℚ] W) :
    PolarizedResidualSourceBirth P cl ↔ DualResidualSourceBirth cl := by
  constructor
  · intro hBirth ψ hψ
    let r : W := P.toDual.symm ψ
    have hr : r ≠ 0 := by
      intro hr0
      apply hψ
      have hzero : P.toDual r = 0 := by simp [hr0]
      simpa [r] using hzero
    obtain ⟨z, hz⟩ := hBirth r hr
    exact ⟨z, by simpa [r] using hz⟩
  · intro hBirth r hr
    have hψ : P.toDual r ≠ 0 := by
      intro hzero
      exact hr (P.toDual.injective (by simpa using hzero))
    obtain ⟨z, hz⟩ := hBirth (P.toDual r) hψ
    exact ⟨z, hz⟩

/-- The cycle-class map into the Hodge subspace, built without changing the
supplied Stage-2G cycle-class map. -/
noncomputable def hodgeCycleClassMap
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (G : GeometricCycleClassSpine V H)
    (p : Nat) :
    codimensionCycles V.X p →ₗ[ℚ]
      rationalHodgeSubspace (H.hodgeBigrading p) where
  toFun Z := ⟨H.cycleClass p Z, G.algebraic_is_hodge p Z⟩
  map_add' := by
    intro Z W
    apply Subtype.ext
    exact (H.cycleClass p).map_add Z W
  map_smul' := by
    intro q Z
    apply Subtype.ext
    exact (H.cycleClass p).map_smul q Z

/-- Finite-dimensionality of each rational Hodge fiber. For a genuine smooth
projective complex variety this is a standard structural property; it is
kept explicit because the Stage-2G abstract interface does not derive it. -/
structure FiniteDimensionalHodgeSemantics
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) where
  finiteDimensional :
    ∀ p : Nat,
      FiniteDimensional ℚ (rationalHodgeSubspace (H.hodgeBigrading p))

/-- The one GST target, simultaneously for every codimension: every nonzero
dual residual on the Hodge fiber has nonzero period on some actual native
codimension-p algebraic cycle. -/
def UniversalDualResidualSourceBirth
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (G : GeometricCycleClassSpine V H) : Prop :=
  ∀ p : Nat,
    DualResidualSourceBirth (hodgeCycleClassMap G p)

/-- CONDITIONAL HODGE THEOREM: the single universal dual source-birth law
forces every rational (p,p) class to have a native algebraic cycle
representative. -/
theorem everyHodgeClassIsRationalAlgebraic_of_universalDualResidualSourceBirth
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (G : GeometricCycleClassSpine V H)
    (S : FiniteDimensionalHodgeSemantics V H)
    (hBirth : UniversalDualResidualSourceBirth G) :
    EveryHodgeClassIsRationalAlgebraic H := by
  intro p alpha halpha
  letI := S.finiteDimensional p
  have hsurj :
      Function.Surjective (hodgeCycleClassMap G p) :=
    (dualResidualSourceBirth_iff_surjective
      (hodgeCycleClassMap G p)).mp (hBirth p)
  let target : rationalHodgeSubspace (H.hodgeBigrading p) :=
    ⟨alpha, halpha⟩
  obtain ⟨Z, hZ⟩ := hsurj target
  exact ⟨Z, congrArg Subtype.val hZ⟩

/-- Exactness of the reduction: under finite-dimensional Hodge semantics,
the universal dual residual source-birth law is equivalent to the Stage-2G
Hodge conjecture. It is the single remaining mathematical target, not an
easier substitute for the conjecture. -/
theorem universalDualResidualSourceBirth_iff_hodge
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (G : GeometricCycleClassSpine V H)
    (S : FiniteDimensionalHodgeSemantics V H) :
    UniversalDualResidualSourceBirth G ↔
      EveryHodgeClassIsRationalAlgebraic H := by
  constructor
  · exact everyHodgeClassIsRationalAlgebraic_of_universalDualResidualSourceBirth
      G S
  · intro hHodge p ψ hψ
    by_contra hNo
    have hzero : ∀ Z : codimensionCycles V.X p,
        ψ (hodgeCycleClassMap G p Z) = 0 := by
      intro Z
      by_contra hne
      exact hNo ⟨Z, hne⟩
    have hsurj : Function.Surjective (hodgeCycleClassMap G p) := by
      intro r
      obtain ⟨Z, hZ⟩ := hHodge p r.1 r.2
      exact ⟨Z, by
        apply Subtype.ext
        exact hZ⟩
    have hψzero : ψ = 0 := by
      ext r
      rcases hsurj r with ⟨Z, rfl⟩
      exact hzero Z
    exact hψ hψzero

#check DualResidualSourceBirth
#check dualResidualSourceBirth_iff_surjective
#check PerfectPairing
#check PolarizedResidualSourceBirth
#check polarizedResidualSourceBirth_iff_dualResidualSourceBirth
#check hodgeCycleClassMap
#check FiniteDimensionalHodgeSemantics
#check UniversalDualResidualSourceBirth
#check everyHodgeClassIsRationalAlgebraic_of_universalDualResidualSourceBirth
#check universalDualResidualSourceBirth_iff_hodge

#print axioms dualResidualSourceBirth_iff_surjective
#print axioms everyHodgeClassIsRationalAlgebraic_of_universalDualResidualSourceBirth
#print axioms universalDualResidualSourceBirth_iff_hodge

end GSTUniversalResidualSourceBirth
