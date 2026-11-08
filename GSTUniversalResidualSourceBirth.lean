import Mathlib.LinearAlgebra.Dual.Lemmas
import GSTClassicalHodgeGeometricCycleClassSpine
import GSTClassicalHodgeExactClayStatement

/-!
# GST UNIVERSAL RESIDUAL SOURCE-BIRTH — THE SINGLE CONDITIONAL HODGE TARGET

The cycle-class image is a subspace of the rational Hodge fiber. A positive
perfect pairing identifies that fiber with its dual. The one remaining
source-generation law is:

  every nonzero Hodge residual pairs nontrivially with at least one actual
  native algebraic cycle.

This module proves that this law is EXACTLY equivalent to surjectivity of the
cycle-class map, hence to the Stage-2G elementwise Hodge target, once the
finite-dimensional polarized Hodge semantics are supplied.

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

/-- A rational positive-definite pairing, recorded by its perfect map to the
linear dual. Positivity is the Hodge-Riemann input; the perfect map is the
nondegeneracy needed for the source-detection theorem. -/
structure PositivePerfectPairing
    (W : Type*) [AddCommGroup W] [Module ℚ W] where
  toDual : W ≃ₗ[ℚ] (W →ₗ[ℚ] ℚ)
  symmetric : ∀ x y : W, toDual x y = toDual y x
  positive : ∀ x : W, x ≠ 0 → 0 < toDual x x

/-- Universal residual source-birth: every nonzero vector is detected by an
actual vector in the image of the native cycle-class map. -/
def ResidualSourceBirth
    {N W : Type*}
    [AddCommGroup N] [Module ℚ N]
    [AddCommGroup W] [Module ℚ W]
    (P : PositivePerfectPairing W)
    (cl : N →ₗ[ℚ] W) : Prop :=
  ∀ r : W, r ≠ 0 → ∃ z : N, P.toDual r (cl z) ≠ 0

/-- The residual source-birth law is equivalent to surjectivity of the
native cycle-class map. The forward implication is the dual-map theorem:
if every nonzero functional is detected on a cycle, the transpose map is
injective; finite-dimensionality of the Hodge fiber then forces the original
map to be surjective. -/
theorem residualSourceBirth_iff_surjective
    {N W : Type*}
    [AddCommGroup N] [Module ℚ N]
    [AddCommGroup W] [Module ℚ W]
    [FiniteDimensional ℚ W]
    (P : PositivePerfectPairing W)
    (cl : N →ₗ[ℚ] W) :
    ResidualSourceBirth P cl ↔ Function.Surjective cl := by
  constructor
  · intro hBirth
    apply (LinearMap.dualMap_injective_iff).mp
    intro φ ψ hEq
    by_contra hne
    let r : W := P.toDual.symm (φ - ψ)
    have hr : r ≠ 0 := by
      intro hr0
      apply hne
      have hdiff : φ - ψ = 0 := by
        calc
          φ - ψ = P.toDual r := by simp [r]
          _ = 0 := by simp [hr0]
      exact sub_eq_zero.mp hdiff
    obtain ⟨z, hz⟩ := hBirth r hr
    have hEval : φ (cl z) = ψ (cl z) := by
      have hpoint := congrFun hEq z
      simpa only [LinearMap.dualMap_apply', LinearMap.comp_apply] using hpoint
    have hzero : P.toDual r (cl z) = 0 := by
      rw [show P.toDual r = φ - ψ by simp [r]]
      simp [hEval]
    exact hz hzero
  · intro hsurj r hr
    by_contra hNo
    have hzero : ∀ z : N, P.toDual r (cl z) = 0 := by
      intro z
      by_contra hne
      exact hNo ⟨z, hne⟩
    have hdualzero : P.toDual r = 0 := by
      ext w
      rcases hsurj w with ⟨z, rfl⟩
      exact hzero z
    have hr0 : r = 0 := P.toDual.injective (by simpa using hdualzero)
    exact hr hr0

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

/-- The finite-dimensional, positively polarized Hodge semantics needed to
turn residual detection into surjectivity. These are structural properties
of the genuine projective Hodge fiber, not the remaining source-generation
claim. -/
structure PolarizedHodgeSemantics
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) where
  finiteDimensional :
    ∀ p : Nat,
      FiniteDimensional ℚ (rationalHodgeSubspace (H.hodgeBigrading p))
  pairing :
    ∀ p : Nat,
      PositivePerfectPairing (rationalHodgeSubspace (H.hodgeBigrading p))

/-- The one GST target, simultaneously for every codimension: every nonzero
Hodge residual has nonzero polarized coupling with some actual native
codimension-p algebraic cycle. -/
def UniversalResidualSourceBirth
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (G : GeometricCycleClassSpine V H)
    (S : PolarizedHodgeSemantics V H) : Prop :=
  ∀ p : Nat,
    ResidualSourceBirth (S.pairing p) (hodgeCycleClassMap G p)

/-- CONDITIONAL HODGE THEOREM: the single universal residual source-birth law
forces every rational (p,p) class to have a native algebraic cycle
representative. -/
theorem everyHodgeClassIsRationalAlgebraic_of_universalResidualSourceBirth
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (G : GeometricCycleClassSpine V H)
    (S : PolarizedHodgeSemantics V H)
    (hBirth : UniversalResidualSourceBirth G S) :
    EveryHodgeClassIsRationalAlgebraic H := by
  intro p alpha halpha
  letI := S.finiteDimensional p
  have hsurj :
      Function.Surjective (hodgeCycleClassMap G p) :=
    (residualSourceBirth_iff_surjective
      (S.pairing p) (hodgeCycleClassMap G p)).mp (hBirth p)
  let target : rationalHodgeSubspace (H.hodgeBigrading p) :=
    ⟨alpha, halpha⟩
  obtain ⟨Z, hZ⟩ := hsurj target
  exact ⟨Z, congrArg Subtype.val hZ⟩

/-- Exactness of the reduction: under the same polarized semantics, the
universal residual source-birth law is equivalent to the Stage-2G Hodge
conjecture. Thus it is the single remaining mathematical target, not an
easier substitute for the conjecture. -/
theorem universalResidualSourceBirth_iff_hodge
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (G : GeometricCycleClassSpine V H)
    (S : PolarizedHodgeSemantics V H) :
    UniversalResidualSourceBirth G S ↔
      EveryHodgeClassIsRationalAlgebraic H := by
  constructor
  · exact everyHodgeClassIsRationalAlgebraic_of_universalResidualSourceBirth
      G S
  · intro hHodge p r hr
    obtain ⟨Z, hZ⟩ := hHodge p r.1 r.2
    refine ⟨Z, ?_⟩
    have hmap : hodgeCycleClassMap G p Z = r := by
      apply Subtype.ext
      exact hZ
    rw [hmap]
    exact ne_of_gt ((S.pairing p).positive r hr)

#check PositivePerfectPairing
#check ResidualSourceBirth
#check residualSourceBirth_iff_surjective
#check hodgeCycleClassMap
#check PolarizedHodgeSemantics
#check UniversalResidualSourceBirth
#check everyHodgeClassIsRationalAlgebraic_of_universalResidualSourceBirth
#check universalResidualSourceBirth_iff_hodge

#print axioms residualSourceBirth_iff_surjective
#print axioms everyHodgeClassIsRationalAlgebraic_of_universalResidualSourceBirth
#print axioms universalResidualSourceBirth_iff_hodge

end GSTUniversalResidualSourceBirth
