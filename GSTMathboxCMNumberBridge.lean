import GSTClassicalHodgeSingleCorrespondenceRankTwo
import Mathlib

/-!
# Mathbox GST / CM number bridge: image proposal 2026-10-14

Formal and adversarial translation of three photographed candidate laws.

E1: 99*x*sqrt(((ax^4)_3-(by^4)_3)/(psi^2*xi_7)).
The indexed terms have not been defined; we treat them as symbolic A,B.
The radical is not by itself a nonvanishing or actual-cycle theorem.

E2: a proposed nonvanishing of the difference of two operator actions.
A nonzero CM determinant on a *model plane* does NOT imply geometric
transversality of the actual realized operator on an arbitrary Hodge fiber.

E3: an infinite sum with an index-independent denominator is not a
convergent zeta kernel. We prove its precise finite partial-sum identity.

The successful conditional result below upgrades the user's CM insight:
if a *genuinely realized* closed correspondence acts on a rank-two Hodge
fiber with a certified nonzero "imaginary" transverse coordinate b, the
existing weight-local GST charge-wedge gives an ACTUAL rational algebraic
cycle for every rational Hodge class in that fiber.

No unchecked mapping of CM to scheme geometry is assumed. The required
coordinate bridge to a realized correspondence is displayed as an input.
-/

set_option maxHeartbeats 20000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeLimitlessSpinePropagation
open GSTClassicalHodgeRealizedCorrespondenceExpressionAlgebra
open GSTClassicalHodgeSingleCorrespondenceRankTwo

namespace GSTMathboxCMNumberBridge

/-- Rational squared radicand of the image's E1. A and B stand for
currently UNDEFINED subscripted symbolic quantities. -/
def conversionRadicand (A B psi xi : ℚ) : ℚ :=
  (A - B) / (psi ^ 2 * xi)

/-- The radicand is nonzero when (and only when, under nonzero
denominator) its two independent symbolic inputs differ. -/
theorem conversionRadicand_ne_zero
    (A B psi xi : ℚ)
    (hAB : A ≠ B) (hpsi : psi ≠ 0) (hxi : xi ≠ 0) :
    conversionRadicand A B psi xi ≠ 0 := by
  unfold conversionRadicand
  apply div_ne_zero
  · exact sub_ne_zero.mpr hAB
  · exact mul_ne_zero (pow_ne_zero 2 hpsi) hxi

/-- E1 can certainly vanish for admissible nonzero denominator inputs:
a zero radical numerator gives zero regardless of the factor 99*x. -/
theorem conversionRadicand_equal_inputs
    (A psi xi : ℚ) :
    conversionRadicand A A psi xi = 0 := by
  simp [conversionRadicand]

/-- CM multiplication on a rational Gaussian-coordinate plane:
(a + i*b) acts via the real matrix [[a,-b],[b,a]]. -/
def cmActionMatrix (a b : ℚ) : Matrix (Fin 2) (Fin 2) ℚ :=
  !![a, -b; b, a]

/-- The CM matrix has squared norm determinant a^2+b^2. -/
theorem cmActionMatrix_det (a b : ℚ) :
    (cmActionMatrix a b).det = a ^ 2 + b ^ 2 := by
  simp [cmActionMatrix, Matrix.det_fin_two]
  ring

/-- Its action on the reference spine (1,0) is the coordinate pair (a,b). -/
theorem cmActionMatrix_seed (a b : ℚ) :
    (cmActionMatrix a b).mulVec (![1, 0] : Fin 2 → ℚ) =
      (![a, b] : Fin 2 → ℚ) := by
  funext i
  fin_cases i <;> simp [cmActionMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The charge-wedge of the standard CM-plane seed has imaginary coordinate
b. This is the component that genuinely controls transversality. -/
def cmChargedWedge (a b : ℚ) : Fin 2 → ℚ :=
  let seed := (![1, 0] : Fin 2 → ℚ)
  let image := (![a, b] : Fin 2 → ℚ)
  image - a • seed

theorem cmChargedWedge_eq (a b : ℚ) :
    cmChargedWedge a b = (![0, b] : Fin 2 → ℚ) := by
  funext i
  fin_cases i <;> simp [cmChargedWedge, Pi.sub_apply, Pi.smul_apply] <;> ring

/-- The CM-model charge wedge vanishes for purely real multiplication,
even when its CM norm determinant is NONZERO. -/
theorem cm_norm_nonzero_without_transverse :
    (cmActionMatrix (1 : ℚ) 0).det ≠ 0 ∧
      cmChargedWedge 1 0 = 0 := by
  constructor
  · rw [cmActionMatrix_det]
    norm_num
  · rw [cmChargedWedge_eq]
    ext i
    fin_cases i <;> simp

/-- A verified nonzero imaginary coordinate gives a nonzero CM-plane wedge. -/
theorem cmChargedWedge_ne_zero_of_imag_ne_zero
    (a b : ℚ) (hb : b ≠ 0) :
    cmChargedWedge a b ≠ 0 := by
  intro hz
  have hcoord := congrArg (fun v : Fin 2 → ℚ => v 1) hz
  rw [cmChargedWedge_eq] at hcoord
  exact hb (by simpa using hcoord)

/-- E3 as printed has no dependence on its summation index. The finite
partial sum is therefore N times the summand. This is an exact obstruction
to treating the displayed expression as a convergent ordinary infinite sum. -/
theorem constantKernelPartialSum (c : ℚ) (N : ℕ) :
    (∑ _n ∈ Finset.range N, c) = (N : ℚ) * c := by
  induction N with
  | zero => simp
  | succ N ih =>
    simp only [Finset.sum_range_succ, ih, Nat.cast_succ]
    ring

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Decisive geometric bridge to a CM transverse direction. The *target*
functional picks out a geometric coordinate orthogonal to the native spine.
A genuine realized correspondence E must be proved to have coordinate b ≠ 0.
Only then is its Betti image not proportional to the native spine. -/
theorem geometric_nonproportional_of_verified_CM_coordinate
    (G : GeometricCycleClassSpine V H)
    (E : RealizedCorrespondenceExpr V H p)
    (imagRead : ClassicalHodgeFiber V H p →ₗ[ℚ] ℚ)
    (hseed : imagRead (spineHodgeSeed G p) = 0)
    (b : ℚ)
    (hb : b ≠ 0)
    (hCM : imagRead (movedSpine G E) = b) :
    ∀ c : ℚ, movedSpine G E ≠ c • spineHodgeSeed G p := by
  intro c hc
  have hzero : imagRead (movedSpine G E) = 0 := by
    rw [hc, map_smul, hseed, smul_zero]
  exact hb (hCM.symm.trans hzero)

/-- Conditional GST+CM bridge to the literal rank-two rational Hodge-cycle
conclusion. Nontriviality is not obtained merely from a formal CM norm;
a *geometric* CM transverse coordinate and an actually realized
correspondence are explicitly required. -/
theorem rank_two_hodge_cycle_of_verified_CM_geometry
    (G : GeometricCycleClassSpine V H)
    [FiniteDimensional ℚ (ClassicalHodgeFiber V H p)]
    (ell : ClassicalHodgeFiber V H p →ₗ[ℚ] ℚ)
    (hlive : ell (spineHodgeSeed G p) ≠ 0)
    (E : RealizedCorrespondenceExpr V H p)
    (imagRead : ClassicalHodgeFiber V H p →ₗ[ℚ] ℚ)
    (hseed : imagRead (spineHodgeSeed G p) = 0)
    (b : ℚ)
    (hb : b ≠ 0)
    (hCM : imagRead (movedSpine G E) = b)
    (hrank : Module.finrank ℚ (ClassicalHodgeFiber V H p) = 2)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p)) :
    ∃ Z : codimensionCycles V.X p, H.cycleClass p Z = alpha :=
  every_rank_two_hodge_class_of_nonproportional_geometric_action
    G ell hlive E
    (geometric_nonproportional_of_verified_CM_coordinate G E imagRead hseed b hb hCM)
    hrank alpha halpha

#check conversionRadicand_ne_zero
#check cmActionMatrix_det
#check cmActionMatrix_seed
#check cmChargedWedge_eq
#check cm_norm_nonzero_without_transverse
#check cmChargedWedge_ne_zero_of_imag_ne_zero
#check constantKernelPartialSum
#check geometric_nonproportional_of_verified_CM_coordinate
#check rank_two_hodge_cycle_of_verified_CM_geometry

#print axioms cmActionMatrix_det
#print axioms cm_norm_nonzero_without_transverse
#print axioms constantKernelPartialSum
#print axioms rank_two_hodge_cycle_of_verified_CM_geometry

end GSTMathboxCMNumberBridge
