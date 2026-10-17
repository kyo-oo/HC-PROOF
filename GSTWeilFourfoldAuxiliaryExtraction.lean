import Mathlib

/-!
# Exact auxiliary-factor extraction for a Weil fourfold

This file verifies the rational arithmetic in the geometric construction
written in `research/records/20261018-weil-fourfold-auxiliary-extraction.md`.
It does NOT construct abelian varieties, Chow intersections, Betti cycle
classes, or the secant-sheaf cycle on the auxiliary split sixfold.

Those geometric operations and the split-sixfold Weil-plane theorem are
external inputs to the manuscript, not axioms asserted by this file.
In particular, no nonzero geometric cycle is manufactured from coordinates.

The coefficients below represent a tensor in a product of two rational
Weil planes. Its two conjugate determinant summands satisfy the displayed
balance equations. Contraction with Delta - F1 - F2 is injective on this
two-dimensional tensor sector. A second result verifies that the actual
fourth-power character, rather than multiplication by u alone, generates
two independent directions from a nonzero extracted vector.
-/

set_option maxHeartbeats 1000000

namespace GSTWeilFourfoldAuxiliaryExtraction

/-- Coordinates in the ordered divisor list (Gamma_u, F1, F2, Delta). -/
abbrev AuxiliaryDivisor := Fin 4 → ℚ

/-- Intersection numbers for an elliptic curve with u² = -d.
The geometric identification of this formula is external. -/
def auxiliaryIntersection (d : ℚ) (v w : AuxiliaryDivisor) : ℚ :=
  d * (v 0 * w 1 + v 1 * w 0) +
  (v 0 * w 2 + v 2 * w 0) +
  (d + 1) * (v 0 * w 3 + v 3 * w 0) +
  (v 1 * w 2 + v 2 * w 1) +
  (v 1 * w 3 + v 3 * w 1) +
  (v 2 * w 3 + v 3 * w 2)

def graphDifference (i : Fin 4) : ℚ :=
  match i.val with
  | 0 => 0
  | 1 => -1
  | 2 => -1
  | _ => 1

def imaginaryGraphDifference (d : ℚ) (i : Fin 4) : ℚ :=
  match i.val with
  | 0 => 1
  | 1 => -1
  | 2 => -d
  | _ => 0

def firstFiber (i : Fin 4) : ℚ := if i.val = 1 then 1 else 0
def secondFiber (i : Fin 4) : ℚ := if i.val = 2 then 1 else 0

theorem auxiliary_graph_pairings (d : ℚ) :
    auxiliaryIntersection d graphDifference graphDifference = -2 ∧
    auxiliaryIntersection d graphDifference (imaginaryGraphDifference d) = 0 ∧
    auxiliaryIntersection d (imaginaryGraphDifference d)
      (imaginaryGraphDifference d) = -2 * d := by
  refine ⟨?_, ?_, ?_⟩
  <;> norm_num [auxiliaryIntersection, graphDifference, imaginaryGraphDifference]
  <;> ring

theorem graph_difference_kills_product_polarization (d a b : ℚ) :
    auxiliaryIntersection d graphDifference
      (fun i => a * firstFiber i + b * secondFiber i) = 0 := by
  norm_num [auxiliaryIntersection, graphDifference, firstFiber, secondFiber]
  <;> ring

/-- Coefficients in (A0 D0, A0 Du, A1 D0, A1 Du). -/
@[ext] structure TensorCoefficients where
  aa : ℚ
  ab : ℚ
  ba : ℚ
  bb : ℚ

def zeroCoefficients : TensorCoefficients := ⟨0, 0, 0, 0⟩

/-- Equalizer of J_A tensor 1 and 1 tensor J_B, where J² = -d. -/
def balanced (d : ℚ) (v : TensorCoefficients) : Prop :=
  v.ba = v.ab ∧ v.aa = -d * v.bb

def determinantTensor (d x y : ℚ) : TensorCoefficients :=
  ⟨x, y, y, -x / d⟩

def contractGraph (v : TensorCoefficients) : ℚ × ℚ :=
  (-2 * v.aa, -2 * v.ba)

theorem determinant_tensor_balanced (d x y : ℚ) (hd : d ≠ 0) :
    balanced d (determinantTensor d x y) := by
  constructor
  · rfl
  · dsimp [determinantTensor]
    field_simp [hd]

theorem contraction_formula (d x y : ℚ) :
    contractGraph (determinantTensor d x y) = (-2 * x, -2 * y) := rfl

/-- The graph detector loses no nonzero tensor in the Weil sector.
This is a universal rational calculation, not a source-existence theorem. -/
theorem contraction_injective_on_balanced (d : ℚ) (hd : d ≠ 0)
    (v : TensorCoefficients) (hv : balanced d v)
    (hzero : contractGraph v = (0, 0)) : v = zeroCoefficients := by
  have ha := congrArg Prod.fst hzero
  have hb := congrArg Prod.snd hzero
  change -2 * v.aa = 0 at ha
  change -2 * v.ba = 0 at hb
  have haa : v.aa = 0 := by linarith
  have hba : v.ba = 0 := by linarith
  have hab : v.ab = 0 := by rw [← hv.1, hba]
  have hmul : d * v.bb = 0 := by linarith [hv.2]
  have hbb : v.bb = 0 := (mul_eq_zero.mp hmul).resolve_left hd
  exact TensorCoefficients.ext haa hab hba hbb

theorem contraction_nonzero (d : ℚ) (hd : d ≠ 0)
    (v : TensorCoefficients) (hv : balanced d v)
    (hne : v ≠ zeroCoefficients) : contractGraph v ≠ (0, 0) := by
  intro hzero
  exact hne (contraction_injective_on_balanced d hd v hv hzero)

/-- Determinant after padding a (2,2) Hermitian form by (+t,-1/(delta*t)). -/
theorem padded_determinant (delta t : ℚ) (hdelta : delta ≠ 0) (ht : t ≠ 0) :
    delta * t * (-1 / (delta * t)) = -1 := by
  field_simp [hdelta, ht]

def realFourthPower (d m : ℚ) : ℚ := m ^ 4 - 6 * m ^ 2 * d + d ^ 2
def imaginaryFourthPower (d m : ℚ) : ℚ := 4 * m * (m ^ 2 - d)

/-- Matrix of pullback by m+u on the degree-four Weil plane, u²=-d. -/
def fourthPowerAction (d m : ℚ) (v : ℚ × ℚ) : ℚ × ℚ :=
  (realFourthPower d m * v.1 - d * imaginaryFourthPower d m * v.2,
   imaginaryFourthPower d m * v.1 + realFourthPower d m * v.2)

def planeDeterminant (v w : ℚ × ℚ) : ℚ := v.1 * w.2 - v.2 * w.1

theorem fourth_power_orbit_determinant (d m : ℚ) (v : ℚ × ℚ) :
    planeDeterminant v (fourthPowerAction d m v) =
      imaginaryFourthPower d m * (v.1 ^ 2 + d * v.2 ^ 2) := by
  dsimp [planeDeterminant, fourthPowerAction]
  ring

theorem imaginary_fourth_power_positive (d : ℚ) (hd : 0 < d) :
    0 < imaginaryFourthPower d (d + 1) := by
  have hm : 0 < d + 1 := by linarith
  have hq : 0 < (d + 1) ^ 2 - d := by nlinarith [sq_nonneg d]
  dsimp [imaginaryFourthPower]
  positivity

theorem quadratic_norm_positive (d : ℚ) (hd : 0 < d)
    (v : ℚ × ℚ) (hv : v ≠ (0, 0)) : 0 < v.1 ^ 2 + d * v.2 ^ 2 := by
  by_cases hx : v.1 = 0
  · have hy : v.2 ≠ 0 := by
      intro hy
      exact hv (Prod.ext hx hy)
    have hy2 : 0 < v.2 ^ 2 := sq_pos_of_ne_zero hy
    rw [hx]
    nlinarith
  · have hx2 : 0 < v.1 ^ 2 := sq_pos_of_ne_zero hx
    have hy2 : 0 ≤ d * v.2 ^ 2 := mul_nonneg hd.le (sq_nonneg _)
    linarith

/-- A nonzero extracted rational vector and its (d+1+u)-pullback are independent. -/
theorem extracted_fourth_power_orbit_has_rank_two (d : ℚ) (hd : 0 < d)
    (v : ℚ × ℚ) (hv : v ≠ (0, 0)) :
    0 < planeDeterminant v (fourthPowerAction d (d + 1) v) := by
  rw [fourth_power_orbit_determinant]
  exact mul_pos (imaginary_fourth_power_positive d hd)
    (quadratic_norm_positive d hd v hv)

#print axioms auxiliary_graph_pairings
#print axioms graph_difference_kills_product_polarization
#print axioms determinant_tensor_balanced
#print axioms contraction_injective_on_balanced
#print axioms contraction_nonzero
#print axioms padded_determinant
#print axioms fourth_power_orbit_determinant
#print axioms extracted_fourth_power_orbit_has_rank_two

end GSTWeilFourfoldAuxiliaryExtraction
