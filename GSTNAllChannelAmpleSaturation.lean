import waves.GSTNCohomologyV3

/-!
# GST N-cohomology: constructive integral ample-shift saturation in ALL finite ranks

Original research goal: construct fixed-integral-homology almost-calibrated
currents on EVERY smooth projective complex variety for every rational Hodge
class. This file proves an exact N-channel integer model mechanism relevant to
that goal. It is NOT a theorem constructing geometric currents on arbitrary X.

Unlike the two-channel result, this works for any finite N-shape, any signed
integer coefficient vector, any positive integer ample vector b, and any
nonnegative integer channel masses/periods w.

The explicit budget M=sum_i |a_i| produces nonnegative integer coordinates
c_i=a_i+M*b_i. Its weighted homology period is exactly period(a)+M*period(b)
and nonlinear absolute-multiplicity mass equals its period exactly.
Therefore the constant integer sequence of c has calibration defect zero.

To apply this to a genuine complex projective variety, an independently proved
geometric cycle-class realization must identify EVERY rational Hodge direction
with integer combinations of ACTUAL calibrated holomorphic cycles. That
surjectivity is not assumed or proved here.
-/

set_option maxHeartbeats 10000000
noncomputable section

namespace GSTNAllChannelAmpleSaturation

open GSTNCohomology
open scoped BigOperators

/-- Signed integer N-channel coefficients, with N coming from GST N-shapes. -/
abbrev IntegerChannels (s : NShape) := Fin s.holes → ℤ

/-- Explicit single ample-shift budget, valid for arbitrary finite N. -/
def shiftBudget (s : NShape) (a : IntegerChannels s) : ℤ :=
  ∑ i : Fin s.holes, |a i|

/-- Shift along any strictly positive integer channel-vector b. -/
def shiftedChannels (s : NShape) (a b : IntegerChannels s) :
    IntegerChannels s :=
  fun i => a i + shiftBudget s a * b i

theorem shiftBudget_nonnegative (s : NShape) (a : IntegerChannels s) :
    0 ≤ shiftBudget s a := by
  unfold shiftBudget
  exact Finset.sum_nonneg (fun i hi => abs_nonneg (a i))

theorem shiftBudget_dominates_coordinate
    (s : NShape) (a : IntegerChannels s) (i : Fin s.holes) :
    |a i| ≤ shiftBudget s a := by
  classical
  unfold shiftBudget
  exact Finset.single_le_sum
    (fun j hj => abs_nonneg (a j)) (Finset.mem_univ i)

/-- The constructive ALL-N saturation theorem. There are no existential
witnesses hidden in the proof: shiftedChannels is an explicit formula. -/
theorem shiftedChannels_nonnegative
    (s : NShape) (a b : IntegerChannels s)
    (hb : ∀ i, 1 ≤ b i) :
    ∀ i, 0 ≤ shiftedChannels s a b i := by
  intro i
  have hs := shiftBudget_dominates_coordinate s a i
  have hm := shiftBudget_nonnegative s a
  have hb_i := hb i
  have habs : -|a i| ≤ a i := neg_abs_le (a i)
  unfold shiftedChannels
  nlinarith [mul_nonneg hm (show 0 ≤ b i - 1 by omega)]

/-- Weighted integer homology period in an abstract N-channel lattice. -/
def period (s : NShape) (w a : IntegerChannels s) : ℤ :=
  ∑ i : Fin s.holes, w i * a i

/-- Nonnegative but NONLINEAR multiplicity mass. -/
def currentMass (s : NShape) (w a : IntegerChannels s) : ℤ :=
  ∑ i : Fin s.holes, w i * |a i|

def calibrationDefect (s : NShape) (w a : IntegerChannels s) : ℤ :=
  currentMass s w a - period s w a

theorem period_shifted
    (s : NShape) (w a b : IntegerChannels s) :
    period s w (shiftedChannels s a b) =
      period s w a + shiftBudget s a * period s w b := by
  unfold period shiftedChannels
  calc
    (∑ i : Fin s.holes, w i * (a i + shiftBudget s a * b i)) =
      (∑ i : Fin s.holes, w i * a i) +
        (∑ i : Fin s.holes, shiftBudget s a * (w i * b i)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = (∑ i : Fin s.holes, w i * a i) +
        shiftBudget s a * (∑ i : Fin s.holes, w i * b i) := by
      rw [Finset.mul_sum]

theorem mass_shifted_eq_period
    (s : NShape) (w a b : IntegerChannels s)
    (hb : ∀ i, 1 ≤ b i) :
    currentMass s w (shiftedChannels s a b) =
      period s w (shiftedChannels s a b) := by
  unfold currentMass period
  apply Finset.sum_congr rfl
  intro i hi
  rw [abs_of_nonneg (shiftedChannels_nonnegative s a b hb i)]

theorem shifted_zero_defect
    (s : NShape) (w a b : IntegerChannels s)
    (hb : ∀ i, 1 ≤ b i) :
    calibrationDefect s w (shiftedChannels s a b) = 0 := by
  unfold calibrationDefect
  rw [mass_shifted_eq_period s w a b hb]
  exact sub_self _

/-- A *single fixed shifted integer homology period* at every sequence
index, with absolute (not normalized) calibration defect exactly zero,
in the all-N integer-channel model. -/
def integerCalibratedSequence
    (s : NShape) (a b : IntegerChannels s) : ℕ → IntegerChannels s :=
  fun _ => shiftedChannels s a b

theorem all_N_integral_fixed_period_calibrated_sequence
    (s : NShape) (w a b : IntegerChannels s)
    (hb : ∀ i, 1 ≤ b i) :
    (∀ k : ℕ,
      period s w (integerCalibratedSequence s a b k) =
        period s w a + shiftBudget s a * period s w b) ∧
    (∀ k : ℕ,
      calibrationDefect s w (integerCalibratedSequence s a b k) = 0) := by
  constructor
  · intro k
    exact period_shifted s w a b
  · intro k
    exact shifted_zero_defect s w a b hb

#check all_N_integral_fixed_period_calibrated_sequence
#print axioms all_N_integral_fixed_period_calibrated_sequence


/-! ## Exact positivity-cone semantics for ALL N-window channels

The construction above only supplied a sufficient positive ample shift.
These results prove NECESSITY as well: whenever every channel has
strictly positive integer mass weight, abstract zero calibration defect
is equivalent to coordinatewise nonnegativity. This is a complete
integer-effective cone, not a claim that X has a realized algebraic
cycle for every coordinate direction.
-/

/-- A canonical expression of N-channel defect as a sum of weighted
negative-part penalties, valid WITHOUT sign assumptions. -/
theorem defect_as_weighted_negative_part
    (s : NShape) (w a : IntegerChannels s) :
    calibrationDefect s w a =
      ∑ i : Fin s.holes, w i * (|a i| - a i) := by
  unfold calibrationDefect currentMass period
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- For arbitrary nonnegative integer weights, the N-channel
nonlinear defect is globally nonnegative, just like actual
Kähler calibration defect (but only inside this coordinate model). -/
theorem defect_nonnegative
    (s : NShape) (w a : IntegerChannels s)
    (hw : ∀ i, 0 ≤ w i) :
    0 ≤ calibrationDefect s w a := by
  rw [defect_as_weighted_negative_part]
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (hw i) (sub_nonneg.mpr (le_abs_self (a i)))

/-- Exact all-N classification of zero-defect integer packets:
under strictly positive weights there are no hidden signed
calibrated directions, and the earlier ample shift lands in
precisely the entire integral nonnegative cone. -/
theorem defect_zero_iff_all_coordinates_nonnegative
    (s : NShape) (w a : IntegerChannels s)
    (hw : ∀ i, 1 ≤ w i) :
    calibrationDefect s w a = 0 ↔
      ∀ i : Fin s.holes, 0 ≤ a i := by
  constructor
  · intro hz i
    by_contra hnot
    have hneg : a i < 0 := lt_of_not_ge hnot
    have hweights : ∀ j ∈ Finset.univ,
        0 ≤ w j * (|a j| - a j) := by
      intro j hj
      exact mul_nonneg (by have h := hw j; omega)
        (sub_nonneg.mpr (le_abs_self (a j)))
    have hpositive : 0 < w i * (|a i| - a i) := by
      have hwi : 0 < w i := by have h := hw i; omega
      have hai : 0 < |a i| - a i := by
        rw [abs_of_neg hneg]
        omega
      exact mul_pos hwi hai
    have hle :
        w i * (|a i| - a i) ≤
          ∑ j : Fin s.holes, w j * (|a j| - a j) :=
      Finset.single_le_sum
        (fun j hj => hweights j (Finset.mem_univ j))
        (Finset.mem_univ i)
    rw [defect_as_weighted_negative_part] at hz
    omega
  · intro ha
    rw [defect_as_weighted_negative_part]
    apply Finset.sum_eq_zero
    intro i hi
    rw [abs_of_nonneg (ha i)]
    ring

/-- The earlier explicit GST ample-shift operation is now a
constructive witness for the complete zero-defect cone. -/
theorem shifted_lands_in_complete_zero_defect_cone
    (s : NShape) (w a b : IntegerChannels s)
    (hw : ∀ i, 1 ≤ w i)
    (hb : ∀ i, 1 ≤ b i) :
    calibrationDefect s w (shiftedChannels s a b) = 0 ∧
      (∀ i : Fin s.holes, 0 ≤ shiftedChannels s a b i) := by
  have h := shiftedChannels_nonnegative s a b hb
  exact ⟨(defect_zero_iff_all_coordinates_nonnegative s w
    (shiftedChannels s a b) hw).2 h, h⟩

#check defect_zero_iff_all_coordinates_nonnegative
#print axioms defect_zero_iff_all_coordinates_nonnegative



/-! ## Sharp GST N-window ample shift: the LEAST integral coefficient

Previous ample-shift budget was sum_i |a_i|, which may grossly
overshoot the integer effective cone. The new law uses the LEAST
nonnegative integer shift, not merely any sufficient one. No Hodge
surjectivity or imaginary geometric cycle is introduced.
-/

/-- An actual candidate integer shift works in every N channel. -/
def IsFeasibleAmpleShift
    (s : NShape) (a b : IntegerChannels s) (k : ℕ) : Prop :=
  ∀ i : Fin s.holes, 0 ≤ a i + (k : ℤ) * b i

theorem feasible_ample_shift_exists
    (s : NShape) (a b : IntegerChannels s)
    (hb : ∀ i, 1 ≤ b i) :
    ∃ k : ℕ, IsFeasibleAmpleShift s a b k := by
  have hbudget := shiftBudget_nonnegative s a
  refine ⟨(shiftBudget s a).toNat, ?_⟩
  intro i
  have h := shiftedChannels_nonnegative s a b hb i
  have hcast : (((shiftBudget s a).toNat : ℕ) : ℤ) =
      shiftBudget s a := by omega
  change 0 ≤ a i + (((shiftBudget s a).toNat : ℕ) : ℤ) * b i
  rw [hcast]
  exact h

/-- Exact minimal integer ample shift over ALL feasible natural shifts. -/
noncomputable def leastAmpleShift
    (s : NShape) (a b : IntegerChannels s)
    (hb : ∀ i, 1 ≤ b i) : ℕ :=
  Nat.find (feasible_ample_shift_exists s a b hb)

theorem leastAmpleShift_feasible
    (s : NShape) (a b : IntegerChannels s)
    (hb : ∀ i, 1 ≤ b i) :
    IsFeasibleAmpleShift s a b (leastAmpleShift s a b hb) :=
  Nat.find_spec (feasible_ample_shift_exists s a b hb)

/-- The new value is OPTIMAL, not merely a large positivity bound. -/
theorem leastAmpleShift_minimal
    (s : NShape) (a b : IntegerChannels s)
    (hb : ∀ i, 1 ≤ b i)
    (k : ℕ) (hk : IsFeasibleAmpleShift s a b k) :
    leastAmpleShift s a b hb ≤ k :=
  Nat.find_min' (feasible_ample_shift_exists s a b hb) hk

/-- At the exact LEAST shift, all nonnegative and all strictly positive
weight choices have zero absolute N-channel calibration defect. -/
theorem leastAmpleShift_calibrates_all_positive_weights
    (s : NShape) (w a b : IntegerChannels s)
    (hw : ∀ i, 1 ≤ w i)
    (hb : ∀ i, 1 ≤ b i) :
    calibrationDefect s w
      (fun i => a i + ((leastAmpleShift s a b hb : ℕ) : ℤ) * b i) = 0 := by
  apply (defect_zero_iff_all_coordinates_nonnegative s w _ hw).2
  exact leastAmpleShift_feasible s a b hb

/-- Strong necessity: EVERY zero-defect positive-weight integer shift
must be at least this sharp minimum. -/
theorem leastAmpleShift_optimal_for_zero_defect
    (s : NShape) (w a b : IntegerChannels s)
    (hw : ∀ i, 1 ≤ w i)
    (hb : ∀ i, 1 ≤ b i)
    (k : ℕ)
    (hk : calibrationDefect s w (fun i => a i + (k : ℤ) * b i) = 0) :
    leastAmpleShift s a b hb ≤ k := by
  apply leastAmpleShift_minimal s a b hb k
  exact (defect_zero_iff_all_coordinates_nonnegative s w _ hw).1 hk

#check leastAmpleShift_calibrates_all_positive_weights
#check leastAmpleShift_optimal_for_zero_defect
#print axioms leastAmpleShift_optimal_for_zero_defect

end GSTNAllChannelAmpleSaturation
