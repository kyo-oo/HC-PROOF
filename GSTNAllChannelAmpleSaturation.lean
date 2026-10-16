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

end GSTNAllChannelAmpleSaturation
