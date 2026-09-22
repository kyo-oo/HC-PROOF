import Mathlib
import waves.GSTWaveCohomology

/-!
# GST WORLD COSMOLOGY — dimension-free native carrier

This layer removes the fixed twelve-cell ceiling from the wave geometry.
The old world `carry < 4, digit < 3` is retained as one chart, but the
native carrier is now an arbitrary rectangular GST world.

No geometric interpretation is assumed.  The laws below are internal:
axis transport, transport composition, axis commutation, boundary
extinction, and the exact embedding of the original twelve-cell chart.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

namespace GSTWorldCosmology

open GSTWaveCohomology

/-- A native GST world with arbitrary carry-depth and digit-depth. -/
abbrev WorldCell (carryDepth digitDepth : Nat) : Type :=
  Fin carryDepth × Fin digitDepth

/-- Integer amplitudes on a native GST world. -/
abbrev WorldCoef (carryDepth digitDepth : Nat) : Type :=
  WorldCell carryDepth digitDepth → ℤ

/-- Native digit-axis transport by `n` layers.  No truncation constant is
built into the operator: the active world supplies the boundary. -/
def digitShiftN {carryDepth digitDepth : Nat} (n : Nat)
    (g : WorldCoef carryDepth digitDepth) :
    WorldCoef carryDepth digitDepth :=
  fun c =>
    if h : n ≤ c.2.1 then
      g (c.1, ⟨c.2.1 - n, by omega⟩)
    else 0

/-- Native carry-axis transport by `n` layers. -/
def carryShiftN {carryDepth digitDepth : Nat} (n : Nat)
    (g : WorldCoef carryDepth digitDepth) :
    WorldCoef carryDepth digitDepth :=
  fun c =>
    if h : n ≤ c.1.1 then
      g (⟨c.1.1 - n, by omega⟩, c.2)
    else 0

/-- Zero transport is the identity on every GST world. -/
theorem digitShiftN_zero {carryDepth digitDepth : Nat}
    (g : WorldCoef carryDepth digitDepth) :
    digitShiftN 0 g = g := by
  funext c
  simp [digitShiftN]

/-- Zero carry transport is the identity on every GST world. -/
theorem carryShiftN_zero {carryDepth digitDepth : Nat}
    (g : WorldCoef carryDepth digitDepth) :
    carryShiftN 0 g = g := by
  funext c
  simp [carryShiftN]

/-- Digit transport composes additively: traversing `m` layers and then
`n` layers is exactly one traversal of `m+n` layers. -/
theorem digitShiftN_add {carryDepth digitDepth : Nat}
    (m n : Nat) (g : WorldCoef carryDepth digitDepth) :
    digitShiftN m (digitShiftN n g) = digitShiftN (m + n) g := by
  funext c
  by_cases hmn : m + n ≤ c.2.1
  · have hm : m ≤ c.2.1 := by omega
    have hn : n ≤ c.2.1 - m := by omega
    simp [digitShiftN, hm, hn, hmn, Nat.sub_sub]
  · by_cases hm : m ≤ c.2.1
    · have hn : ¬ n ≤ c.2.1 - m := by omega
      simp [digitShiftN, hm, hn, hmn]
    · simp [digitShiftN, hm, hmn]

/-- Carry transport composes additively. -/
theorem carryShiftN_add {carryDepth digitDepth : Nat}
    (m n : Nat) (g : WorldCoef carryDepth digitDepth) :
    carryShiftN m (carryShiftN n g) = carryShiftN (m + n) g := by
  funext c
  by_cases hmn : m + n ≤ c.1.1
  · have hm : m ≤ c.1.1 := by omega
    have hn : n ≤ c.1.1 - m := by omega
    simp [carryShiftN, hm, hn, hmn, Nat.sub_sub]
  · by_cases hm : m ≤ c.1.1
    · have hn : ¬ n ≤ c.1.1 - m := by omega
      simp [carryShiftN, hm, hn, hmn]
    · simp [carryShiftN, hm, hmn]

/-- **THE NATIVE RECTANGLE LAW.**  Carry transport and digit transport
commute at every depth in every rectangular GST world.  The old
twelve-cell cup commutation is therefore one finite chart of a
dimension-free law. -/
theorem axes_commute {carryDepth digitDepth : Nat}
    (m n : Nat) (g : WorldCoef carryDepth digitDepth) :
    digitShiftN n (carryShiftN m g) =
      carryShiftN m (digitShiftN n g) := by
  funext c
  by_cases hm : m ≤ c.1.1 <;>
    by_cases hn : n ≤ c.2.1 <;>
      simp [digitShiftN, carryShiftN, hm, hn]

/-- The digit axis extinguishes exactly at the world depth. -/
theorem digit_boundary_extinction {carryDepth digitDepth : Nat}
    (g : WorldCoef carryDepth digitDepth) :
    digitShiftN digitDepth g = fun _ => 0 := by
  funext c
  have h : ¬ digitDepth ≤ c.2.1 := by omega
  simp [digitShiftN, h]

/-- The carry axis extinguishes exactly at the world depth. -/
theorem carry_boundary_extinction {carryDepth digitDepth : Nat}
    (g : WorldCoef carryDepth digitDepth) :
    carryShiftN carryDepth g = fun _ => 0 := by
  funext c
  have h : ¬ carryDepth ≤ c.1.1 := by omega
  simp [carryShiftN, h]

/-- Any transport which crosses either world boundary is annihilated.
This is the mixed extinction law of the native rectangle. -/
theorem mixed_boundary_extinction {carryDepth digitDepth m n : Nat}
    (g : WorldCoef carryDepth digitDepth)
    (h : carryDepth ≤ m ∨ digitDepth ≤ n) :
    digitShiftN n (carryShiftN m g) = fun _ => 0 := by
  funext c
  rcases h with hm | hn
  · have hcm : ¬ m ≤ c.1.1 := by omega
    by_cases hd : n ≤ c.2.1
    · simp [digitShiftN, carryShiftN, hd, hcm]
    · simp [digitShiftN, hd]
  · have hdn : ¬ n ≤ c.2.1 := by omega
    simp [digitShiftN, hdn]

/-! ## The old twelve-cell world as one exact chart -/

/-- Embed an original twelve-cell wave cell into the native `4 × 3` world. -/
def waveToWorld (c : WaveCell) : WorldCell 4 3 :=
  (⟨c.carry, c.hcarry⟩, ⟨c.digit, c.hdigit⟩)

/-- Read a native `4 × 3` world cell back as an original wave cell. -/
def worldToWave (c : WorldCell 4 3) : WaveCell :=
  ⟨c.1.1, c.2.1, c.1.2, c.2.2⟩

/-- The two cell presentations are exactly inverse. -/
theorem worldToWave_waveToWorld (c : WaveCell) :
    worldToWave (waveToWorld c) = c := by
  cases c
  rfl

/-- The inverse direction of the chart identity. -/
theorem waveToWorld_worldToWave (c : WorldCell 4 3) :
    waveToWorld (worldToWave c) = c := by
  rcases c with ⟨C, d⟩
  rfl

/-- The old twelve-cell carrier is exactly one native `4 × 3` chart. -/
def waveWorldEquiv : WaveCell ≃ WorldCell 4 3 where
  toFun := waveToWorld
  invFun := worldToWave
  left_inv := worldToWave_waveToWorld
  right_inv := waveToWorld_worldToWave

/-- Export an old wave coefficient into the native `4 × 3` chart. -/
def liftWave (f : WaveCoef) : WorldCoef 4 3 :=
  fun c => f (worldToWave c)

/-- Import a native `4 × 3` coefficient into the old wave chart. -/
def lowerWave (f : WorldCoef 4 3) : WaveCoef :=
  fun c => f (waveToWorld c)

/-- Coefficient transport from the old chart into the native world loses
no information. -/
theorem lowerWave_liftWave (f : WaveCoef) :
    lowerWave (liftWave f) = f := by
  funext c
  simp [lowerWave, liftWave, worldToWave_waveToWorld]

/-- Coefficient transport back into the old chart also loses no information. -/
theorem liftWave_lowerWave (f : WorldCoef 4 3) :
    liftWave (lowerWave f) = f := by
  funext c
  simp [lowerWave, liftWave, waveToWorld_worldToWave]

/-- **THE FIRST COSMOLOGY UPGRADE.**  The original twelve-cell universe is
not a terminal geometry: it is an exact finite chart inside the
dimension-free GST world family, while the native axis laws are valid at
arbitrary carry-depth and digit-depth. -/
theorem twelve_cell_is_native_chart :
    Function.Bijective waveToWorld
    ∧ (∀ (carryDepth digitDepth : Nat)
        (g : WorldCoef carryDepth digitDepth),
        digitShiftN digitDepth g = fun _ => 0)
    ∧ (∀ (carryDepth digitDepth : Nat)
        (g : WorldCoef carryDepth digitDepth),
        carryShiftN carryDepth g = fun _ => 0)
    ∧ (∀ (carryDepth digitDepth m n : Nat)
        (g : WorldCoef carryDepth digitDepth),
        digitShiftN n (carryShiftN m g) =
          carryShiftN m (digitShiftN n g)) := by
  refine ⟨waveWorldEquiv.bijective, ?_, ?_, ?_⟩
  · intro carryDepth digitDepth g
    exact digit_boundary_extinction g
  · intro carryDepth digitDepth g
    exact carry_boundary_extinction g
  · intro carryDepth digitDepth m n g
    exact axes_commute m n g

#check digitShiftN
#check carryShiftN
#check digitShiftN_add
#check carryShiftN_add
#check axes_commute
#check digit_boundary_extinction
#check carry_boundary_extinction
#check mixed_boundary_extinction
#check waveWorldEquiv
#check lowerWave_liftWave
#check liftWave_lowerWave
#check twelve_cell_is_native_chart

#print axioms digitShiftN_add
#print axioms carryShiftN_add
#print axioms axes_commute
#print axioms digit_boundary_extinction
#print axioms carry_boundary_extinction
#print axioms mixed_boundary_extinction
#print axioms twelve_cell_is_native_chart

end GSTWorldCosmology
