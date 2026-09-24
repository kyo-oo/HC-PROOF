import GSTLimitlessWorld
import GSTWorldCosmology

/-!
# GST LIMITLESS WORLD — compiler contract

This module pins the public interface of the unbounded algebraic cosmos and
its exact relationship with every finite GST observation window.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

namespace GSTLimitlessWorldTest

open GSTLimitlessWorld
open GSTWorldCosmology

#check CosmicCell
#check CosmicCoef
#check cosmicDigitShiftN
#check cosmicCarryShiftN
#check cosmic_digitShiftN_zero
#check cosmic_carryShiftN_zero
#check cosmic_digitShiftN_add
#check cosmic_carryShiftN_add
#check cosmic_axes_commute
#check extendWorld
#check restrictWorld
#check restrictWorld_extendWorld
#check restrict_cosmicDigitShift_extend
#check restrict_cosmicCarryShift_extend
#check twelve_cell_limitless_embedding

/-- A coordinate genuinely outside the historical `4 × 3` chart exists in
the limitless carrier without changing the ambient type. -/
def beyondHistoricalCell : CosmicCell := (37, 41)

example : beyondHistoricalCell = (37, 41) := rfl

/-- Arbitrary-depth transport is a single global operation, not a change of
finite ambient rectangle. -/
example (f : CosmicCoef) :
    cosmicDigitShiftN 1000 (cosmicCarryShiftN 2000 f) =
      cosmicCarryShiftN 2000 (cosmicDigitShiftN 1000 f) := by
  exact cosmic_axes_commute 2000 1000 f

/-- Composition remains exact at depths far beyond every historical chart. -/
example (f : CosmicCoef) :
    cosmicDigitShiftN 500 (cosmicDigitShiftN 700 f) =
      cosmicDigitShiftN 1200 f := by
  simpa using cosmic_digitShiftN_add 500 700 f

/-- Finite digit transport is exactly the visible part of global transport. -/
example {A B : Nat} (n : Nat) (g : WorldCoef A B) :
    restrictWorld A B (cosmicDigitShiftN n (extendWorld g)) = digitShiftN n g := by
  exact restrict_cosmicDigitShift_extend n g

/-- Finite carry transport is exactly the visible part of global transport. -/
example {A B : Nat} (n : Nat) (g : WorldCoef A B) :
    restrictWorld A B (cosmicCarryShiftN n (extendWorld g)) = carryShiftN n g := by
  exact restrict_cosmicCarryShift_extend n g

#print axioms cosmic_digitShiftN_add
#print axioms cosmic_carryShiftN_add
#print axioms cosmic_axes_commute
#print axioms restrictWorld_extendWorld
#print axioms restrict_cosmicDigitShift_extend
#print axioms restrict_cosmicCarryShift_extend
#print axioms twelve_cell_limitless_embedding

end GSTLimitlessWorldTest
