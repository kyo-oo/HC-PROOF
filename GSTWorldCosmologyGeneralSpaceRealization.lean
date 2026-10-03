import GSTGeneralSpaceRealization
import GSTWorldCosmology

/-!
# GST WORLD COSMOLOGY — General Space realization

The historical `Nat × Nat` limitless carrier is preserved exactly, but now as
one chart/realization of General Space rather than the ontology of General
Space itself.
-/

namespace GSTWorldCosmologyGeneralSpaceRealization

open GSTGeneralSpace
open GSTGeneralSpaceRealization
open GSTWorldCosmology

/-- The old cosmic cell carrier as one concrete preorder-path realization. -/
def cosmicCellSpace : GeneralSpace :=
  ofPreorder CosmicCell

/-- Identity coordinate chart exposing the historical `Nat × Nat` cells. -/
def cosmicCellChart : Chart cosmicCellSpace where
  Coord := CosmicCell
  observe := id

/-- Any completed GST field is a scalar realization of the same General Space
cell ontology. -/
def completedFieldRealization (f : CompletedCosmos) :
    Realization cosmicCellSpace where
  State := ℤ
  realize := f

/-- Finite rectangles remain exact observations of a completed field. -/
def finiteWindowObservation (A B : Nat) (f : CompletedCosmos) :
    WorldCoef A B :=
  observe A B f

/-- All finite observations still separate completed fields.  General Space
changes the ontology, not this exact reconstruction theorem. -/
theorem allFiniteWindows_separate {f g : CompletedCosmos}
    (h : ∀ A B, finiteWindowObservation A B f =
      finiteWindowObservation A B g) :
    f = g := by
  exact observations_separate h

/-- Existing unbounded digit/carry transports remain exact commuting
operations in this chart. -/
theorem old_cosmic_axes_are_one_commuting_chart
    (m n : Nat) (f : CompletedCosmos) :
    cosmicDigitShift n (cosmicCarryShift m f) =
      cosmicCarryShift m (cosmicDigitShift n f) :=
  cosmic_axes_commute m n f

/-- Finite-window observation of global digit transport remains exact. -/
theorem observe_digit_transport_exact
    (A B n : Nat) (f : CompletedCosmos) :
    finiteWindowObservation A B (cosmicDigitShift n f) =
      digitShiftN n (finiteWindowObservation A B f) := by
  exact observe_cosmicDigitShift A B n f

#check cosmicCellSpace
#check cosmicCellChart
#check completedFieldRealization
#check finiteWindowObservation
#check allFiniteWindows_separate
#check old_cosmic_axes_are_one_commuting_chart
#check observe_digit_transport_exact

#print axioms allFiniteWindows_separate
#print axioms old_cosmic_axes_are_one_commuting_chart

end GSTWorldCosmologyGeneralSpaceRealization
