import GSTClassicalHodgeGeometricCycleClassPointRigidity
import GSTClassicalHodgeExactClayStatement

/-!
# Stage2G with point-generated geometric cycle classes in EVERY codimension

This construction REMOVES the arbitrary linear-map choice of cycleClass
from the Hodge data interface once a geometric fundamental Betti class
is assigned to EVERY irreducible codimension-p subvariety. The resulting
cycleClass is the unique rational-linear extension of all point classes.

It is an unconditional algebraic construction FROM THE SUPPLIED POINT
FUNDAMENTAL CLASSES. It is not an analytic construction of those classes
and it does NOT imply that their span contains all rational Hodge classes.
That latter assertion, for arbitrary X and p, is the EXACT classical
Hodge conjecture, kept as an explicit separate acceptance target.
-/

set_option maxHeartbeats 10000000
noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeGeometricCycleClassPointRigidity

namespace GSTCanonicalPointGeometryStage2G

variable {V : SmoothProjectiveComplexScheme}

/-- A coherent family of rational Betti point fundamental classes
in all codimensions on the ORIGINAL variety V. -/
abbrev AllCodimensionPointBettiClasses
    (H : HodgeBigradedBettiData V) : Type :=
  ∀ p : Nat, PointBettiClass (V := V) p H.analytification

/-- Actual all-codimension cycle-class map derived from
irreducible subvariety point data rather than a supplied arbitrary
linear map. No Hodge-cycle representatives are chosen. -/
noncomputable def pointGeneratedHodgeData
    (H : HodgeBigradedBettiData V)
    (pt : AllCodimensionPointBettiClasses H) :
    HodgeBigradedBettiData V where
  analytification := H.analytification
  hodgeBigrading := H.hodgeBigrading
  cycleClass := fun p =>
    cycleClassFromPointGeometry (V := V) p H.analytification (pt p)

/-- The new geometry-generated cycleClass maps every actual
codimension-p point cycle to its stated Betti fundamental class. -/
theorem pointGeneratedHodgeData_point
    (H : HodgeBigradedBettiData V)
    (pt : AllCodimensionPointBettiClasses H)
    (p : Nat) (x : CodimensionPoint V.X p) :
    (pointGeneratedHodgeData H pt).cycleClass p
      (codimensionPointCycle V.X p x) = pt p x := by
  exact cycleClassFromPointGeometry_point
    (V := V) p H.analytification (pt p) x

/-- The exact range of the derived all-codimension class map
is the rational span of genuine irreducible point fundamental
classes. This is a statement of geometry-generated semantics,
NOT the assertion that such a span equals the Hodge sector. -/
theorem pointGeneratedHodgeData_range
    (H : HodgeBigradedBettiData V)
    (pt : AllCodimensionPointBettiClasses H)
    (p : Nat) :
    LinearMap.range ((pointGeneratedHodgeData H pt).cycleClass p) =
      Submodule.span ℚ (Set.range (pt p)) := by
  exact cycleClassFromPointGeometry_range_eq_pointSpan
    (V := V) p H.analytification (pt p)

/-- Pin the classical Hodge conjecture in point-geometric
semantics: the conjecture is exactly the statement that, in
EVERY codimension, the rational Hodge subspace lies in the
span of actual point fundamental classes. The equality is an
auditable reduction, not a proof of the containment. -/
theorem pointGeneratedHodgeStatement_iff_actual_point_span
    (H : HodgeBigradedBettiData V)
    (pt : AllCodimensionPointBettiClasses H) :
    BigradedBettiHodgeStatement V (pointGeneratedHodgeData H pt) ↔
      ∀ p : Nat,
        rationalHodgeSubspace (H.hodgeBigrading p) ≤
          Submodule.span ℚ (Set.range (pt p)) := by
  unfold BigradedBettiHodgeStatement
  constructor
  · intro h p
    have hp := h p
    change rationalHodgeSubspace (H.hodgeBigrading p) ≤
      LinearMap.range
        (cycleClassFromPointGeometry (V := V) p H.analytification (pt p)) at hp
    rwa [cycleClassFromPointGeometry_range_eq_pointSpan] at hp
  · intro h p
    change rationalHodgeSubspace (H.hodgeBigrading p) ≤
      LinearMap.range
        (cycleClassFromPointGeometry (V := V) p H.analytification (pt p))
    rw [cycleClassFromPointGeometry_range_eq_pointSpan]
    exact h p

#check pointGeneratedHodgeData
#check pointGeneratedHodgeData_point
#check pointGeneratedHodgeData_range
#check pointGeneratedHodgeStatement_iff_actual_point_span
#print axioms pointGeneratedHodgeStatement_iff_actual_point_span

end GSTCanonicalPointGeometryStage2G
