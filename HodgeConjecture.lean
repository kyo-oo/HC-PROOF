import GSTClassicalHodgePresentationLanding

/-!
# HODGE CONJECTURE — CLASSICAL GST CAPSTONE

This file is intentionally small.  The unrestricted classical Hodge
multiplicity, limitless GST coordinates, native algebraic cycles, and finite
codimension-point presentations live in dedicated modules below this capstone.

The target here is exactly the Stage-2G rational Hodge statement for an
actual bundled smooth projective complex scheme and its supplied classical
semantic data.  No finite GST carrier is substituted for arbitrary classical
cohomology.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeCycleLanding
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgePresentationLanding

namespace HodgeConjecture

/-- The genuine Stage-2G rational Hodge target. -/
def ClassicalHodgeTarget
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) : Prop :=
  BigradedBettiHodgeStatement V H

/-- Elementwise normal form: every rational class whose complexification lies
in `H^(p,p)` has an actual native codimension-p algebraic-cycle preimage. -/
theorem classicalHodgeTarget_iff_explicit_witness
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) :
    ClassicalHodgeTarget V H ↔
      ∀ p : Nat,
      ∀ alpha : RationalSingularCohomology H.analytification (2 * p),
        complexificationMapQ
            (RationalSingularCohomology H.analytification (2 * p)) alpha
          ∈ (H.hodgeBigrading p).ppComponent →
        ∃ Z : codimensionCycles V.X p,
          H.cycleClass p Z = alpha := by
  simpa [ClassicalHodgeTarget] using
    (bigradedBettiHodgeStatement_iff_explicit_witness V H)

/-- Existing Stage-2G compact-realization closure. -/
theorem classicalHodgeTarget_of_compact_realization
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (hR : Stage2GCompactRealizationObligation V H) :
    ClassicalHodgeTarget V H := by
  exact bigraded_betti_hodge_of_stage2g_compact_obligation V H hR

/-- The limitless GST/classical normal form.  The GST projection of each
basis direction to cosmic `(p,p)` is already unconditional; all unresolved
content is the native algebraic-cycle landing. -/
theorem classicalHodgeTarget_iff_fibered_gst_algebraicity
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) :
    ClassicalHodgeTarget V H ↔ FiberedGSTAlgebraicityBridge V H := by
  simpa [ClassicalHodgeTarget] using
    (bigradedBettiHodgeStatement_iff_fibered_gst_algebraicity V H)

/-- Native basis-cycle representatives in every Hodge multiplicity fiber
close the genuine classical target. -/
theorem classicalHodgeTarget_of_fibered_basis_cycles
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (R : ∀ p : Nat, FiberedBasisCycleBridge V H p) :
    ClassicalHodgeTarget V H := by
  exact bigraded_hodge_of_fibered_basis_cycle_family V H R

/-- Finite rational presentations by genuine codimension-p scheme points in
every Hodge basis direction close the genuine classical target. -/
theorem classicalHodgeTarget_of_finite_presentations
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (R : ∀ p : Nat, FiberedBasisPresentationBridge V H p) :
    ClassicalHodgeTarget V H := by
  exact bigraded_hodge_of_finite_presentation_family V H R

/-- Most concrete forward interface currently available: a finite rational
sum of the actual point-cycle classes equals each genuine Hodge basis vector. -/
theorem classicalHodgeTarget_of_point_class_sum_family
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (presentation :
      ∀ p : Nat,
        ClassicalHodgeBasisIndex V H p →
          FiniteCodimensionPresentation V.X p)
    (hclass :
      ∀ p : Nat, ∀ i : ClassicalHodgeBasisIndex V H p,
        (presentation p i).sum (fun x q =>
            q • H.cycleClass p (codimensionPointCycle V.X p x)) =
          (classicalHodgeBasis V H p i).1) :
    ClassicalHodgeTarget V H := by
  exact bigraded_hodge_of_point_class_sum_family V H presentation hclass

/-- Semantic firewall.  An arbitrary Stage-2G package can choose the zero
cycle-class map; if a nonzero `(p,p)` class exists then the target is false.
Therefore a final unconditional theorem must construct or geometrically
characterize the genuine classical cycle-class map rather than manufacture
surjectivity from an unconstrained field. -/
theorem not_classicalHodgeTarget_of_zero_cycleClass
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha :
      complexificationMapQ
          (RationalSingularCohomology H.analytification (2 * p)) alpha
        ∈ (H.hodgeBigrading p).ppComponent)
    (halpha_ne : alpha ≠ 0)
    (hzero : H.cycleClass p = 0) :
    ¬ ClassicalHodgeTarget V H := by
  intro hTarget
  obtain ⟨Z, hZ⟩ :=
    (classicalHodgeTarget_iff_explicit_witness V H).mp hTarget
      p alpha halpha
  have hzeroZ : H.cycleClass p Z = 0 := by
    rw [hzero]
    rfl
  apply halpha_ne
  rw [← hZ, hzeroZ]

#check ClassicalHodgeTarget
#check classicalHodgeTarget_iff_explicit_witness
#check classicalHodgeTarget_of_compact_realization
#check classicalHodgeTarget_iff_fibered_gst_algebraicity
#check classicalHodgeTarget_of_fibered_basis_cycles
#check classicalHodgeTarget_of_finite_presentations
#check classicalHodgeTarget_of_point_class_sum_family
#check not_classicalHodgeTarget_of_zero_cycleClass

#print axioms classicalHodgeTarget_iff_explicit_witness
#print axioms classicalHodgeTarget_of_compact_realization
#print axioms classicalHodgeTarget_iff_fibered_gst_algebraicity
#print axioms classicalHodgeTarget_of_fibered_basis_cycles
#print axioms classicalHodgeTarget_of_finite_presentations
#print axioms classicalHodgeTarget_of_point_class_sum_family
#print axioms not_classicalHodgeTarget_of_zero_cycleClass

end HodgeConjecture
