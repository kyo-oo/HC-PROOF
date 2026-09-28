import GSTClassicalHodgeProjectiveDetectorVisibility
import GSTClassicalHodgeFiniteCorrespondenceCohomologyNaturality

/-!
# GST CLASSICAL HODGE — VISIBILITY EQUIVALENCE AUDIT

The scalar detector-visibility reductions are useful because they identify the
smallest possible collision with a surviving separator.  They must not,
however, be mistaken for an independently weaker geometric theorem.

In the present Stage-2G semantics they are exact reformulations of the Hodge
target:

* if Hodge holds there are no omniversal separator ghosts, so every universal
  visibility family is vacuously inhabited;
* if such a visibility family is supplied, the existing blackout theorem
  immediately contradicts any ghost and therefore proves Hodge.

The same applies after enlarging the native geometry from endomorphism-generated
projective kernels to genuine finite closed correspondences with ordinary Betti
push-pull naturality.

This audit marks the semantic floor.  Further progress cannot come from merely
renaming visibility, moment hits, or correspondence detection.  It must come
from strengthening the underlying classical geometric semantics or deriving a
new independent geometric law not available in the zero/free cycle-class
model.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeVisibilityEquivalenceAudit

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeSynchronizedDefectOrbit
open GSTClassicalHodgeOmniversalSeparatorGhostCrown
open GSTClassicalHodgeProjectiveDetectorVisibility
open GSTClassicalHodgeFiniteCorrespondenceCohomologyNaturality

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Projective detector visibility for every possible omniversal ghost is
exactly equivalent to the Stage-2G Hodge statement. -/
theorem hodge_iff_projectiveDetectorVisibility
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H) :
    BigradedBettiHodgeStatement V H ↔
      ∀ E : OmniversalSeparatorGhost G,
        Nonempty (ProjectiveDetectorVisible G M E) := by
  constructor
  · intro h E
    exfalso
    have hno : IsEmpty (OmniversalSeparatorGhost G) :=
      (hodge_iff_no_omniversalSeparatorGhost G).mp h
    exact hno.false E
  · intro hvis
    exact bigradedBettiHodge_of_projectiveDetectorVisibility G M hvis

/-- The same equivalence persists after enlarging geometry to genuine finite
closed correspondences carrying only ordinary Betti push-pull naturality. -/
theorem hodge_iff_finiteCorrespondenceDetectorVisibility
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H) :
    BigradedBettiHodgeStatement V H ↔
      ∀ E : OmniversalSeparatorGhost G,
        Nonempty (FiniteCorrespondenceDetectorVisible G M E) := by
  constructor
  · intro h E
    exfalso
    have hno : IsEmpty (OmniversalSeparatorGhost G) :=
      (hodge_iff_no_omniversalSeparatorGhost G).mp h
    exact hno.false E
  · intro hvis
    exact bigradedBettiHodge_of_finiteCorrespondenceDetectorVisibility G M hvis

/-- Negative form: under a counterexample, not only does one ghost exist, but
both universal visibility principles fail. -/
theorem failure_forces_visibility_failure
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (hnot : ¬ BigradedBettiHodgeStatement V H) :
    (¬ ∀ E : OmniversalSeparatorGhost G,
        Nonempty (ProjectiveDetectorVisible G M E))
      ∧
    (¬ ∀ E : OmniversalSeparatorGhost G,
        Nonempty (FiniteCorrespondenceDetectorVisible G M E)) := by
  constructor
  · intro h
    exact hnot ((hodge_iff_projectiveDetectorVisibility G M).2 h)
  · intro h
    exact hnot ((hodge_iff_finiteCorrespondenceDetectorVisibility G M).2 h)

#check hodge_iff_projectiveDetectorVisibility
#check hodge_iff_finiteCorrespondenceDetectorVisibility
#check failure_forces_visibility_failure

#print axioms hodge_iff_projectiveDetectorVisibility
#print axioms hodge_iff_finiteCorrespondenceDetectorVisibility
#print axioms failure_forces_visibility_failure

end GSTClassicalHodgeVisibilityEquivalenceAudit
