import GSTClassicalHodgeTomographyVisibilityCrown
import GSTClassicalHodgeOmniversalSeparatorGhostCrown

/-!
# GST CLASSICAL HODGE — GENUINE SEMANTIC CLOSURE

This file is the exact conditional landing for the two-burst route.

`GenuineCycleClassGeometry` is now deliberately limited to independently
geometric information: the established geometric spine and positive
projective-degree trace.  Horizontal projective-orbit irreducibility is a
separate explicit certificate because the repository's visibility-equivalence
audit shows that universal detector visibility is already Hodge-strength.

Therefore every theorem below displays the horizontal certificate in its
signature.  This makes the remaining mathematical obligation impossible to
hide under the name "genuine geometry".
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeGenuineSemanticClosure

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeSynchronizedDefectOrbit
open GSTClassicalHodgeOmniversalSeparatorGhostCrown
open GSTClassicalHodgeGenuineCycleClassGeometry
open GSTClassicalHodgeTomographyVisibilityCrown

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Any negation of the Hodge target contradicts an explicit horizontal
projective-orbit irreducibility certificate. -/
theorem not_hodge_impossible_of_projectiveOrbitIrreducibility
    (J : GenuineCycleClassGeometry V H)
    (R : ProjectiveOrbitIrreducibility V H J)
    (M : NativeMassCycleClassBridge V H)
    (hnot : ¬ BigradedBettiHodgeStatement V H) : False := by
  rcases
      (not_hodge_iff_nonempty_omniversalSeparatorGhost J.spine).mp hnot with
    ⟨E⟩
  exact omniversalGhost_false J R M E

/--
**CONDITIONAL SEMANTIC HODGE CLOSURE.**

The full Stage-2G rational `(p,p)` cycle-class landing follows from independently
certified genuine cycle-class geometry, the native-mass bridge, and the
explicit horizontal projective-orbit irreducibility certificate.
-/
theorem bigradedBettiHodge_of_projectiveOrbitIrreducibility
    (J : GenuineCycleClassGeometry V H)
    (R : ProjectiveOrbitIrreducibility V H J)
    (M : NativeMassCycleClassBridge V H) :
    BigradedBettiHodgeStatement V H := by
  exact
    (hodge_iff_no_omniversalSeparatorGhost J.spine).2
      (no_omniversalSeparatorGhost J R M)

/-- Direct contradiction form exposing the terminal projective-tomography
collision selected by any alleged counterexample. -/
theorem counterexample_yields_projective_tomography_contradiction
    (J : GenuineCycleClassGeometry V H)
    (R : ProjectiveOrbitIrreducibility V H J)
    (M : NativeMassCycleClassBridge V H)
    (hnot : ¬ BigradedBettiHodgeStatement V H) :
    ∃ E : OmniversalSeparatorGhost J.spine,
      Nonempty
        (GSTClassicalHodgeProjectiveDetectorMomentCollision.ProjectiveDetectorMomentHit
          J.spine M E)
      ∧ IsEmpty
        (GSTClassicalHodgeProjectiveDetectorMomentCollision.ProjectiveDetectorMomentHit
          J.spine M E) := by
  rcases
      (not_hodge_iff_nonempty_omniversalSeparatorGhost J.spine).mp hnot with
    ⟨E⟩
  refine ⟨E, omniversalGhost_has_tomography_moment_hit J R M E, ?_⟩
  exact
    GSTClassicalHodgeProjectiveDetectorMomentCollision.no_projectiveDetectorMomentHit
      J.spine M E

/-- Conditional Burst-2 crown with the unresolved horizontal certificate
exposed rather than hidden. -/
theorem conditional_semantic_closure_crown
    (J : GenuineCycleClassGeometry V H)
    (R : ProjectiveOrbitIrreducibility V H J)
    (M : NativeMassCycleClassBridge V H) :
    BigradedBettiHodgeStatement V H
    ∧ IsEmpty (OmniversalSeparatorGhost J.spine) := by
  exact ⟨
    bigradedBettiHodge_of_projectiveOrbitIrreducibility J R M,
    no_omniversalSeparatorGhost J R M⟩

#check not_hodge_impossible_of_projectiveOrbitIrreducibility
#check bigradedBettiHodge_of_projectiveOrbitIrreducibility
#check counterexample_yields_projective_tomography_contradiction
#check conditional_semantic_closure_crown

#print axioms not_hodge_impossible_of_projectiveOrbitIrreducibility
#print axioms bigradedBettiHodge_of_projectiveOrbitIrreducibility
#print axioms counterexample_yields_projective_tomography_contradiction
#print axioms conditional_semantic_closure_crown

end GSTClassicalHodgeGenuineSemanticClosure
