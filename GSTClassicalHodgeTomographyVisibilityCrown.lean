import GSTClassicalHodgeProjectiveVisibilitySeparation
import GSTClassicalHodgeProjectiveDetectorMomentCollision
import GSTClassicalHodgeProjectiveDetectorVisibility
import GSTClassicalHodgeOmniversalSeparatorGhostCrown

/-!
# GST CLASSICAL HODGE — TOMOGRAPHY VISIBILITY CROWN

Burst 2 begins here.  The strengthened genuine cycle-class geometry supplies
one nonzero projective detector readout on the canonical nonzero algebraic
spine source of every omniversal ghost.  The existing rational scaling law
normalizes that readout to the exact nonzero finite GST Lefschetz-tomography
moment selected by the ghost.

But the existing detector-moment collision theorem proves that no surviving
ghost can admit such a projective moment hit.  Thus the two independently
developed fronts collide directly:

  genuine projective-orbit visibility
    -> exact finite tomography moment hit
    -> ghost annihilates every projective image
    -> contradiction.

No all-pairs matrix-unit realization or target basis-cycle witness is used in
this composition.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeTomographyVisibilityCrown

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeSynchronizedDefectOrbit
open GSTClassicalHodgeOmniversalSeparatorGhostCrown
open GSTClassicalHodgeProjectiveDetectorMomentCollision
open GSTClassicalHodgeProjectiveDetectorVisibility
open GSTClassicalHodgeProjectiveVisibilitySeparation
open GSTClassicalHodgeGenuineCycleClassGeometry

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Every omniversal ghost under genuine cycle-class geometry produces the
projective detector visibility datum that the old ghost laws forbid. -/
theorem omniversalGhost_has_projective_visibility
    (J : GenuineCycleClassGeometry V H)
    (M : NativeMassCycleClassBridge V H)
    (E : OmniversalSeparatorGhost J.spine) :
    Nonempty (ProjectiveDetectorVisible J.spine M E) :=
  exists_projectiveDetectorVisible J M E

/-- Every omniversal ghost also produces an exact hit on its selected nonzero
finite GST tomography moment. -/
theorem omniversalGhost_has_tomography_moment_hit
    (J : GenuineCycleClassGeometry V H)
    (M : NativeMassCycleClassBridge V H)
    (E : OmniversalSeparatorGhost J.spine) :
    Nonempty (ProjectiveDetectorMomentHit J.spine M E) :=
  exists_projectiveDetectorMomentHit J M E

/-- **PROJECTIVE TOMOGRAPHY COLLISION.**  A surviving omniversal ghost is
incompatible with genuine cycle-class geometry plus the native-mass spine. -/
theorem omniversalGhost_false
    (J : GenuineCycleClassGeometry V H)
    (M : NativeMassCycleClassBridge V H)
    (E : OmniversalSeparatorGhost J.spine) : False := by
  rcases omniversalGhost_has_tomography_moment_hit J M E with ⟨R⟩
  exact (no_projectiveDetectorMomentHit J.spine M E).false R

/-- Visibility-level proof of the same contradiction, useful as an audit that
the exact moment normalization is not mathematically essential. -/
theorem omniversalGhost_false_of_visibility
    (J : GenuineCycleClassGeometry V H)
    (M : NativeMassCycleClassBridge V H)
    (E : OmniversalSeparatorGhost J.spine) : False := by
  rcases omniversalGhost_has_projective_visibility J M E with ⟨R⟩
  exact (no_projectiveDetectorVisible J.spine M E).false R

/-- Under the strengthened geometry package there are no omniversal separator
ghosts at all. -/
theorem no_omniversalSeparatorGhost
    (J : GenuineCycleClassGeometry V H)
    (M : NativeMassCycleClassBridge V H) :
    IsEmpty (OmniversalSeparatorGhost J.spine) :=
  ⟨fun E => omniversalGhost_false J M E⟩

/-- Burst-2 crown: every hypothetical ghost generates both the nonzero
visibility datum and the exact tomography hit, yet the entire ghost type is
empty. -/
theorem tomography_visibility_crown
    (J : GenuineCycleClassGeometry V H)
    (M : NativeMassCycleClassBridge V H) :
    (∀ E : OmniversalSeparatorGhost J.spine,
      Nonempty (ProjectiveDetectorVisible J.spine M E))
    ∧ (∀ E : OmniversalSeparatorGhost J.spine,
      Nonempty (ProjectiveDetectorMomentHit J.spine M E))
    ∧ IsEmpty (OmniversalSeparatorGhost J.spine) := by
  exact ⟨
    omniversalGhost_has_projective_visibility J M,
    omniversalGhost_has_tomography_moment_hit J M,
    no_omniversalSeparatorGhost J M⟩

#check omniversalGhost_has_projective_visibility
#check omniversalGhost_has_tomography_moment_hit
#check omniversalGhost_false
#check omniversalGhost_false_of_visibility
#check no_omniversalSeparatorGhost
#check tomography_visibility_crown

#print axioms omniversalGhost_false
#print axioms omniversalGhost_false_of_visibility
#print axioms no_omniversalSeparatorGhost
#print axioms tomography_visibility_crown

end GSTClassicalHodgeTomographyVisibilityCrown
