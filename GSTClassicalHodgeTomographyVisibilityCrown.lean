import GSTClassicalHodgeProjectiveVisibilitySeparation
import GSTClassicalHodgeProjectiveDetectorMomentCollision
import GSTClassicalHodgeProjectiveDetectorVisibility
import GSTClassicalHodgeOmniversalSeparatorGhostCrown

/-!
# GST CLASSICAL HODGE — TOMOGRAPHY VISIBILITY CROWN

This module records the exact consequence of an explicit horizontal
`ProjectiveOrbitIrreducibility` certificate.

The independently geometric `GenuineCycleClassGeometry` package supplies the
nonzero genuine cycle-class foundation.  The separate orbit certificate then
supplies one nonzero projective detector readout on the canonical algebraic
spine source of every omniversal ghost.  Existing rational scaling normalizes
that readout to the exact nonzero finite GST Lefschetz-tomography moment.

The existing detector-moment collision theorem proves that no surviving ghost
can admit such a hit.  Thus this file is an exact conditional crown and makes
the remaining horizontal theorem explicit rather than hiding it in the
geometry package.
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
open GSTClassicalHodgeLimitlessSpinePropagation

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Every omniversal ghost under an explicit orbit-irreducibility certificate
produces the projective detector visibility datum forbidden by the old ghost
laws. -/
theorem omniversalGhost_has_projective_visibility
    (J : GenuineCycleClassGeometry V H)
    (R : ProjectiveOrbitIrreducibility V H J)
    (M : NativeMassCycleClassBridge V H)
    (E : OmniversalSeparatorGhost J.spine) :
    Nonempty (ProjectiveDetectorVisible J.spine M E) :=
  exists_projectiveDetectorVisible J R M E

/-- Every omniversal ghost also produces an exact hit on its selected nonzero
finite GST tomography moment. -/
theorem omniversalGhost_has_tomography_moment_hit
    (J : GenuineCycleClassGeometry V H)
    (R : ProjectiveOrbitIrreducibility V H J)
    (M : NativeMassCycleClassBridge V H)
    (E : OmniversalSeparatorGhost J.spine) :
    Nonempty (ProjectiveDetectorMomentHit J.spine M E) :=
  exists_projectiveDetectorMomentHit J R M E

/-- **PROJECTIVE TOMOGRAPHY COLLISION — CONDITIONAL FORM.** -/
theorem omniversalGhost_false
    (J : GenuineCycleClassGeometry V H)
    (R : ProjectiveOrbitIrreducibility V H J)
    (M : NativeMassCycleClassBridge V H)
    (E : OmniversalSeparatorGhost J.spine) : False := by
  rcases omniversalGhost_has_tomography_moment_hit J R M E with ⟨D⟩
  exact (no_projectiveDetectorMomentHit J.spine M E).false D

/-- Visibility-level proof of the same conditional contradiction. -/
theorem omniversalGhost_false_of_visibility
    (J : GenuineCycleClassGeometry V H)
    (R : ProjectiveOrbitIrreducibility V H J)
    (M : NativeMassCycleClassBridge V H)
    (E : OmniversalSeparatorGhost J.spine) : False := by
  rcases omniversalGhost_has_projective_visibility J R M E with ⟨D⟩
  exact (no_projectiveDetectorVisible J.spine M E).false D

/-- An orbit-irreducibility certificate makes the omniversal ghost type empty. -/
theorem no_omniversalSeparatorGhost
    (J : GenuineCycleClassGeometry V H)
    (R : ProjectiveOrbitIrreducibility V H J)
    (M : NativeMassCycleClassBridge V H) :
    IsEmpty (OmniversalSeparatorGhost J.spine) :=
  ⟨fun E => omniversalGhost_false J R M E⟩

/-- Conditional tomography visibility crown with the horizontal certificate
shown explicitly in the theorem signature. -/
theorem tomography_visibility_crown
    (J : GenuineCycleClassGeometry V H)
    (R : ProjectiveOrbitIrreducibility V H J)
    (M : NativeMassCycleClassBridge V H) :
    (∀ E : OmniversalSeparatorGhost J.spine,
      Nonempty (ProjectiveDetectorVisible J.spine M E))
    ∧ (∀ E : OmniversalSeparatorGhost J.spine,
      Nonempty (ProjectiveDetectorMomentHit J.spine M E))
    ∧ IsEmpty (OmniversalSeparatorGhost J.spine) := by
  exact ⟨
    omniversalGhost_has_projective_visibility J R M,
    omniversalGhost_has_tomography_moment_hit J R M,
    no_omniversalSeparatorGhost J R M⟩

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
