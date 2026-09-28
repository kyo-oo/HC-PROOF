import GSTClassicalHodgeProjectiveVisibilitySeparation
import GSTClassicalHodgeProjectiveDetectorVisibility
import GSTClassicalHodgeProjectiveTomographyReadout
import GSTClassicalHodgeProjectiveOrbitIrreducibilityAudit

/-!
# GST CLASSICAL HODGE — PROJECTIVE VISIBILITY NO-GO BARRIER

The two-burst audit uncovered a crucial logical boundary.

A genuine projective correspondence applied to an already algebraic native
source produces another genuine native algebraic cycle.  Therefore every
omniversal separator ghost annihilates its cycle class.  In particular the
projective detector readout of the canonical algebraic ghost-spine source is
identically zero for every genuine projective kernel.

This means that horizontal `ProjectiveOrbitIrreducibility` cannot be obtained
merely from the existing projective-correspondence algebra: in the presence of
a ghost it is actually impossible.  Any later closure must introduce a new,
independently proved compatibility theorem connecting a GST/cohomological
multiplicity motion to genuine cycle geometry; it must not relabel ordinary
projective correspondence closure as that theorem.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeProjectiveVisibilityNoGo

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeGenuineCycleClassGeometry
open GSTClassicalHodgeProjectiveTomographyReadout
open GSTClassicalHodgeProjectiveDetectorVisibility
open GSTClassicalHodgeProjectiveVisibilitySeparation
open GSTClassicalHodgeOmniversalSeparatorGhostCrown
open GSTClassicalHodgeGhostSpineCosmicLeak
open GSTClassicalHodgeLimitlessSpinePropagation
open GSTClassicalHodgeSynchronizedDefectOrbit

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- **PROJECTIVE READOUT VANISHING.**  Every genuine projective-kernel image
of the canonical algebraic ghost spine has zero reading under the omniversal
ghost detector. -/
theorem projectiveDetectorReadout_ghostSpine_eq_zero
    (J : GenuineCycleClassGeometry V H)
    (M : NativeMassCycleClassBridge V H)
    (E : OmniversalSeparatorGhost J.spine)
    (K : GSTClassicalHodgeProjectiveCorrespondenceAlgebra.ProjectiveNativeKernel
      V E.weight) :
    projectiveDetectorReadout J E.weight
        (ghostSpineSeed J.spine M E).cycle
        E.separator.detector K = 0 := by
  unfold projectiveDetectorReadout
  rw [(ghostSpineSeed J.spine M E).class_eq]
  exact
    ghost_detector_kills_projective_spine_image
      J.spine M E K

/-- Hence no genuine projective kernel can provide the nonzero visibility datum
requested by the earlier detector-visibility reduction. -/
theorem no_nonzero_projectiveDetectorReadout_on_ghostSpine
    (J : GenuineCycleClassGeometry V H)
    (M : NativeMassCycleClassBridge V H)
    (E : OmniversalSeparatorGhost J.spine) :
    ¬ ∃ K : GSTClassicalHodgeProjectiveCorrespondenceAlgebra.ProjectiveNativeKernel
        V E.weight,
      projectiveDetectorReadout J E.weight
        (ghostSpineSeed J.spine M E).cycle
        E.separator.detector K ≠ 0 := by
  rintro ⟨K, hK⟩
  exact hK (projectiveDetectorReadout_ghostSpine_eq_zero J M E K)

/-- In a world containing an omniversal ghost, the global horizontal
`ProjectiveOrbitIrreducibility` certificate is empty.  This is the precise
machine-checked circularity barrier behind the Burst-2 audit. -/
theorem projectiveOrbitIrreducibility_isEmpty_of_ghost
    (J : GenuineCycleClassGeometry V H)
    (M : NativeMassCycleClassBridge V H)
    (E : OmniversalSeparatorGhost J.spine) :
    IsEmpty (ProjectiveOrbitIrreducibility V H J) := by
  refine ⟨?_⟩
  intro R
  rcases exists_projectiveDetectorVisible J R M E with ⟨D⟩
  exact D.detector_nonzero
    (ghost_detector_kills_projective_spine_image J.spine M E D.kernel)

/-- Any proposed theorem deriving projective-orbit irreducibility from only the
genuine geometry package and native-mass bridge already excludes every ghost
and therefore is Hodge-strength. -/
theorem universal_projectiveOrbitIrreducibility_is_hodge_strength
    (J : GenuineCycleClassGeometry V H)
    (M : NativeMassCycleClassBridge V H)
    (build : Nonempty (ProjectiveOrbitIrreducibility V H J)) :
    GSTGeometricRealizationStage2G.BigradedBettiHodgeStatement V H := by
  rcases build with ⟨R⟩
  exact
    GSTClassicalHodgeProjectiveOrbitIrreducibilityAudit.projectiveOrbitIrreducibility_implies_hodge
      J R M

#check projectiveDetectorReadout_ghostSpine_eq_zero
#check no_nonzero_projectiveDetectorReadout_on_ghostSpine
#check projectiveOrbitIrreducibility_isEmpty_of_ghost
#check universal_projectiveOrbitIrreducibility_is_hodge_strength

#print axioms projectiveDetectorReadout_ghostSpine_eq_zero
#print axioms projectiveOrbitIrreducibility_isEmpty_of_ghost
#print axioms universal_projectiveOrbitIrreducibility_is_hodge_strength

end GSTClassicalHodgeProjectiveVisibilityNoGo
