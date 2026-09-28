import GSTClassicalHodgeProjectiveTomographyReadout
import GSTClassicalHodgeGhostSpineCosmicLeak
import GSTClassicalHodgeProjectiveDetectorVisibility
import GSTClassicalHodgeProjectiveDetectorMomentCollision

/-!
# GST CLASSICAL HODGE — PROJECTIVE VISIBILITY SEPARATION

This file specializes an explicit `ProjectiveOrbitIrreducibility` certificate
to the canonical algebraic spine source carried by an omniversal separator
ghost.

The source is genuinely algebraic and nonzero by the native-mass bridge.  The
ghost detector is genuinely Hodge-visible because it detects its stored basis
sheet.  Hence a supplied orbit-irreducibility certificate produces a genuine
projective kernel with nonzero detector readout.  The existing rational
rescaling theorem then converts that visibility into an exact hit on the
nonzero finite GST Lefschetz-tomography moment.

This module is therefore a reduction layer, not an independent construction of
horizontal visibility.  `GenuineCycleClassGeometry` alone is deliberately not
sufficient for the theorem statements below.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeProjectiveVisibilitySeparation

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeProjectiveCorrespondenceAlgebra
open GSTClassicalHodgeProjectiveCorrespondenceCosmicRealization
open GSTClassicalHodgeOmniversalSeparatorGhostCrown
open GSTClassicalHodgeGhostSpineCosmicLeak
open GSTClassicalHodgeProjectiveDetectorMomentCollision
open GSTClassicalHodgeProjectiveDetectorVisibility
open GSTClassicalHodgeProjectiveTomographyReadout
open GSTClassicalHodgeGenuineCycleClassGeometry

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- The canonical native spine cycle attached to a ghost has nonzero cycle
class.  This uses only the native-mass nonvanishing already stored in the
`NativeHodgeOrbitSeed`. -/
theorem ghostSpine_cycleClass_ne_zero
    (J : GenuineCycleClassGeometry V H)
    (M : NativeMassCycleClassBridge V H)
    (E : OmniversalSeparatorGhost J.spine) :
    H.cycleClass E.weight (ghostSpineSeed J.spine M E).cycle ≠ 0 := by
  let S := ghostSpineSeed J.spine M E
  have hval : S.hodge.1 ≠ 0 := by
    intro hzero
    apply S.hodge_ne_zero
    apply Subtype.ext
    exact hzero
  rw [S.class_eq]
  exact hval

/-- The ghost detector is a Hodge-visible detector in the sense required by
projective-orbit irreducibility. -/
theorem ghost_detector_hodge_visible
    (J : GenuineCycleClassGeometry V H)
    (E : OmniversalSeparatorGhost J.spine) :
    E.separator.detector
      (classicalHodgeBasis V H E.weight E.sheet).1 ≠ 0 :=
  E.separator.detects_basis

/--
**FINITE PROJECTIVE VISIBILITY SEPARATION — CONDITIONAL FORM.**

The explicit orbit-irreducibility certificate applied to the nonzero canonical
spine source and the basis state detected by the ghost produces one actual
projective kernel whose detector response is nonzero.
-/
theorem exists_projectiveDetectorVisible
    (J : GenuineCycleClassGeometry V H)
    (R : ProjectiveOrbitIrreducibility V H J)
    (M : NativeMassCycleClassBridge V H)
    (E : OmniversalSeparatorGhost J.spine) :
    Nonempty (ProjectiveDetectorVisible J.spine M E) := by
  let S := ghostSpineSeed J.spine M E
  obtain ⟨K, hK⟩ :=
    exists_nonzero_projectiveDetectorReadout
      J R E.weight S.cycle
      (ghostSpine_cycleClass_ne_zero J M E)
      (classicalHodgeBasis V H E.weight E.sheet)
      E.separator.detector
      E.separator.detects_basis
  refine ⟨{
    kernel := K
    detector_nonzero := ?_
  }⟩
  unfold projectiveDetectorReadout at hK
  rw [S.class_eq] at hK
  simpa [S] using hK

/-- The same conditional visibility can be normalized to the exact nonzero
tomography moment selected by the ghost. -/
theorem exists_projectiveDetectorMomentHit
    (J : GenuineCycleClassGeometry V H)
    (R : ProjectiveOrbitIrreducibility V H J)
    (M : NativeMassCycleClassBridge V H)
    (E : OmniversalSeparatorGhost J.spine) :
    Nonempty (ProjectiveDetectorMomentHit J.spine M E) := by
  rcases exists_projectiveDetectorVisible J R M E with ⟨D⟩
  exact ⟨D.toMomentHit⟩

/-- Explicit scalar form of the conditional reduction. -/
theorem exists_projectiveKernel_readout_eq_ghostMoment
    (J : GenuineCycleClassGeometry V H)
    (R : ProjectiveOrbitIrreducibility V H J)
    (M : NativeMassCycleClassBridge V H)
    (E : OmniversalSeparatorGhost J.spine) :
    ∃ K : ProjectiveNativeKernel V E.weight,
      E.separator.detector
        ((projectiveCorrespondencePair J.spine K).cohomologyOperator
          (ghostSpineSeed J.spine M E).hodge.1) =
        GSTClassicalHodgeLefschetzTomography.lefschetzTomography
          (GSTClassicalHodgeLefschetzTomography.supportCoordinateVector
            (fiberedWeightCoordinates V H E.weight
              (classicalHodgeBasis V H E.weight E.sheet)))
          (ghostMomentIndex J.spine E) := by
  rcases exists_projectiveDetectorMomentHit J R M E with ⟨D⟩
  exact ⟨D.kernel, D.detector_eq_moment⟩

#check ghostSpine_cycleClass_ne_zero
#check ghost_detector_hodge_visible
#check exists_projectiveDetectorVisible
#check exists_projectiveDetectorMomentHit
#check exists_projectiveKernel_readout_eq_ghostMoment

#print axioms ghostSpine_cycleClass_ne_zero
#print axioms exists_projectiveDetectorVisible
#print axioms exists_projectiveDetectorMomentHit
#print axioms exists_projectiveKernel_readout_eq_ghostMoment

end GSTClassicalHodgeProjectiveVisibilitySeparation
