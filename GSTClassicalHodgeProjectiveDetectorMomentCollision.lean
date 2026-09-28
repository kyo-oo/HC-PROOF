import GSTClassicalHodgeProjectiveCorrespondenceCosmicRealization
import GSTClassicalHodgeGhostSpineCosmicLeak
import GSTClassicalHodgeTomographyDefectSplice

/-!
# GST CLASSICAL HODGE — PROJECTIVE DETECTOR-MOMENT COLLISION

The earlier projective externalization interfaces asked a genuine geometric
operator to realize an entire GST matrix unit or to hit a prescribed Hodge
basis vector exactly.  That is much stronger than a separator contradiction
needs.

A ghost separator annihilates every genuine cycle class.  The canonical spine
seed is already an actual cycle class.  Therefore *every* genuine
cycle-natural projective-correspondence operator has separator reading zero on
the cohomological image of that seed.

Finite GST tomography, independently, supplies a nonzero rational moment on
the obstructed basis state.  Hence the remaining horizontal realization target
can be reduced to one scalar equality: build a genuine projective kernel whose
separator reading on the spine source equals one chosen nonzero GST tomography
moment.  Such a kernel immediately contradicts the ghost.

This scalar target does not assume a target basis cycle, a matrix-unit action,
or Hodge surjectivity.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeProjectiveDetectorMomentCollision

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeAtomicAnnihilator
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeProjectiveCorrespondenceAlgebra
open GSTClassicalHodgeProjectiveCorrespondenceCosmicRealization
open GSTClassicalHodgeSynchronizedDefectOrbit
open GSTClassicalHodgeGhostSpineCosmicLeak
open GSTClassicalHodgeOmniversalSeparatorGhostCrown
open GSTClassicalHodgeTomographyDefectSplice
open GSTClassicalHodgeLefschetzTomography
open GSTClassicalHodgeFiberedCosmology

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Every genuine projective-correspondence image of the canonical algebraic
spine seed is invisible to a surviving ghost separator. -/
theorem ghost_detector_kills_projective_spine_image
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (E : OmniversalSeparatorGhost G)
    (K : ProjectiveNativeKernel V E.weight) :
    E.separator.detector
      ((projectiveCorrespondencePair G K).cohomologyOperator
        (ghostSpineSeed G M E).hodge.1) = 0 := by
  let S := ghostSpineSeed G M E
  have hnat :=
    (projectiveCorrespondencePair G K).cycleClass_cycleOperator S.cycle
  rw [S.class_eq] at hnat
  have hrange :
      H.cycleClass E.weight
          ((projectiveCorrespondencePair G K).cycleOperator S.cycle) ∈
        LinearMap.range (H.cycleClass E.weight) := by
    exact ⟨(projectiveCorrespondencePair G K).cycleOperator S.cycle, rfl⟩
  have hatomic :
      H.cycleClass E.weight
          ((projectiveCorrespondencePair G K).cycleOperator S.cycle) ∈
        pointCycleClassSpan E.weight (H.cycleClass E.weight) := by
    rw [← smoothProjective_cycleClass_range_eq_atomic_span V H E.weight]
    exact hrange
  have hker :
      pointCycleClassSpan E.weight (H.cycleClass E.weight) ≤
        LinearMap.ker E.separator.detector :=
    (annihilatesPointCycles_iff_atomicSpan_le_ker
      E.weight (H.cycleClass E.weight) E.separator.detector).mp
      E.separator.annihilates_atoms
  have hzero := hker hatomic
  rw [LinearMap.mem_ker] at hzero
  rw [← hnat]
  exact hzero

/-- Canonical finite tomography index selected from the ghost basis. -/
noncomputable def ghostMomentIndex
    (G : GeometricCycleClassSpine V H)
    (E : OmniversalSeparatorGhost G) :
    Fin
      (fiberedSupportSize
        (fiberedWeightCoordinates V H E.weight
          (classicalHodgeBasis V H E.weight E.sheet))) :=
  Classical.choose
    (separator_basis_has_nonzero_lefschetzMoment E.separator)

/-- The selected ghost tomography moment is nonzero. -/
theorem ghostMoment_ne_zero
    (G : GeometricCycleClassSpine V H)
    (E : OmniversalSeparatorGhost G) :
    lefschetzTomography
      (supportCoordinateVector
        (fiberedWeightCoordinates V H E.weight
          (classicalHodgeBasis V H E.weight E.sheet)))
      (ghostMomentIndex G E) ≠ 0 :=
  Classical.choose_spec
    (separator_basis_has_nonzero_lefschetzMoment E.separator)

/-- The new minimal horizontal target: one genuine projective kernel whose
single separator reading matches the one nonzero tomography scalar selected by
the ghost.  No exact target-vector identity is requested. -/
structure ProjectiveDetectorMomentHit
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (E : OmniversalSeparatorGhost G) where
  kernel : ProjectiveNativeKernel V E.weight
  detector_eq_moment :
    E.separator.detector
      ((projectiveCorrespondencePair G kernel).cohomologyOperator
        (ghostSpineSeed G M E).hodge.1) =
      lefschetzTomography
        (supportCoordinateVector
          (fiberedWeightCoordinates V H E.weight
            (classicalHodgeBasis V H E.weight E.sheet)))
        (ghostMomentIndex G E)

/-- A surviving ghost admits no projective detector-moment hit. -/
theorem no_projectiveDetectorMomentHit
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (E : OmniversalSeparatorGhost G) :
    IsEmpty (ProjectiveDetectorMomentHit G M E) := by
  refine ⟨?_⟩
  intro R
  have hzero := ghost_detector_kills_projective_spine_image G M E R.kernel
  rw [R.detector_eq_moment] at hzero
  exact (ghostMoment_ne_zero G E) hzero

/-- Counterexample form: any Stage-2G failure produces a concrete ghost for
which the scalar projective tomography target is impossible. -/
theorem failure_yields_projectiveDetectorMoment_obstruction
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (hnot : ¬ BigradedBettiHodgeStatement V H) :
    ∃ E : OmniversalSeparatorGhost G,
      IsEmpty (ProjectiveDetectorMomentHit G M E) := by
  rcases (not_hodge_iff_nonempty_omniversalSeparatorGhost G).mp hnot with ⟨E⟩
  exact ⟨E, no_projectiveDetectorMomentHit G M E⟩

/-- **SCALAR TOMOGRAPHY CLOSURE CRITERION.**
It is enough to construct one projective detector-moment hit for every possible
omniversal ghost.  This criterion is strictly weaker than realizing a complete
matrix unit, a target basis vector, or an all-pairs operator arsenal. -/
theorem bigradedBettiHodge_of_projectiveDetectorMoments
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (realize : ∀ E : OmniversalSeparatorGhost G,
      Nonempty (ProjectiveDetectorMomentHit G M E)) :
    BigradedBettiHodgeStatement V H := by
  by_contra hnot
  rcases (not_hodge_iff_nonempty_omniversalSeparatorGhost G).mp hnot with ⟨E⟩
  exact (no_projectiveDetectorMomentHit G M E).false
    (Classical.choice (realize E))

#check ghost_detector_kills_projective_spine_image
#check ghostMomentIndex
#check ghostMoment_ne_zero
#check ProjectiveDetectorMomentHit
#check no_projectiveDetectorMomentHit
#check failure_yields_projectiveDetectorMoment_obstruction
#check bigradedBettiHodge_of_projectiveDetectorMoments

#print axioms ghost_detector_kills_projective_spine_image
#print axioms ghostMoment_ne_zero
#print axioms no_projectiveDetectorMomentHit
#print axioms bigradedBettiHodge_of_projectiveDetectorMoments

end GSTClassicalHodgeProjectiveDetectorMomentCollision
