import GSTClassicalHodgeProjectiveDetectorMomentCollision

/-!
# GST CLASSICAL HODGE — PROJECTIVE DETECTOR VISIBILITY

The detector-moment target can be weakened one final time.

The projective correspondence sector is a rational linear span.  On the
canonical spine source, which is already an actual cycle class, the canonical
cohomological realization of a rationally scaled native kernel scales exactly
by the same rational scalar.  Therefore any nonzero projective separator
reading can be normalized to the specific nonzero Lefschetz-tomography moment
selected by the ghost.

Thus the horizontal geometric frontier is no longer an exact matrix unit, an
exact basis vector, or even an exact tomography scalar.  It is the scalar
visibility statement:

  some genuine projective correspondence has nonzero separator reading on the
  canonical algebraic spine source.

A surviving ghost forces every such reading to zero.  Proving projective
visibility from independent geometry therefore closes the transformed attack.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeProjectiveDetectorVisibility

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeProjectiveCorrespondenceAlgebra
open GSTClassicalHodgeProjectiveCorrespondenceCosmicRealization
open GSTClassicalHodgeSynchronizedDefectOrbit
open GSTClassicalHodgeGhostSpineCosmicLeak
open GSTClassicalHodgeOmniversalSeparatorGhostCrown
open GSTClassicalHodgeProjectiveDetectorMomentCollision

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Rational scaling stays inside the genuine projective-correspondence
operator sector. -/
noncomputable def scaleProjectiveKernel
    {p : Nat}
    (q : ℚ)
    (K : ProjectiveNativeKernel V p) :
    ProjectiveNativeKernel V p :=
  ⟨q • K.1, smul_mem V p q K.2⟩

/-- On any actual cycle class, the cohomological realization of a scaled
projective kernel scales exactly.  No statement is made about arbitrary
ambient classes outside the cycle-class range. -/
theorem scaled_projectivePair_on_cycleClass
    (G : GeometricCycleClassSpine V H)
    {p : Nat}
    (q : ℚ)
    (K : ProjectiveNativeKernel V p)
    (Z : codimensionCycles V.X p) :
    (projectiveCorrespondencePair G (scaleProjectiveKernel q K)).cohomologyOperator
        (H.cycleClass p Z) =
      q • (projectiveCorrespondencePair G K).cohomologyOperator
        (H.cycleClass p Z) := by
  have hs :=
    (projectiveCorrespondencePair G (scaleProjectiveKernel q K)).cycleClass_cycleOperator Z
  have hk :=
    (projectiveCorrespondencePair G K).cycleClass_cycleOperator Z
  calc
    (projectiveCorrespondencePair G (scaleProjectiveKernel q K)).cohomologyOperator
        (H.cycleClass p Z)
        = H.cycleClass p
            ((projectiveCorrespondencePair G (scaleProjectiveKernel q K)).cycleOperator Z) := by
              symm
              exact hs
    _ = H.cycleClass p (q • K.1 Z) := by rfl
    _ = q • H.cycleClass p (K.1 Z) := by simp
    _ = q • (projectiveCorrespondencePair G K).cohomologyOperator
          (H.cycleClass p Z) := by rw [hk]

/-- Scaling law specialized to the canonical algebraic spine seed selected by
a ghost. -/
theorem scaled_projectivePair_on_ghostSpine
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (E : OmniversalSeparatorGhost G)
    (q : ℚ)
    (K : ProjectiveNativeKernel V E.weight) :
    (projectiveCorrespondencePair G (scaleProjectiveKernel q K)).cohomologyOperator
        (ghostSpineSeed G M E).hodge.1 =
      q • (projectiveCorrespondencePair G K).cohomologyOperator
        (ghostSpineSeed G M E).hodge.1 := by
  rw [← (ghostSpineSeed G M E).class_eq]
  exact scaled_projectivePair_on_cycleClass G q K (ghostSpineSeed G M E).cycle

/-- Minimal horizontal visibility datum: one genuine projective kernel gives a
nonzero separator reading on the canonical spine source. -/
structure ProjectiveDetectorVisible
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (E : OmniversalSeparatorGhost G) where
  kernel : ProjectiveNativeKernel V E.weight
  detector_nonzero :
    E.separator.detector
      ((projectiveCorrespondencePair G kernel).cohomologyOperator
        (ghostSpineSeed G M E).hodge.1) ≠ 0

/-- Any nonzero projective detector reading can be rescaled to the exact
nonzero tomography moment selected by the ghost. -/
noncomputable def ProjectiveDetectorVisible.toMomentHit
    {G : GeometricCycleClassSpine V H}
    {M : NativeMassCycleClassBridge V H}
    {E : OmniversalSeparatorGhost G}
    (R : ProjectiveDetectorVisible G M E) :
    ProjectiveDetectorMomentHit G M E := by
  let v : ℚ :=
    E.separator.detector
      ((projectiveCorrespondencePair G R.kernel).cohomologyOperator
        (ghostSpineSeed G M E).hodge.1)
  let m : ℚ :=
    GSTClassicalHodgeLefschetzTomography.lefschetzTomography
      (GSTClassicalHodgeLefschetzTomography.supportCoordinateVector
        (GSTClassicalHodgeFiberedCosmology.fiberedWeightCoordinates
          V H E.weight
          (GSTClassicalHodgeFiberedCosmology.classicalHodgeBasis
            V H E.weight E.sheet)))
      (ghostMomentIndex G E)
  have hv : v ≠ 0 := by
    simpa [v] using R.detector_nonzero
  let q : ℚ := m / v
  refine {
    kernel := scaleProjectiveKernel q R.kernel
    detector_eq_moment := ?_
  }
  rw [scaled_projectivePair_on_ghostSpine G M E q R.kernel]
  rw [map_smul]
  change q * v = m
  dsimp [q]
  field_simp [hv]

/-- A surviving ghost has no nonzero projective detector visibility. -/
theorem no_projectiveDetectorVisible
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (E : OmniversalSeparatorGhost G) :
    IsEmpty (ProjectiveDetectorVisible G M E) := by
  refine ⟨?_⟩
  intro R
  exact R.detector_nonzero
    (ghost_detector_kills_projective_spine_image G M E R.kernel)

/-- **VISIBILITY-LEVEL HODGE CLOSURE.**
It is enough that every possible ghost admit one genuine projective kernel with
a nonzero separator reading on the canonical spine.  Exact GST operator
realization and exact target-vector identities have disappeared completely. -/
theorem bigradedBettiHodge_of_projectiveDetectorVisibility
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (visible : ∀ E : OmniversalSeparatorGhost G,
      Nonempty (ProjectiveDetectorVisible G M E)) :
    BigradedBettiHodgeStatement V H := by
  by_contra hnot
  rcases (not_hodge_iff_nonempty_omniversalSeparatorGhost G).mp hnot with ⟨E⟩
  exact (no_projectiveDetectorVisible G M E).false
    (Classical.choice (visible E))

#check scaleProjectiveKernel
#check scaled_projectivePair_on_cycleClass
#check scaled_projectivePair_on_ghostSpine
#check ProjectiveDetectorVisible
#check ProjectiveDetectorVisible.toMomentHit
#check no_projectiveDetectorVisible
#check bigradedBettiHodge_of_projectiveDetectorVisibility

#print axioms scaled_projectivePair_on_cycleClass
#print axioms scaled_projectivePair_on_ghostSpine
#print axioms ProjectiveDetectorVisible.toMomentHit
#print axioms no_projectiveDetectorVisible
#print axioms bigradedBettiHodge_of_projectiveDetectorVisibility

end GSTClassicalHodgeProjectiveDetectorVisibility
