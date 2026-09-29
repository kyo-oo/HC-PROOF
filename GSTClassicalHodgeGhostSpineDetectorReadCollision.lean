import GSTClassicalHodgeGhostSpineCosmicLeak

/-!
# GST CLASSICAL HODGE — GHOST-SPINE DETECTOR-READ COLLISION

The canonical cosmic leak previously showed that a Hodge failure produces one
specific GST spine-to-ghost state that cannot be realized exactly by any
verified graded geometric program.

Exact state realization is much stronger than the contradiction actually
needs.

For an omniversal separator ghost `E`, every verified graded geometric program
applied to the canonical algebraic spine seed remains in the genuine geometric
program orbit.  That orbit lies in the actual cycle-class range, hence in the
atomic point-cycle span.  The ghost separator annihilates that entire span.
Therefore every genuine program output has separator read exactly zero.

By contrast, the already-proved canonical GST spine-to-ghost two-slot word has
nonzero separator read.

Consequently it is enough to externalize a *single scalar observable*:
geometry need only produce one verified program whose separator read agrees
with the separator read of the GST two-slot output.  No equality of Hodge
vectors, no target-basis realization, no matrix-unit realization, and no
all-pairs operator package is required.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeGhostSpineDetectorReadCollision

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeAtomicAnnihilator
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeLimitlessSpinePropagation
open GSTClassicalHodgeGradedGeometricProgramOrbit
open GSTClassicalHodgeGradedGeometricOrbitAlgebra
open GSTClassicalHodgeOmniversalSeparatorGhostCrown
open GSTClassicalHodgeGhostSpineCosmicLeak
open GSTClassicalHodgeUniversalTwoSlotSaturation
open GSTClassicalHodgeRankFreePrimitiveGeneration
open GSTClassicalHodgeAugmentedTargetWindow

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Every genuine graded-program output from the canonical spine seed is
invisible to the omniversal ghost separator. -/
theorem program_on_ghostSpine_detector_eq_zero
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (E : OmniversalSeparatorGhost G)
    (P : GradedGeometricProgram V E.weight E.weight) :
    E.separator.detector
      (P.cohomologyEval G (ghostSpineSeed G M E).hodge.1) = 0 := by
  have hsource :
      (ghostSpineSeed G M E).hodge.1 ∈
        geometricProgramOrbitModule G E.weight :=
    ghostSpineSeed_mem_orbit G M E
  have himage :
      P.cohomologyEval G (ghostSpineSeed G M E).hodge.1 ∈
        geometricProgramOrbitModule G E.weight :=
    program_maps_geometricProgramOrbitModule G P hsource
  have hrange :
      P.cohomologyEval G (ghostSpineSeed G M E).hodge.1 ∈
        LinearMap.range (H.cycleClass E.weight) :=
    geometricProgramOrbitModule_le_cycleClass_range G E.weight himage
  have hatomic :
      P.cohomologyEval G (ghostSpineSeed G M E).hodge.1 ∈
        pointCycleClassSpan E.weight (H.cycleClass E.weight) := by
    rw [← smoothProjective_cycleClass_range_eq_atomic_span V H E.weight]
    exact hrange
  have hker :
      pointCycleClassSpan E.weight (H.cycleClass E.weight) ≤
        LinearMap.ker E.separator.detector :=
    (annihilatesPointCycles_iff_atomicSpan_le_ker
      E.weight (H.cycleClass E.weight) E.separator.detector).mp
      E.separator.annihilates_atoms
  exact hker hatomic

/-- A deliberately weak externalization target: one verified geometric program
need only reproduce the *separator scalar read* of the canonical GST
spine-to-ghost two-slot transfer. -/
structure GhostSpineDetectorReadRealization
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (E : OmniversalSeparatorGhost G) where
  program : GradedGeometricProgram V E.weight E.weight
  detector_read :
    E.separator.detector
        (program.cohomologyEval G (ghostSpineSeed G M E).hodge.1) =
      E.separator.detector
        (liftFiniteHodgeOperator
          (pairBasisIndex (ghostSpineSeed G M E).sourceIndex E.sheet)
          (forwardArsenalWord sourceSlot targetSlot)
          (ghostSpineSeed G M E).hodge).1

/-- **ONE-SCALAR COLLISION.**
No omniversal ghost can admit even detector-read realization of its canonical
spine-to-ghost GST transfer. -/
theorem no_ghostSpine_detectorReadRealization
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (E : OmniversalSeparatorGhost G) :
    IsEmpty (GhostSpineDetectorReadRealization G M E) := by
  refine ⟨?_⟩
  intro R
  have hzero := program_on_ghostSpine_detector_eq_zero
    G M E R.program
  have hread := R.detector_read
  rw [hzero] at hread
  exact ghostSpine_twoSlot_detector_ne_zero G M E hread.symm

/-- Any exact one-state program realization implies the much weaker detector
read realization and is therefore impossible.  This recovers the earlier
cosmic-leak obstruction through a strictly smaller interface. -/
theorem no_exact_realization_via_detector
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (E : OmniversalSeparatorGhost G) :
    IsEmpty
      { P : GradedGeometricProgram V E.weight E.weight //
        P.cohomologyEval G (ghostSpineSeed G M E).hodge.1 =
          (liftFiniteHodgeOperator
            (pairBasisIndex (ghostSpineSeed G M E).sourceIndex E.sheet)
            (forwardArsenalWord sourceSlot targetSlot)
            (ghostSpineSeed G M E).hodge).1 } := by
  refine ⟨?_⟩
  rintro ⟨P, hP⟩
  let R : GhostSpineDetectorReadRealization G M E := {
    program := P
    detector_read := congrArg E.separator.detector hP
  }
  exact (no_ghostSpine_detectorReadRealization G M E).false R

/-- **DETECTOR-READ HODGE CROWN.**
If the geometry/cosmology supplies the one-scalar detector-read realization for
every possible omniversal separator ghost, no Hodge failure can exist.  This
is strictly weaker than externalizing any complete GST matrix unit. -/
theorem bigradedBettiHodge_of_detectorReadRealizations
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (R : ∀ E : OmniversalSeparatorGhost G,
      Nonempty (GhostSpineDetectorReadRealization G M E)) :
    BigradedBettiHodgeStatement V H := by
  by_contra hnot
  rcases (not_hodge_iff_nonempty_omniversalSeparatorGhost G).mp hnot with ⟨E⟩
  rcases R E with ⟨RE⟩
  exact (no_ghostSpine_detectorReadRealization G M E).false RE

/-- Counterexample normal form at the new minimal interface: every hypothetical
Hodge failure selects a ghost for which even the single canonical detector
scalar cannot be reproduced by any verified graded geometric program. -/
theorem failure_yields_detectorRead_blackout
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (hnot : ¬ BigradedBettiHodgeStatement V H) :
    ∃ E : OmniversalSeparatorGhost G,
      IsEmpty (GhostSpineDetectorReadRealization G M E) := by
  rcases (not_hodge_iff_nonempty_omniversalSeparatorGhost G).mp hnot with ⟨E⟩
  exact ⟨E, no_ghostSpine_detectorReadRealization G M E⟩

#check program_on_ghostSpine_detector_eq_zero
#check GhostSpineDetectorReadRealization
#check no_ghostSpine_detectorReadRealization
#check no_exact_realization_via_detector
#check bigradedBettiHodge_of_detectorReadRealizations
#check failure_yields_detectorRead_blackout

#print axioms program_on_ghostSpine_detector_eq_zero
#print axioms no_ghostSpine_detectorReadRealization
#print axioms bigradedBettiHodge_of_detectorReadRealizations
#print axioms failure_yields_detectorRead_blackout

end GSTClassicalHodgeGhostSpineDetectorReadCollision
