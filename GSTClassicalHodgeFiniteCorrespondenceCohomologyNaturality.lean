import GSTClassicalHodgeFiniteClosedCorrespondenceOperator
import GSTClassicalHodgeCycleOperatorNaturality
import GSTClassicalHodgeGhostSpineCosmicLeak
import GSTClassicalHodgeTomographyDefectSplice

/-!
# GST CLASSICAL HODGE — FINITE-CORRESPONDENCE BETTI NATURALITY

The native finite-correspondence operator is already constructed from a genuine
closed subscheme of `X × X` with finite left fibers.  What was still missing
was the ordinary cohomological push-pull square for that operator.

This file exposes precisely that geometric semantic layer.  It does not ask a
correspondence to realize a GST matrix unit, a Hodge basis vector, or any Hodge
surjectivity statement.  It only records the standard functorial equation

  cl(K_* Z) = K_* cl(Z)

for the independently constructed native correspondence operator.

Once that square is available, the correspondence becomes a genuine
`CycleClassOperatorPair`, so all zero-defect and separator machinery applies
without adding any Hodge-specific realization hypothesis.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeFiniteCorrespondenceCohomologyNaturality

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiniteClosedCorrespondence
open GSTClassicalHodgeFiniteClosedCorrespondenceOperator
open GSTClassicalHodgeCycleOperatorNaturality
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeSynchronizedDefectOrbit
open GSTClassicalHodgeGhostSpineCosmicLeak
open GSTClassicalHodgeOmniversalSeparatorGhostCrown
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeAtomicAnnihilator
open GSTClassicalHodgeLimitlessSpinePropagation

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Ordinary Betti push-pull naturality for one genuine finite closed
correspondence.  This is a geometric cycle-class law only; it contains no
Hodge-basis or GST target equation. -/
structure FiniteCorrespondenceBettiNaturality
    (K : FiniteClosedCorrespondence V)
    (p : Nat) where
  cohomologyOperator :
    RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
      RationalSingularCohomology H.analytification (2 * p)
  naturality :
    ∀ Z : codimensionCycles V.X p,
      H.cycleClass p (nativeCorrespondenceOperator K p Z) =
        cohomologyOperator (H.cycleClass p Z)

namespace FiniteCorrespondenceBettiNaturality

/-- The genuine native finite-correspondence operator and its standard Betti
push-pull action form an exact cycle-class operator pair. -/
noncomputable def toOperatorPair
    {K : FiniteClosedCorrespondence V}
    (N : FiniteCorrespondenceBettiNaturality (H := H) K p) :
    CycleClassOperatorPair V H p where
  cycleOperator := nativeCorrespondenceOperator K p
  cohomologyOperator := N.cohomologyOperator
  cycleClass_natural := by
    ext Z
    exact N.naturality Z

/-- Kernel preservation is no longer a separate hypothesis once genuine
correspondence naturality is known. -/
theorem kernelStable
    {K : FiniteClosedCorrespondence V}
    (N : FiniteCorrespondenceBettiNaturality (H := H) K p)
    (Z : codimensionCycles V.X p)
    (hZ : H.cycleClass p Z = 0) :
    H.cycleClass p (nativeCorrespondenceOperator K p Z) = 0 := by
  rw [N.naturality, hZ]
  exact N.cohomologyOperator.map_zero

end FiniteCorrespondenceBettiNaturality

/-- Every genuine finite-correspondence image of the canonical algebraic spine
is still an actual cycle class, so an omniversal ghost separator annihilates
its Betti push-pull image. -/
theorem ghost_detector_kills_finiteCorrespondence_spine_image
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (E : OmniversalSeparatorGhost G)
    (K : FiniteClosedCorrespondence V)
    (N : FiniteCorrespondenceBettiNaturality (H := H) K E.weight) :
    E.separator.detector
      (N.cohomologyOperator (ghostSpineSeed G M E).hodge.1) = 0 := by
  let S := ghostSpineSeed G M E
  have hnat := N.naturality S.cycle
  rw [S.class_eq] at hnat
  have hrange :
      H.cycleClass E.weight
          (nativeCorrespondenceOperator K E.weight S.cycle) ∈
        LinearMap.range (H.cycleClass E.weight) := by
    exact ⟨nativeCorrespondenceOperator K E.weight S.cycle, rfl⟩
  have hatomic :
      H.cycleClass E.weight
          (nativeCorrespondenceOperator K E.weight S.cycle) ∈
        pointCycleClassSpan E.weight (H.cycleClass E.weight) := by
    rw [← smoothProjective_cycleClass_range_eq_atomic_span V H E.weight]
    exact hrange
  have hker :
      pointCycleClassSpan E.weight (H.cycleClass E.weight) ≤
        LinearMap.ker E.separator.detector :=
    (annihilatesPointCycles_iff_atomicSpan_le_ker
      E.weight (H.cycleClass E.weight) E.separator.detector).mp
      E.separator.annihilates_atoms
  have hz := hker hatomic
  rw [LinearMap.mem_ker] at hz
  rw [← hnat]
  exact hz

/-- Scalar visibility datum for the full finite-correspondence universe.  The
correspondence and Betti naturality are entirely geometric; only the final
statement asks whether the ghost detector sees its action on the canonical
spine source. -/
structure FiniteCorrespondenceDetectorVisible
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (E : OmniversalSeparatorGhost G) where
  correspondence : FiniteClosedCorrespondence V
  bettiNaturality :
    FiniteCorrespondenceBettiNaturality
      (H := H) correspondence E.weight
  detector_nonzero :
    E.separator.detector
      (bettiNaturality.cohomologyOperator
        (ghostSpineSeed G M E).hodge.1) ≠ 0

/-- A surviving ghost blacks out even the enlarged finite-correspondence
universe once ordinary Betti push-pull naturality is imposed. -/
theorem no_finiteCorrespondenceDetectorVisible
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (E : OmniversalSeparatorGhost G) :
    IsEmpty (FiniteCorrespondenceDetectorVisible G M E) := by
  refine ⟨?_⟩
  intro R
  exact R.detector_nonzero
    (ghost_detector_kills_finiteCorrespondence_spine_image
      G M E R.correspondence R.bettiNaturality)

/-- The corresponding scalar closure criterion over genuine closed
correspondences.  This remains a criterion: the substantive geometric task is
to derive nonzero visibility from an independent correspondence computation,
not to store it in the semantic data. -/
theorem bigradedBettiHodge_of_finiteCorrespondenceDetectorVisibility
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (visible : ∀ E : OmniversalSeparatorGhost G,
      Nonempty (FiniteCorrespondenceDetectorVisible G M E)) :
    BigradedBettiHodgeStatement V H := by
  by_contra hnot
  rcases (not_hodge_iff_nonempty_omniversalSeparatorGhost G).mp hnot with ⟨E⟩
  exact (no_finiteCorrespondenceDetectorVisible G M E).false
    (Classical.choice (visible E))

#check FiniteCorrespondenceBettiNaturality
#check FiniteCorrespondenceBettiNaturality.toOperatorPair
#check FiniteCorrespondenceBettiNaturality.kernelStable
#check ghost_detector_kills_finiteCorrespondence_spine_image
#check FiniteCorrespondenceDetectorVisible
#check no_finiteCorrespondenceDetectorVisible
#check bigradedBettiHodge_of_finiteCorrespondenceDetectorVisibility

#print axioms FiniteCorrespondenceBettiNaturality.toOperatorPair
#print axioms FiniteCorrespondenceBettiNaturality.kernelStable
#print axioms ghost_detector_kills_finiteCorrespondence_spine_image
#print axioms no_finiteCorrespondenceDetectorVisible
#print axioms bigradedBettiHodge_of_finiteCorrespondenceDetectorVisibility

end GSTClassicalHodgeFiniteCorrespondenceCohomologyNaturality
