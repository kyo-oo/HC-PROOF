import GSTClassicalHodgePrimitiveAlgebraicDefect
import GSTClassicalHodgeGeometryFirstTwoGenerator
import GSTClassicalHodgeLimitlessSpinePropagation

/-!
# GST CLASSICAL HODGE — MINIMAL GHOST SINGLE-TRANSPORT EXTINCTION

The primitive-defect reduction leaves one least-weight separator ghost.  Full
matrix-unit externalization is far stronger than is needed to kill that ghost.

Fix its detected basis sheet `j`.  It is enough to find ONE algebraic Hodge
state `a`, ONE live basis coordinate `i` of `a`, and ONE geometry-first GST
transport from `i` to `j`.  The verified geometry-first word is native-natural,
so it preserves the actual algebraic Hodge subspace.  On the Hodge fiber the
same word is exactly the matrix unit `E_{i,j}`.  Hence its value on `a` is

  coordinate_i(a) • basis_j.

The source coordinate is nonzero, while the minimal separator detects
`basis_j`.  Therefore the separator detects the transported state.  But the
transported state is algebraic, so the same separator must annihilate it.
Contradiction.

Thus the least-weight primitive obstruction requires neither a realization of
all matrix units nor a realization for every target.  One live algebraic source
and one targeted geometry-first transport suffice.
-/

set_option maxHeartbeats 90000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeMinimalGhostSingleTransportExtinction

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeMinimalPrimitiveSeparatorGhost
open GSTClassicalHodgeMinimalAlgebraicPrimitiveQuotient
open GSTClassicalHodgePrimitiveAlgebraicDefect
open GSTClassicalHodgeGeometryFirstTwoGenerator
open GSTClassicalHodgeLimitlessSpinePropagation

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Minimal data needed to extinguish one least-weight primitive ghost:
one algebraic Hodge source, one live coordinate of that source, and one
genuine geometry-first GST transport into the detected ghost sheet. -/
structure MinimalGhostTargetTransport
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G) where
  source : ClassicalHodgeFiber V H M.weight
  sourceIndex : ClassicalHodgeBasisIndex V H M.weight
  sourceCoefficient_ne_zero : hodgeCoordinate sourceIndex source ≠ 0
  source_algebraic : source ∈ AlgebraicHodgeSubspace V H M.weight
  transport : GeometryFirstTwoGenerator
    (V := V) (H := H) sourceIndex M.sheet

/-- **ONE-TRANSPORT EXTINCTION.**
A least-weight primitive separator cannot coexist with one algebraic source
whose live coordinate can be transported geometrically to the detected sheet. -/
theorem minimalGhost_false_of_targetTransport
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    (T : MinimalGhostTargetTransport G M) : False := by
  have halg :
      hodgeMatrixUnit T.sourceIndex M.sheet T.source ∈
        AlgebraicHodgeSubspace V H M.weight :=
    T.transport.matrixUnit_mem_algebraic T.source T.source_algebraic
  have hzero :=
    AlgebraicHodgeSubspace_le_minimalGhostHodgeDetector_kernel G M halg
  have hmul :
      hodgeCoordinate T.sourceIndex T.source *
          M.separator.detector
            (classicalHodgeBasis V H M.weight M.sheet).1 = 0 := by
    simpa [minimalGhostHodgeDetector, hodgeMatrixUnit_apply] using hzero
  exact
    (mul_ne_zero T.sourceCoefficient_ne_zero M.separator.detects_basis) hmul

/-- The canonical projective spine supplies the algebraic source automatically.
Once it is nonzero, any one of its live coordinates may be used as the source
of the single required transport. -/
noncomputable def spineTargetTransport
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    (i : ClassicalHodgeBasisIndex V H M.weight)
    (hi : hodgeCoordinate i (spineHodgeSeed G M.weight) ≠ 0)
    (R : GeometryFirstTwoGenerator (V := V) (H := H) i M.sheet) :
    MinimalGhostTargetTransport G M where
  source := spineHodgeSeed G M.weight
  sourceIndex := i
  sourceCoefficient_ne_zero := hi
  source_algebraic := spineHodgeSeed_algebraic G M.weight
  transport := R

/-- A nonzero canonical spine plus one geometry-first transport from any live
spine coordinate to the ghost target already contradicts the minimal ghost. -/
theorem minimalGhost_false_of_spine_targetTransport
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    (hspine : spineHodgeSeed G M.weight ≠ 0)
    (R : ∀ i : ClassicalHodgeBasisIndex V H M.weight,
      hodgeCoordinate i (spineHodgeSeed G M.weight) ≠ 0 →
        GeometryFirstTwoGenerator (V := V) (H := H) i M.sheet) : False := by
  obtain ⟨i, hi⟩ := exists_nonzero_hodgeCoordinate hspine
  exact minimalGhost_false_of_targetTransport G M
    (spineTargetTransport G M i hi (R i hi))

/-- **MINIMAL-GHOST TARGETED-TRANSPORT HODGE CRITERION.**
To close Stage-2G it is enough to extinguish each hypothetical least-weight
ghost with one targeted transport.  This is strictly narrower than asking for
geometry-first realizations of every ordered pair in every Hodge weight. -/
theorem bigradedBettiHodge_of_minimalGhost_targetTransports
    (G : GeometricCycleClassSpine V H)
    (T : ∀ M : MinimalPrimitiveGhost G,
      Nonempty (MinimalGhostTargetTransport G M)) :
    BigradedBettiHodgeStatement V H := by
  by_contra hnot
  let M : MinimalPrimitiveGhost G := minimalPrimitiveGhostOfFailure G hnot
  exact minimalGhost_false_of_targetTransport G M (T M).some

/-- Spine-specialized family criterion: only the least bad target sheet is
requested, and only from a live coordinate of the canonical algebraic spine. -/
theorem bigradedBettiHodge_of_minimalGhost_spine_targetTransports
    (G : GeometricCycleClassSpine V H)
    (hspine : ∀ M : MinimalPrimitiveGhost G,
      spineHodgeSeed G M.weight ≠ 0)
    (R : ∀ M : MinimalPrimitiveGhost G,
      ∀ i : ClassicalHodgeBasisIndex V H M.weight,
      hodgeCoordinate i (spineHodgeSeed G M.weight) ≠ 0 →
        GeometryFirstTwoGenerator (V := V) (H := H) i M.sheet) :
    BigradedBettiHodgeStatement V H := by
  by_contra hnot
  let M : MinimalPrimitiveGhost G := minimalPrimitiveGhostOfFailure G hnot
  exact minimalGhost_false_of_spine_targetTransport G M
    (hspine M) (R M)

/-- A conserved spine charge discharges the nonvanishing side entirely; the
only remaining input is one targeted geometry-first transport from a live
spine coordinate into each hypothetical minimal ghost sheet. -/
theorem bigradedBettiHodge_of_conservedSpine_and_minimalTargetTransport
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge G)
    (R : ∀ M : MinimalPrimitiveGhost G,
      ∀ i : ClassicalHodgeBasisIndex V H M.weight,
      hodgeCoordinate i (spineHodgeSeed G M.weight) ≠ 0 →
        GeometryFirstTwoGenerator (V := V) (H := H) i M.sheet) :
    BigradedBettiHodgeStatement V H := by
  exact bigradedBettiHodge_of_minimalGhost_spine_targetTransports G
    (fun M => D.spineHodgeSeed_ne_zero M.weight) R

#check MinimalGhostTargetTransport
#check minimalGhost_false_of_targetTransport
#check spineTargetTransport
#check minimalGhost_false_of_spine_targetTransport
#check bigradedBettiHodge_of_minimalGhost_targetTransports
#check bigradedBettiHodge_of_minimalGhost_spine_targetTransports
#check bigradedBettiHodge_of_conservedSpine_and_minimalTargetTransport

#print axioms minimalGhost_false_of_targetTransport
#print axioms minimalGhost_false_of_spine_targetTransport
#print axioms bigradedBettiHodge_of_minimalGhost_targetTransports
#print axioms bigradedBettiHodge_of_minimalGhost_spine_targetTransports
#print axioms bigradedBettiHodge_of_conservedSpine_and_minimalTargetTransport

end GSTClassicalHodgeMinimalGhostSingleTransportExtinction
