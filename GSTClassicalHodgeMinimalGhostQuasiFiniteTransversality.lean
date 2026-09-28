import GSTClassicalHodgeQuasiFiniteCorrespondenceOperator
import GSTClassicalHodgeMinimalGhostNativeOrbitAnnihilation

/-!
# GST CLASSICAL HODGE — MINIMAL GHOST QUASI-FINITE TRANSVERSALITY

The self-map projective algebra has now been enlarged to genuine multivalued
quasi-finite point correspondences.  A kernel-stable correspondence has an
ambient Betti action derived from its native finite-fibre relation, not supplied
as Hodge data.

For the least-weight primitive ghost, the full classical contradiction again
reduces to one scalar: if one such correspondence sends one algebraic Hodge
source to a state detected nontrivially by the minimal separator, the ghost is
impossible.  No matrix-unit identity and no full correspondence algebra is
required.
-/

set_option maxHeartbeats 90000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeMinimalGhostQuasiFiniteTransversality

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeMinimalPrimitiveSeparatorGhost
open GSTClassicalHodgePrimitiveAlgebraicDefect
open GSTClassicalHodgeQuasiFinitePointCorrespondence
open GSTClassicalHodgeQuasiFiniteCorrespondenceOperator
open GSTClassicalHodgeMinimalGhostNativeOrbitAnnihilation

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- One genuinely multivalued geometric correspondence transverse to the
least-weight ghost on one algebraic source. -/
structure MinimalGhostQuasiFiniteTransverse
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G) where
  correspondence : QuasiFinitePointCorrespondence V.X M.weight
  kernelStable :
    CorrespondenceKernelStable (H := H) correspondence
  source : ClassicalHodgeFiber V H M.weight
  source_algebraic :
    source ∈ AlgebraicHodgeSubspace V H M.weight
  transverse :
    M.separator.detector
      ((operatorPair correspondence kernelStable).cohomologyOperator source.1) ≠ 0

/-- Every kernel-stable quasi-finite correspondence orbit of an algebraic
source is forced into the separator kernel by a surviving minimal ghost. -/
theorem minimalGhost_annihilates_quasiFiniteCorrespondence
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    (C : QuasiFinitePointCorrespondence V.X M.weight)
    (hC : CorrespondenceKernelStable (H := H) C)
    (alpha : ClassicalHodgeFiber V H M.weight)
    (halpha : alpha ∈ AlgebraicHodgeSubspace V H M.weight) :
    M.separator.detector
      ((operatorPair C hC).cohomologyOperator alpha.1) = 0 := by
  exact minimalGhost_annihilates_nativeNatural_image G M
    (operatorPair C hC).cohomologyOperator
    (operatorPair_hasNativePointLifts C hC)
    alpha halpha

/-- **ONE QUASI-FINITE CORRESPONDENCE EXTINCTION.** -/
theorem minimalGhost_false_of_quasiFiniteTransverse
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    (T : MinimalGhostQuasiFiniteTransverse G M) : False := by
  exact T.transverse
    (minimalGhost_annihilates_quasiFiniteCorrespondence G M
      T.correspondence T.kernelStable T.source T.source_algebraic)

/-- Complete Stage-2G landing from one multivalued geometric transverse witness
for every hypothetical least-weight primitive ghost. -/
theorem bigradedBettiHodge_of_minimalGhost_quasiFiniteTransversality
    (G : GeometricCycleClassSpine V H)
    (T : ∀ M : MinimalPrimitiveGhost G,
      Nonempty (MinimalGhostQuasiFiniteTransverse G M)) :
    BigradedBettiHodgeStatement V H := by
  by_contra hnot
  let M : MinimalPrimitiveGhost G := minimalPrimitiveGhostOfFailure G hnot
  exact minimalGhost_false_of_quasiFiniteTransverse G M (T M).some

#check MinimalGhostQuasiFiniteTransverse
#check minimalGhost_annihilates_quasiFiniteCorrespondence
#check minimalGhost_false_of_quasiFiniteTransverse
#check bigradedBettiHodge_of_minimalGhost_quasiFiniteTransversality

#print axioms minimalGhost_annihilates_quasiFiniteCorrespondence
#print axioms minimalGhost_false_of_quasiFiniteTransverse
#print axioms bigradedBettiHodge_of_minimalGhost_quasiFiniteTransversality

end GSTClassicalHodgeMinimalGhostQuasiFiniteTransversality
