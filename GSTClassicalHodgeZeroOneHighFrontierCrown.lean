import GSTClassicalHodgeOneMotionFrontierCrown
import GSTClassicalHodgeWeightOneGenericSeparatorExtinction

/-!
# GST CLASSICAL HODGE — ZERO / ONE / HIGH FRONTIER CROWN

The first two Hodge weights no longer require the same separator-rank input.

* weight 0 already has a nonzero algebraic source from a generic irreducible
  component and projective degree;
* weight 1 now has a nonzero algebraic source from the geometry-proved exact
  generic separator step `0 -> 1`;
* therefore the unresolved ambient separator exactness theorem is needed only
  when the least bad weight is at least two.

This file packages that sharper global frontier.  Every hypothetical minimal
Hodge ghost is split into the three cases `0`, `1`, and `>= 2`.  The first two
are discharged by already-constructed geometric seeds.  Only the high-weight
case still consumes a `PositiveMinimalGhostSuccessor` packet.

Thus no externally supplied separator-exactness statement occurs in weights
zero or one.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeZeroOneHighFrontierCrown

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeMinimalPrimitiveSeparatorGhost
open GSTClassicalHodgeNativeGeneratorNaturality
open GSTClassicalHodgeUniversalTwoSlotNativeClosure
open GSTClassicalHodgeLocalSeedBareLefschetzExtinction
open GSTClassicalHodgeZeroWeightLocalSeed
open GSTClassicalHodgeOneMotionFrontierCrown
open GSTClassicalHodgeWeightOneGenericSeparatorExtinction
open GSTClassicalHodgeProjectiveDegreeTrace

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- **SHARPENED ONE-MOTION GLOBAL FRONTIER.**
Separator ambient-rank exactness is no longer an input at minimal weights zero
or one.  Only a least bad weight `>= 2` may still require an exact canonical
separator successor. -/
theorem bigradedBettiHodge_of_zero_one_high_frontier
    [Nonempty V.X]
    [IrreducibleSpace V.X]
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (x0 : CodimensionPoint V.X 0)
    (hlive0 : ProjectivelyLiveSource V.projective.n
      (V.projective.immersion x0.1))
    (high : ∀ M : MinimalPrimitiveGhost G,
      2 ≤ M.weight → PositiveMinimalGhostSuccessor G M)
    (hLzero : ∀ M : MinimalPrimitiveGhost G,
      ∀ hM : M.weight = 0,
        HasNativePointLifts
          (p := M.weight) (cl := H.cycleClass M.weight)
          (ambientTwoStepLefschetz
            (zeroWeightLocalSeed G D M hM).sourceIndex M.sheet))
    (hLone : ∀ M : MinimalPrimitiveGhost G,
      ∀ hM : M.weight = 1,
        HasNativePointLifts
          (p := M.weight) (cl := H.cycleClass M.weight)
          (ambientTwoStepLefschetz
            (weightOneLocalSeed G D M hM x0 hlive0).sourceIndex M.sheet))
    (hLhigh : ∀ M : MinimalPrimitiveGhost G,
      ∀ hM : 2 ≤ M.weight,
        HasNativePointLifts
          (p := M.weight) (cl := H.cycleClass M.weight)
          (ambientTwoStepLefschetz
            ((((high M hM).toSeparatorSeed G D M).localSeed G M).sourceIndex)
            M.sheet)) :
    BigradedBettiHodgeStatement V H := by
  by_contra hnot
  let M : MinimalPrimitiveGhost G := minimalPrimitiveGhostOfFailure G hnot
  by_cases h0 : M.weight = 0
  · exact minimalGhost_false_of_zeroWeight_bareLefschetz
      G D M h0 (hLzero M h0)
  · by_cases h1 : M.weight = 1
    · exact minimalGhost_false_of_weightOne_genericSeparator_bareLefschetz
        G D M h1 x0 hlive0 (hLone M h1)
    · have h2 : 2 ≤ M.weight := by omega
      let P : PositiveWeightSeparatorSeed G M :=
        (high M h2).toSeparatorSeed G D M
      exact minimalGhost_false_of_positiveWeight_separator_and_bareLefschetz
        G M P (by simpa [P] using hLhigh M h2)

#check bigradedBettiHodge_of_zero_one_high_frontier
#print axioms bigradedBettiHodge_of_zero_one_high_frontier

end GSTClassicalHodgeZeroOneHighFrontierCrown
