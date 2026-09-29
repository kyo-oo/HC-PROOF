import GSTClassicalHodgeZeroOneHighFrontierCrown
import GSTClassicalHodgeSingleStateBareLefschetzExtinction

/-!
# GST CLASSICAL HODGE — ZERO / ONE / HIGH SINGLE-STATE CROWN

The zero/one/high frontier removed canonical separator ambient-rank exactness
from the first two Hodge weights, but still carried the older global
`HasNativePointLifts` interface for the bare two-slot GST `L^2` motion.

The single-state extinction theorem proves that this is stronger than needed:
for the one local algebraic seed attached to a hypothetical minimal primitive
ghost, it is enough that its single bare-`L^2` image lies in the actual atomic
cycle-class span.

This file splices those two reductions.  A hypothetical least Hodge failure is
split into weights `0`, `1`, and `>= 2` exactly as before.  In every case the
contradiction consumes only one concrete source state and one concrete image.
No behavior of the ambient `L^2` operator on any other class is assumed.

Thus the remaining Hodge landing is reduced to two genuinely local geometric
obligations at a hypothetical high minimal weight:

* produce one nonzero algebraic local seed (currently supplied by one exact
  canonical separator successor in the preceding codimension);
* prove algebraicity of one explicit bare two-slot `L^2` image of that seed.

No Hodge-surjectivity hypothesis, global operator naturality, arbitrary basis
cycle choice, or all-successor exactness statement is introduced.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeZeroOneHighSingleStateCrown

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeMinimalPrimitiveSeparatorGhost
open GSTClassicalHodgeUniversalTwoSlotNativeClosure
open GSTClassicalHodgeLocalSeedBareLefschetzExtinction
open GSTClassicalHodgeZeroWeightLocalSeed
open GSTClassicalHodgeOneMotionFrontierCrown
open GSTClassicalHodgeWeightOneGenericSeparatorExtinction
open GSTClassicalHodgeProjectiveDegreeTrace
open GSTClassicalHodgeSingleStateBareLefschetzExtinction

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- **SHARP SINGLE-STATE GLOBAL FRONTIER.**

Weights zero and one use the already-constructed geometric seeds.  A least bad
weight at least two uses the existing one-successor seed packet.  In all three
cases, however, the only Lefschetz-side input is algebraicity of the unique
bare-`L^2` image actually evaluated by the separator contradiction.

This strictly weakens `bigradedBettiHodge_of_zero_one_high_frontier`: no
`HasNativePointLifts` law is required in any branch. -/
theorem bigradedBettiHodge_of_zero_one_high_singleState
    [Nonempty V.X]
    [IrreducibleSpace V.X]
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (x0 : CodimensionPoint V.X 0)
    (hlive0 : ProjectivelyLiveSource V.projective.n
      (V.projective.immersion x0.1))
    (high : ∀ M : MinimalPrimitiveGhost G,
      2 ≤ M.weight → PositiveMinimalGhostSuccessor G M)
    (hzero : ∀ M : MinimalPrimitiveGhost G,
      ∀ hM : M.weight = 0,
        ambientTwoStepLefschetz
            (zeroWeightLocalSeed G D M hM).sourceIndex M.sheet
            (zeroWeightLocalSeed G D M hM).source.1 ∈
          pointCycleClassSpan M.weight (H.cycleClass M.weight))
    (hone : ∀ M : MinimalPrimitiveGhost G,
      ∀ hM : M.weight = 1,
        ambientTwoStepLefschetz
            (weightOneLocalSeed G D M hM x0 hlive0).sourceIndex M.sheet
            (weightOneLocalSeed G D M hM x0 hlive0).source.1 ∈
          pointCycleClassSpan M.weight (H.cycleClass M.weight))
    (hhigh : ∀ M : MinimalPrimitiveGhost G,
      ∀ hM : 2 ≤ M.weight,
        let P := (high M hM).toSeparatorSeed G D M
        let S := P.localSeed G M
        ambientTwoStepLefschetz S.sourceIndex M.sheet S.source.1 ∈
          pointCycleClassSpan M.weight (H.cycleClass M.weight)) :
    BigradedBettiHodgeStatement V H := by
  by_contra hnot
  let M : MinimalPrimitiveGhost G := minimalPrimitiveGhostOfFailure G hnot
  by_cases h0 : M.weight = 0
  · exact minimalGhost_false_of_localSeed_bareLefschetz_image_algebraic
      G M (zeroWeightLocalSeed G D M h0) (hzero M h0)
  · by_cases h1 : M.weight = 1
    · exact minimalGhost_false_of_localSeed_bareLefschetz_image_algebraic
        G M (weightOneLocalSeed G D M h1 x0 hlive0) (hone M h1)
    · have h2 : 2 ≤ M.weight := by omega
      let P : PositiveWeightSeparatorSeed G M :=
        (high M h2).toSeparatorSeed G D M
      let S : MinimalGhostLocalSeed G M := P.localSeed G M
      exact minimalGhost_false_of_localSeed_bareLefschetz_image_algebraic
        G M S (by simpa [P, S] using hhigh M h2)

#check bigradedBettiHodge_of_zero_one_high_singleState
#print axioms bigradedBettiHodge_of_zero_one_high_singleState

end GSTClassicalHodgeZeroOneHighSingleStateCrown
