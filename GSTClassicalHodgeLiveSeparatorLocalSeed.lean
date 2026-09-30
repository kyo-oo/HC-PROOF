import GSTClassicalHodgeSeparatorAmbientCoheightExact
import GSTClassicalHodgeLocalSeedBareLefschetzExtinction
import GSTClassicalHodgeSingleStateFlagNormalExtinction

/-!
# GST CLASSICAL HODGE — LIVE SEPARATOR LOCAL SEED

The positive-weight local-seed layer previously stored ambient exactness of the
canonical separator successor as an independent field of
`PositiveWeightSeparatorSeed`.

On the single-separator branch that field is no longer geometric input:
`separator_successor_ambient_coheight_exact` derives it from smooth projective
regular-local geometry and projective liveness of the source.

This module removes that redundant burden from the minimal-ghost route.  A
positive minimal weight written as `p+1`, one projectively live codimension-p
source, and the genuine projective-degree trace semantics already manufacture
the nonzero algebraic Hodge local seed consumed by both the bare-Lefschetz and
the single-state flag-normal extinction theorems.

Nothing here assumes a Hodge representative for the obstructed sheet.  The
remaining flag-normal comparison is left explicit and isolated.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeMinimalPrimitiveSeparatorGhost
open GSTClassicalHodgeProjectiveDegreeTrace
open GSTClassicalHodgeLocalSeedBareLefschetzExtinction
open GSTClassicalHodgeSingleStateFlagNormalExtinction
open GSTClassicalHodgeSeparatorAmbientCoheightExact

namespace GSTClassicalHodgeLiveSeparatorLocalSeed

variable {V : SmoothProjectiveComplexScheme}
variable {H : GSTGeometricRealizationStage2G.HodgeBigradedBettiData V}

/-- A projectively live source automatically supplies the exactness field of
`PositiveWeightSeparatorSeed`; it is no longer an independent assumption. -/
noncomputable def positiveWeightSeparatorSeedOfLive
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    (p : Nat)
    (hweight : M.weight = p + 1)
    (x : CodimensionPoint V.X p)
    (hlive : ProjectivelyLiveSource V.projective.n (V.projective.immersion x.1))
    (D : ProjectiveDegreeTraceSemantics V H) :
    PositiveWeightSeparatorSeed G M where
  prevWeight := p
  weight_eq := hweight
  sourcePoint := x
  source_live := hlive
  successor_exact := separator_successor_ambient_coheight_exact V p x hlive
  degreeTrace := D

/-- The live separator therefore manufactures the exact nonzero algebraic
local seed used by the minimal-ghost contradiction. -/
noncomputable def liveSeparatorLocalSeed
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    (p : Nat)
    (hweight : M.weight = p + 1)
    (x : CodimensionPoint V.X p)
    (hlive : ProjectivelyLiveSource V.projective.n (V.projective.immersion x.1))
    (D : ProjectiveDegreeTraceSemantics V H) :
    MinimalGhostLocalSeed G M :=
  (positiveWeightSeparatorSeedOfLive G M p hweight x hlive D).localSeed G M

/-- Bare two-step GST extinction with the separator exactness input completely
removed.  The only remaining non-geometric obligation is the native lift of
the one two-slot motion selected by the local seed. -/
theorem minimalGhost_false_of_positiveWeight_liveSeparator_and_bareLefschetz
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    (p : Nat)
    (hweight : M.weight = p + 1)
    (x : CodimensionPoint V.X p)
    (hlive : ProjectivelyLiveSource V.projective.n (V.projective.immersion x.1))
    (D : ProjectiveDegreeTraceSemantics V H)
    (hL : GSTClassicalHodgeNativeGeneratorNaturality.HasNativePointLifts
      (p := M.weight) (cl := H.cycleClass M.weight)
      (GSTClassicalHodgeUniversalTwoSlotNativeClosure.ambientTwoStepLefschetz
        (liveSeparatorLocalSeed G M p hweight x hlive D).sourceIndex M.sheet)) : False := by
  exact minimalGhost_false_of_localSeed_bareLefschetz
    G M (liveSeparatorLocalSeed G M p hweight x hlive D) hL

/-- **LIVE-SEPARATOR / SINGLE-STATE FLAG COLLISION.**

After the pure separator geometry and degree trace have supplied the local
algebraic seed, one genuine principal-cut flag normal matching the bare GST
`L^2` action on that single seed destroys the minimal ghost.  In particular,
ambient separator exactness is not part of the final flag-normal obligation. -/
theorem minimalGhost_false_of_positiveWeight_liveSeparator_and_flagNormal
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    (p : Nat)
    (hweight : M.weight = p + 1)
    (x : CodimensionPoint V.X p)
    (hlive : ProjectivelyLiveSource V.projective.n (V.projective.immersion x.1))
    (D : ProjectiveDegreeTraceSemantics V H)
    (F : SingleStateFlagNormalLefschetzRealization
      G M (liveSeparatorLocalSeed G M p hweight x hlive D)) : False := by
  exact F.minimalGhost_false
    G M (liveSeparatorLocalSeed G M p hweight x hlive D)

#check positiveWeightSeparatorSeedOfLive
#check liveSeparatorLocalSeed
#check minimalGhost_false_of_positiveWeight_liveSeparator_and_bareLefschetz
#check minimalGhost_false_of_positiveWeight_liveSeparator_and_flagNormal

#print axioms positiveWeightSeparatorSeedOfLive
#print axioms liveSeparatorLocalSeed
#print axioms minimalGhost_false_of_positiveWeight_liveSeparator_and_bareLefschetz
#print axioms minimalGhost_false_of_positiveWeight_liveSeparator_and_flagNormal

end GSTClassicalHodgeLiveSeparatorLocalSeed
