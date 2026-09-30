import GSTClassicalHodgeSingleStateFlagNormalSeparatorRead
import GSTClassicalHodgeLimitlessSingleSeedRecoordination

/-!
# GST CLASSICAL HODGE — SINGLE-STATE FLAG NORMAL LIMITLESS READ

The one-read minimal-ghost frontier should not be tied to the canonical
`N x 1` finite-support chart.  The underlying Hodge vector has finite support,
but the ambient GST cosmology is unbounded and every equal-cardinality world is
only a coordinate presentation.

Using the Poincare-transpose recoordination law, the exact bare `L^2`
separator observable may be evaluated in an arbitrary equal-cardinality GST
world.  Therefore the eventual geometric flag realization is free to choose a
world shape adapted to its incidence geometry; matching the read there is
exactly equivalent to the existing canonical finite-GST Poincare target.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeSingleStateFlagNormalLimitlessRead

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeFiniteSupportChart
open GSTClassicalHodgeLimitlessSeparatorGhost
open GSTClassicalHodgeRecoordinationArsenalCrown
open GSTClassicalHodgeSingleStateFlagNormalSeparatorRead
open GSTClassicalHodgeLimitlessSingleSeedRecoordination
open GSTWorldRecoordinationGroupoid

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Fibered compact address of the one bare two-step Hodge image. -/
noncomputable def bareTwoStepAddress
    (G : GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (M : GSTClassicalHodgeMinimalPrimitiveSeparatorGhost.MinimalPrimitiveGhost G)
    (S : GSTClassicalHodgeLocalSeedBareLefschetzExtinction.MinimalGhostLocalSeed G M) :
    FiberedHodgeAddress V H :=
  fiberedWeightCoordinates V H M.weight (bareTwoStepHodgeImage G M S)

/-- Completed separator probe paired with the bare two-step image. -/
noncomputable def bareSeparatorProbe
    (G : GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (M : GSTClassicalHodgeMinimalPrimitiveSeparatorGhost.MinimalPrimitiveGhost G)
    (S : GSTClassicalHodgeLocalSeedBareLefschetzExtinction.MinimalGhostLocalSeed G M) :
    FiberedCompletedAddress V H :=
  separatorFiberedProbe (V := V) (H := H) M.weight M.separator.detector

/-- **ARBITRARY-WORLD FORM OF THE BARE L² SEPARATOR READ.**
The exact nonzero separator scalar of the local bare two-step Lefschetz image
may be evaluated in any GST world shape with the same live cardinality. -/
theorem bareTwoStep_separator_read_eq_recoordinatedPoincare
    (G : GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (M : GSTClassicalHodgeMinimalPrimitiveSeparatorGhost.MinimalPrimitiveGhost G)
    (S : GSTClassicalHodgeLocalSeedBareLefschetzExtinction.MinimalGhostLocalSeed G M)
    (T : GSTWorldShape (fiberedSupportSize (bareTwoStepAddress G M S))) :
    M.separator.detector
        (GSTClassicalHodgeUniversalTwoSlotNativeClosure.ambientTwoStepLefschetz
          S.sourceIndex M.sheet S.source.1) =
      rationalWorldTopPairing
        (transportCoefQ
          (fiberedSupportShape (bareTwoStepAddress G M S)) T
          (fiberedSupportWorld (bareTwoStepAddress G M S)))
        (transportPoincareProbeQ
          (fiberedSupportShape (bareTwoStepAddress G M S)) T
          (dualizedSupportProbe
            (bareTwoStepAddress G M S)
            (bareSeparatorProbe G M S))) := by
  calc
    M.separator.detector
        (GSTClassicalHodgeUniversalTwoSlotNativeClosure.ambientTwoStepLefschetz
          S.sourceIndex M.sheet S.source.1) =
      rationalWorldTopPairing
        (fiberedSupportWorld (bareTwoStepAddress G M S))
        (dualizedSupportProbe
          (bareTwoStepAddress G M S)
          (bareSeparatorProbe G M S)) := by
            simpa [bareTwoStepAddress, bareSeparatorProbe] using
              bareTwoStep_separator_read_eq_finiteGSTPoincare G M S
    _ =
      rationalWorldTopPairing
        (transportCoefQ
          (fiberedSupportShape (bareTwoStepAddress G M S)) T
          (fiberedSupportWorld (bareTwoStepAddress G M S)))
        (transportPoincareProbeQ
          (fiberedSupportShape (bareTwoStepAddress G M S)) T
          (dualizedSupportProbe
            (bareTwoStepAddress G M S)
            (bareSeparatorProbe G M S)) ) :=
      rationalWorldTopPairing_recoordinate
        (fiberedSupportShape (bareTwoStepAddress G M S)) T
        (fiberedSupportWorld (bareTwoStepAddress G M S))
        (dualizedSupportProbe
          (bareTwoStepAddress G M S)
          (bareSeparatorProbe G M S))

/-- Flag realization in an arbitrarily chosen GST world chart.  The chart is
part of the geometric construction, so the proof is free to adapt the world
shape to the actual incidence/transpose geometry. -/
structure SingleStateFlagNormalLimitlessReadRealization
    (G : GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (M : GSTClassicalHodgeMinimalPrimitiveSeparatorGhost.MinimalPrimitiveGhost G)
    (S : GSTClassicalHodgeLocalSeedBareLefschetzExtinction.MinimalGhostLocalSeed G M) where
  base : SingleStateFlagNormalPoincareReadRealization G M S
  world : GSTWorldShape (fiberedSupportSize (bareTwoStepAddress G M S))
  world_read :
    rationalWorldTopPairing
        (fiberedSupportWorld (bareTwoStepAddress G M S))
        (dualizedSupportProbe
          (bareTwoStepAddress G M S)
          (bareSeparatorProbe G M S)) =
      rationalWorldTopPairing
        (transportCoefQ
          (fiberedSupportShape (bareTwoStepAddress G M S)) world
          (fiberedSupportWorld (bareTwoStepAddress G M S)))
        (transportPoincareProbeQ
          (fiberedSupportShape (bareTwoStepAddress G M S)) world
          (dualizedSupportProbe
            (bareTwoStepAddress G M S)
            (bareSeparatorProbe G M S)))

/-- The world-read field is canonically supplied by limitless recoordination;
no extra mathematical hypothesis is needed for changing chart. -/
noncomputable def SingleStateFlagNormalPoincareReadRealization.toLimitlessRead
    (G : GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (M : GSTClassicalHodgeMinimalPrimitiveSeparatorGhost.MinimalPrimitiveGhost G)
    (S : GSTClassicalHodgeLocalSeedBareLefschetzExtinction.MinimalGhostLocalSeed G M)
    (F : SingleStateFlagNormalPoincareReadRealization G M S)
    (T : GSTWorldShape (fiberedSupportSize (bareTwoStepAddress G M S))) :
    SingleStateFlagNormalLimitlessReadRealization G M S where
  base := F
  world := T
  world_read := rationalWorldTopPairing_recoordinate
    (fiberedSupportShape (bareTwoStepAddress G M S)) T
    (fiberedSupportWorld (bareTwoStepAddress G M S))
    (dualizedSupportProbe
      (bareTwoStepAddress G M S)
      (bareSeparatorProbe G M S))

#check bareTwoStepAddress
#check bareTwoStep_separator_read_eq_recoordinatedPoincare
#check SingleStateFlagNormalLimitlessReadRealization
#check SingleStateFlagNormalPoincareReadRealization.toLimitlessRead

#print axioms bareTwoStep_separator_read_eq_recoordinatedPoincare
#print axioms SingleStateFlagNormalPoincareReadRealization.toLimitlessRead

end GSTClassicalHodgeSingleStateFlagNormalLimitlessRead
