import GSTClassicalHodgeLocalSeedBareLefschetzExtinction

/-!
# GST CLASSICAL HODGE — SINGLE-STATE BARE-LEFSCHETZ EXTINCTION

The existing one-motion extinction theorem requests native point lifts for the
entire bare two-slot GST `L^2` ambient operator.  Its contradiction, however,
evaluates that operator on only one already-algebraic local seed.

This file removes the unnecessary global naturality demand.  For a minimal
primitive ghost `M` and a local algebraic source `S`, it is enough to prove one
single-state statement:

  `L^2(S.source)` lies in the actual atomic algebraic span.

The exact two-slot formula then says this image is a nonzero scalar multiple of
the basis sheet detected by `M.separator`.  The same separator annihilates the
complete atomic algebraic span, giving the contradiction.

This is strictly weaker than `HasNativePointLifts`: no behavior on any other
point cycle or cohomology class is required.
-/

set_option maxHeartbeats 90000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeSingleStateBareLefschetzExtinction

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeAtomicAnnihilator
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeMinimalPrimitiveSeparatorGhost
open GSTClassicalHodgeUniversalTwoSlotNativeClosure
open GSTClassicalHodgeTwoSlotLefschetzCollapse
open GSTClassicalHodgeLocalSeedBareLefschetzExtinction

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- **ONE-STATE GST L² EXTINCTION.**  Global native point-lift naturality is
not needed: algebraicity of the unique local-seed image already contradicts a
minimal separator ghost. -/
theorem minimalGhost_false_of_localSeed_bareLefschetz_image_algebraic
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    (S : MinimalGhostLocalSeed G M)
    (himage :
      ambientTwoStepLefschetz S.sourceIndex M.sheet S.source.1 ∈
        pointCycleClassSpan M.weight (H.cycleClass M.weight)) : False := by
  have hker :
      pointCycleClassSpan M.weight (H.cycleClass M.weight) ≤
        LinearMap.ker M.separator.detector :=
    (annihilatesPointCycles_iff_atomicSpan_le_ker
      M.weight (H.cycleClass M.weight) M.separator.detector).mp
      M.separator.annihilates_atoms
  have hzero := hker himage
  rw [ambientTwoStepLefschetz_on_hodge_coordinate] at hzero
  have hscalar :
      (forwardScalar sourceSlot targetSlot : ℚ) *
          hodgeCoordinate S.sourceIndex S.source ≠ 0 :=
    mul_ne_zero twoSlot_forwardScalar_ne_zero S.sourceCoefficient_ne_zero
  exact (smul_ne_zero hscalar M.separator.detects_basis) hzero

/-- Point-lift naturality implies the single-state condition, recovering the
older theorem as a corollary while exposing the genuinely minimal obligation. -/
theorem localSeed_image_algebraic_of_nativePointLifts
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    (S : MinimalGhostLocalSeed G M)
    (hL : GSTClassicalHodgeNativeGeneratorNaturality.HasNativePointLifts
      (p := M.weight) (cl := H.cycleClass M.weight)
      (ambientTwoStepLefschetz S.sourceIndex M.sheet)) :
    ambientTwoStepLefschetz S.sourceIndex M.sheet S.source.1 ∈
      pointCycleClassSpan M.weight (H.cycleClass M.weight) := by
  have hstable := atomicStable_of_nativePointLifts
    (ambientTwoStepLefschetz S.sourceIndex M.sheet) hL
  exact hstable S.source.1 S.source_algebraic

/-- Minimal-ghost criterion phrased with exactly one state per ghost. -/
theorem bigradedBettiHodge_of_localSeeds_singleStateBareLefschetz
    (G : GeometricCycleClassSpine V H)
    (seed : ∀ M : MinimalPrimitiveGhost G,
      Nonempty (MinimalGhostLocalSeed G M))
    (himage : ∀ M : MinimalPrimitiveGhost G,
      ∀ S : MinimalGhostLocalSeed G M,
        ambientTwoStepLefschetz S.sourceIndex M.sheet S.source.1 ∈
          pointCycleClassSpan M.weight (H.cycleClass M.weight)) :
    BigradedBettiHodgeStatement V H := by
  by_contra hnot
  let M : MinimalPrimitiveGhost G := minimalPrimitiveGhostOfFailure G hnot
  exact minimalGhost_false_of_localSeed_bareLefschetz_image_algebraic
    G M (seed M).some (himage M (seed M).some)

#check minimalGhost_false_of_localSeed_bareLefschetz_image_algebraic
#check localSeed_image_algebraic_of_nativePointLifts
#check bigradedBettiHodge_of_localSeeds_singleStateBareLefschetz

#print axioms minimalGhost_false_of_localSeed_bareLefschetz_image_algebraic
#print axioms localSeed_image_algebraic_of_nativePointLifts
#print axioms bigradedBettiHodge_of_localSeeds_singleStateBareLefschetz

end GSTClassicalHodgeSingleStateBareLefschetzExtinction
