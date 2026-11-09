import GSTHodgeWaveCurvatureResidualStep
import GSTHodgeGSTWaveGeometricCompiler
import GSTHodgeGSTUnifiedPrimitiveWaveRank

/-!
# GST wave/CM/curvature residual landing on the ACTUAL original X

The previous theorem eliminates one genuine curvature-detected direction
from the complement of any already realized GST N-hole wave frame.

This module connects it to the original smooth projective complex X at
codimension two, using only:
* the existing native seven-axis wave-source compiler;
* the native primitive cycle normalizer (actual Hard Lefschetz correction);
* two REAL native correspondence operator pairs preserving primitive cycles;
* an independently geometric readout of the curvature-born primitive source.

Output: an explicit original-X codimension-two Chow cycle PLUS a primitive
rational Hodge residual killed by all wave detectors and the curvature probe.

Neither an arbitrary target cycle class preimage nor the universal source
orbit is asserted as a field.
-/

noncomputable section

namespace GSTHodgePrimitiveWaveCurvatureLanding

open GSTHodgeWaveCurvatureResidualStep
open GSTHodgeGSTUnifiedPrimitiveWaveRank
open GSTHodgeGSTWaveGeometricCompiler
open GSTHodgeWaveAllNGeometricLanding
open GSTGraphV2NativeCurvatureBirth
open GSTClassicalHodgeCycleOperatorNaturality
open GSTUniversalCodimensionTwoPrimitiveExtraction
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTUniversalLefschetzCurveCycles
open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTNCohomology

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {d : Nat}
variable {s t : NShape}

/-- The actual primitive original-X cycle built by taking curvature
of a genuine GST wave source, after the real divisor/Lefschetz
primitive correction. The two native folds must preserve the
primitive kernel. -/
def primitiveWaveCurvatureCycle
    (G : GeometricCycleClassSpine V H)
    (P : GeometricHigherLefschetzData G d)
    (h11 : DivisorsRepresentHodge11 H)
    (C : WaveNativeCompiler V H 2 t)
    (A B : CycleClassOperatorPair V H 2)
    (hA : ∀ Z : codimensionCycles V.X 2,
      P.primitiveTest (nativeToHodgeFiberLinear G Z) = 0 →
      P.primitiveTest (nativeToHodgeFiberLinear G (A.cycleOperator Z)) = 0)
    (hB : ∀ Z : codimensionCycles V.X 2,
      P.primitiveTest (nativeToHodgeFiberLinear G Z) = 0 →
      P.primitiveTest (nativeToHodgeFiberLinear G (B.cycleOperator Z)) = 0) :
    ↥(NativePrimitiveCycles G P) :=
  ⟨primitiveBornCurvature C G P h11 A B, by
    apply LinearMap.mem_ker.mpr
    change P.primitiveTest (nativeToHodgeFiberLinear G
      (primitiveBornCurvature C G P h11 A B)) = 0
    exact primitiveBornCurvature_test C G P h11 A B hA hB⟩

/-- Main integrated original-X theorem: one new geometrically
detectable curvature direction extends the GST N-wave primitive
source frame by one and eliminates its readout from the residual.
Every cycle lies on the original X; all comparison maps are the
previous canonical codimension-two maps. -/
theorem originalX_primitive_wave_curvature_residual
    (G : GeometricCycleClassSpine V H)
    (P : GeometricHigherLefschetzData G d)
    (h11 : DivisorsRepresentHodge11 H)
    (C : WaveNativeCompiler V H 2 t)
    (A B : CycleClassOperatorPair V H 2)
    (hA : ∀ Z : codimensionCycles V.X 2,
      P.primitiveTest (nativeToHodgeFiberLinear G Z) = 0 →
      P.primitiveTest (nativeToHodgeFiberLinear G (A.cycleOperator Z)) = 0)
    (hB : ∀ Z : codimensionCycles V.X 2,
      P.primitiveTest (nativeToHodgeFiberLinear G Z) = 0 →
      P.primitiveTest (nativeToHodgeFiberLinear G (B.cycleOperator Z)) = 0)
    (F : GeometricWaveFrame s (primitiveCycleClass G P))
    (read : ↥(PrimitiveHodgeFiber G P) →ₗ[ℚ] ℚ)
    (hOld : ∀ i : Fin s.holes,
      read (primitiveCycleClass G P (F.atom i)) = 0)
    (hNew : read (primitiveCycleClass G P
      (primitiveWaveCurvatureCycle G P h11 C A B hA hB)) ≠ 0)
    (alpha : ClassicalHodgeFiber V H 2) :
    ∃ Z : codimensionCycles V.X 2,
      ∃ r : ↥(PrimitiveHodgeFiber G P),
        alpha = nativeToHodgeFiberLinear G Z + r.1 ∧
        F.bettiCoordinates r = 0 ∧
        read r = 0 := by
  let beta : ↥(PrimitiveHodgeFiber G P) :=
    ⟨primitiveHodgeRemainder G P h11 alpha,
      primitiveHodgeRemainder_primitive G P h11 alpha⟩
  let born := primitiveWaveCurvatureCycle G P h11 C A B hA hB
  let waveZ := waveCurvatureCycle F born read beta
  let residual := waveCurvatureResidual F born read beta
  have hdec := waveCurvatureResidual_decomposition
    F born read hOld hNew beta
  have hbeta : beta.1 = nativeToHodgeFiberLinear G waveZ.1 +
      residual.1 := by
    have h := congrArg Subtype.val hdec.1
    exact h
  refine ⟨waveZ.1 + algebraicLefschetzCorrection G P h11 alpha,
    residual, ?_, hdec.2.1, hdec.2.2⟩
  calc
    alpha = beta.1 +
        nativeToHodgeFiberLinear G
          (algebraicLefschetzCorrection G P h11 alpha) :=
      Hodge_class_eq_primitive_plus_native_cycle G P h11 alpha
    _ = (nativeToHodgeFiberLinear G waveZ.1 + residual.1) +
        nativeToHodgeFiberLinear G
          (algebraicLefschetzCorrection G P h11 alpha) := by rw [hbeta]
    _ = nativeToHodgeFiberLinear G
          (waveZ.1 + algebraicLefschetzCorrection G P h11 alpha) +
        residual.1 := by
          rw [map_add]
          abel

/-- A stronger geometric separation criterion after wave+curvature
eliminates the residual altogether and yields an actual Chow cycle. -/
theorem originalX_primitive_wave_curvature_complete_of_detection
    (G : GeometricCycleClassSpine V H)
    (P : GeometricHigherLefschetzData G d)
    (h11 : DivisorsRepresentHodge11 H)
    (C : WaveNativeCompiler V H 2 t)
    (A B : CycleClassOperatorPair V H 2)
    (hA : ∀ Z : codimensionCycles V.X 2,
      P.primitiveTest (nativeToHodgeFiberLinear G Z) = 0 →
      P.primitiveTest (nativeToHodgeFiberLinear G (A.cycleOperator Z)) = 0)
    (hB : ∀ Z : codimensionCycles V.X 2,
      P.primitiveTest (nativeToHodgeFiberLinear G Z) = 0 →
      P.primitiveTest (nativeToHodgeFiberLinear G (B.cycleOperator Z)) = 0)
    (F : GeometricWaveFrame s (primitiveCycleClass G P))
    (read : ↥(PrimitiveHodgeFiber G P) →ₗ[ℚ] ℚ)
    (hOld : ∀ i : Fin s.holes,
      read (primitiveCycleClass G P (F.atom i)) = 0)
    (hNew : read (primitiveCycleClass G P
      (primitiveWaveCurvatureCycle G P h11 C A B hA hB)) ≠ 0)
    (hSeparate : ∀ r : ↥(PrimitiveHodgeFiber G P),
      F.bettiCoordinates r = 0 → read r = 0 → r = 0)
    (alpha : ClassicalHodgeFiber V H 2) :
    ∃ Z : codimensionCycles V.X 2,
      nativeToHodgeFiberLinear G Z = alpha := by
  obtain ⟨Z, r, hdec, hOldZero, hNewZero⟩ :=
    originalX_primitive_wave_curvature_residual
      G P h11 C A B hA hB F read hOld hNew alpha
  have hr : r = 0 := hSeparate r hOldZero hNewZero
  refine ⟨Z, ?_⟩
  rw [hr, Submodule.coe_zero, add_zero] at hdec
  exact hdec.symm

#check primitiveWaveCurvatureCycle
#check originalX_primitive_wave_curvature_residual
#check originalX_primitive_wave_curvature_complete_of_detection
#print axioms originalX_primitive_wave_curvature_residual

end GSTHodgePrimitiveWaveCurvatureLanding
