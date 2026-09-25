import GSTClassicalHodgeTwoGeneratorNativeArsenal
import GSTClassicalHodgeNativeOperatorCohomologyRealization
import GSTClassicalHodgeRankFreeArsenalIrreducibility
import GSTClassicalHodgeAtomicOperatorAlgebra

/-!
# GST CLASSICAL HODGE — GEOMETRY-FIRST TWO-GENERATOR EXTERNALIZATION

The previous two-generator reduction identified the entire limitless Hodge
arsenal with two primitive Hodge-fiber operators: the two-slot code observable
and the exact two-step Lefschetz transport.  This file reverses the direction
of externalization.

We do not first choose an arbitrary ambient extension and then ask geometry to
realize it.  Instead a native operator on actual codimension-p algebraic cycles
is primary.  Kernel stability makes its action well-defined on the actual
cycle-class range, and the native-operator realization theorem extends that
action to genuine rational singular cohomology.  Native point lifts are then
a theorem, not an input.

A primitive is accepted only after proving that this geometry-generated
ambient action restricts on the genuine rational (p,p) fiber to the desired
GST primitive.  Two such primitives generate the universal normalized two-slot
word.  The existing limitless two-slot theorem identifies that word with the
rank-free matrix unit.  Therefore the actual algebraic Hodge subspace is
invariant under every matrix unit as soon as the two primitive native
geometric operators have the required Hodge restrictions.

This file contains no Hodge-surjectivity assumption and no basis-cycle choice.
-/

set_option maxHeartbeats 30000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeFullArsenalIrreducibility
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeRankFreePrimitiveGeneration
open GSTClassicalHodgeNativeGeneratorNaturality
open GSTClassicalHodgeAtomicOperatorAlgebra
open GSTClassicalHodgeUniversalTwoSlotNativeClosure
open GSTClassicalHodgeTwoGeneratorNativeArsenal
open GSTClassicalHodgeNativeOperatorCohomologyRealization

namespace GSTClassicalHodgeGeometryFirstTwoGenerator

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

abbrev NativeCycles := codimensionCycles V.X p
abbrev AmbientCoh := RationalSingularCohomology H.analytification (2 * p)
abbrev HodgeFiber := ClassicalHodgeFiber V H p

/-- A kernel-stable native algebraic-cycle operator automatically gives native
point lifts for the ambient cohomology operator manufactured from it. -/
theorem kernelStable_ambient_hasNativePointLifts
    (A : NativeCycles V p →ₗ[ℚ] NativeCycles V p)
    (hA : KernelStable (H := H) A) :
    HasNativePointLifts (p := p) (cl := H.cycleClass p)
      (ambientOperator (H := H) A hA) := by
  intro x
  refine ⟨A (codimensionPointCycle V.X p x), ?_⟩
  symm
  exact cycleClass_ambientOperator (H := H) A hA
    (codimensionPointCycle V.X p x)

/-- Geometry-first realization of one Hodge-fiber primitive.

The native cycle operator and kernel-stability proof determine the ambient
cohomology operator.  The only comparison theorem required is its restriction
to the genuine Hodge fiber. -/
structure NativeHodgePrimitive
    (T : Module.End ℚ (HodgeFiber V H p)) where
  cycleOperator : NativeCycles V p →ₗ[ℚ] NativeCycles V p
  kernelStable : KernelStable (H := H) cycleOperator
  restricts_to_hodge :
    ∀ alpha : HodgeFiber V H p,
      ambientOperator (H := H) cycleOperator kernelStable alpha.1 =
        (T alpha).1

namespace NativeHodgePrimitive

variable {T : Module.End ℚ (HodgeFiber V H p)}

/-- Ambient operator forced by the native geometry. -/
noncomputable def ambient
    (R : NativeHodgePrimitive (V := V) (H := H) T) :
    AmbientCoh H p →ₗ[ℚ] AmbientCoh H p :=
  ambientOperator (H := H) R.cycleOperator R.kernelStable

/-- Native point-lift naturality is automatic from the native operator. -/
theorem hasNativePointLifts
    (R : NativeHodgePrimitive (V := V) (H := H) T) :
    HasNativePointLifts (p := p) (cl := H.cycleClass p) R.ambient := by
  exact kernelStable_ambient_hasNativePointLifts
    (H := H) R.cycleOperator R.kernelStable

/-- The geometry-generated ambient operator has the prescribed Hodge action. -/
@[simp]
theorem ambient_on_hodge
    (R : NativeHodgePrimitive (V := V) (H := H) T)
    (alpha : HodgeFiber V H p) :
    R.ambient alpha.1 = (T alpha).1 :=
  R.restricts_to_hodge alpha

end NativeHodgePrimitive

/-- The two genuinely noncommuting native geometric primitives.

Unlike `TwoGeneratorNative`, this structure stores native algebraic-cycle
operators.  Their ambient cohomological actions are derived from kernel
stability. -/
structure GeometryFirstTwoGenerator
    (i j : ClassicalHodgeBasisIndex V H p) where
  code : NativeHodgePrimitive (V := V) (H := H)
    (twoSlotCodeHodge i j)
  lefschetz : NativeHodgePrimitive (V := V) (H := H)
    (twoSlotHodgeOperator i j (diagonalLefschetzQ 2 2))

namespace GeometryFirstTwoGenerator

variable {i j : ClassicalHodgeBasisIndex V H p}

/-- Geometry-generated code action on ambient rational cohomology. -/
noncomputable def ambientCode
    (R : GeometryFirstTwoGenerator (V := V) (H := H) i j) :
    AmbientCoh H p →ₗ[ℚ] AmbientCoh H p :=
  R.code.ambient

/-- Geometry-generated two-step Lefschetz action on ambient cohomology. -/
noncomputable def ambientLefschetz
    (R : GeometryFirstTwoGenerator (V := V) (H := H) i j) :
    AmbientCoh H p →ₗ[ℚ] AmbientCoh H p :=
  R.lefschetz.ambient

/-- Source projector generated polynomially from the geometry-first code
observable. -/
noncomputable def ambientSource
    (R : GeometryFirstTwoGenerator (V := V) (H := H) i j) :
    AmbientCoh H p →ₗ[ℚ] AmbientCoh H p :=
  LinearMap.id - R.ambientCode

/-- Universal normalized two-slot transfer word generated entirely from the
two native geometric primitives. -/
noncomputable def ambientWord
    (R : GeometryFirstTwoGenerator (V := V) (H := H) i j) :
    AmbientCoh H p →ₗ[ℚ] AmbientCoh H p :=
  (forwardScalar sourceSlot targetSlot : ℚ)⁻¹ •
    (R.ambientCode.comp (R.ambientLefschetz.comp R.ambientSource))

/-- Identity-minus-code remains native-natural. -/
theorem source_hasNativePointLifts
    (R : GeometryFirstTwoGenerator (V := V) (H := H) i j) :
    HasNativePointLifts (p := p) (cl := H.cycleClass p) R.ambientSource := by
  rw [← smoothProjective_atomicStable_iff_nativePointLifts]
  exact atomicSpanStable_sub atomicSpanStable_id
    ((smoothProjective_atomicStable_iff_nativePointLifts).2
      R.code.hasNativePointLifts)

/-- The universal geometry-first word is native-natural by pure operator
closure; no basis cycle is chosen. -/
theorem ambientWord_hasNativePointLifts
    (R : GeometryFirstTwoGenerator (V := V) (H := H) i j) :
    HasNativePointLifts (p := p) (cl := H.cycleClass p) R.ambientWord := by
  unfold ambientWord
  apply GSTClassicalHodgeNativeGeneratorNaturality.HasNativePointLifts.smul
  exact nativePointLifts_comp R.code.hasNativePointLifts
    (nativePointLifts_comp R.lefschetz.hasNativePointLifts
      R.source_hasNativePointLifts)

/-- On the genuine Hodge fiber the geometry-first source operator is exactly
the source sheet projector. -/
theorem ambientSource_on_hodge
    (R : GeometryFirstTwoGenerator (V := V) (H := H) i j)
    (alpha : HodgeFiber V H p) :
    R.ambientSource alpha.1 =
      ((LinearMap.id - twoSlotCodeHodge i j) alpha).1 := by
  simp [ambientSource, ambientCode, NativeHodgePrimitive.ambient_on_hodge]

/-- **GEOMETRY-FIRST UNIVERSAL WORD.**
On the genuine Hodge fiber the native-geometric word is exactly the rank-free
matrix unit `E_{i,j}` generated by the full GST projector/Lefschetz/Poincare
arsenal. -/
theorem ambientWord_on_hodge
    (R : GeometryFirstTwoGenerator (V := V) (H := H) i j)
    (alpha : HodgeFiber V H p) :
    R.ambientWord alpha.1 = (hodgeMatrixUnit i j alpha).1 := by
  let src : HodgeFiber V H p :=
    (LinearMap.id - twoSlotCodeHodge i j) alpha
  let mid : HodgeFiber V H p :=
    twoSlotHodgeOperator i j (diagonalLefschetzQ 2 2) src
  have hsrc : R.ambientSource alpha.1 = src.1 := by
    simpa [src] using R.ambientSource_on_hodge alpha
  have hmid : R.ambientLefschetz src.1 = mid.1 := by
    simpa [ambientLefschetz, mid] using R.lefschetz.ambient_on_hodge src
  have htgt : R.ambientCode mid.1 = (twoSlotCodeHodge i j mid).1 := by
    simpa [ambientCode] using R.code.ambient_on_hodge mid
  unfold ambientWord
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [hsrc, hmid, htgt]
  have hfinite :
      ((forwardScalar sourceSlot targetSlot : ℚ)⁻¹ •
        ((twoSlotCode).comp
          ((diagonalLefschetzQ 2 2).comp
            (LinearMap.id - twoSlotCode)))) =
        pureMatrixUnit sourceSlot targetSlot := by
    rw [← sheetProjectorQ_target_eq_code,
      ← sheetProjectorQ_source_eq_id_sub_code]
    exact forwardArsenalWord_eq_matrixUnit
      sourceSlot targetSlot (by omega)
  have hlift :
      liftFiniteHodgeOperator (pairBasisIndex i j)
          (pureMatrixUnit sourceSlot targetSlot) =
        hodgeMatrixUnit i j :=
    exact rankFreeMatrixUnit_eq_lifted_GST_word i j |>.symm
  simpa [src, mid, twoSlotCodeHodge, twoSlotHodgeOperator,
    hfinite, hlift]

/-- Every geometry-first two-generator realization forces the corresponding
rank-free matrix unit to preserve the actual algebraic Hodge subspace. -/
theorem matrixUnit_mem_algebraic
    (R : GeometryFirstTwoGenerator (V := V) (H := H) i j)
    (alpha : HodgeFiber V H p)
    (halpha : alpha ∈ AlgebraicHodgeSubspace V H p) :
    hodgeMatrixUnit i j alpha ∈ AlgebraicHodgeSubspace V H p := by
  have hstable : AtomicSpanStable (p := p) (cl := H.cycleClass p)
      R.ambientWord :=
    (smoothProjective_atomicStable_iff_nativePointLifts).2
      R.ambientWord_hasNativePointLifts
  have himage := hstable alpha.1 halpha
  rw [R.ambientWord_on_hodge alpha] at himage
  exact himage

end GeometryFirstTwoGenerator

/-- A geometry-first realization for every ordered Hodge-basis pair gives the
full unrestricted arsenal invariance theorem. -/
theorem rankFreeArsenalInvariant_of_geometryFirstTwoGenerators
    (R : ∀ i j : ClassicalHodgeBasisIndex V H p,
      GeometryFirstTwoGenerator (V := V) (H := H) i j) :
    RankFreeArsenalInvariant (AlgebraicHodgeSubspace V H p) := by
  intro i j alpha halpha
  exact (R i j).matrixUnit_mem_algebraic alpha halpha

/-- Consequently, once the algebraic Hodge subspace is nonzero, geometry-first
two-generator naturality saturates the entire genuine Hodge fiber. -/
theorem algebraicHodgeSubspace_eq_top_of_geometryFirstTwoGenerators
    (R : ∀ i j : ClassicalHodgeBasisIndex V H p,
      GeometryFirstTwoGenerator (V := V) (H := H) i j)
    (hne : AlgebraicHodgeSubspace V H p ≠ ⊥) :
    AlgebraicHodgeSubspace V H p = ⊤ := by
  exact rankFreeArsenalInvariant_eq_top
    (AlgebraicHodgeSubspace V H p)
    (rankFreeArsenalInvariant_of_geometryFirstTwoGenerators R)
    hne

#check kernelStable_ambient_hasNativePointLifts
#check NativeHodgePrimitive
#check NativeHodgePrimitive.ambient
#check NativeHodgePrimitive.hasNativePointLifts
#check GeometryFirstTwoGenerator
#check GeometryFirstTwoGenerator.ambientWord
#check GeometryFirstTwoGenerator.ambientWord_hasNativePointLifts
#check GeometryFirstTwoGenerator.ambientWord_on_hodge
#check GeometryFirstTwoGenerator.matrixUnit_mem_algebraic
#check rankFreeArsenalInvariant_of_geometryFirstTwoGenerators
#check algebraicHodgeSubspace_eq_top_of_geometryFirstTwoGenerators

#print axioms kernelStable_ambient_hasNativePointLifts
#print axioms GeometryFirstTwoGenerator.ambientWord_hasNativePointLifts
#print axioms GeometryFirstTwoGenerator.ambientWord_on_hodge
#print axioms GeometryFirstTwoGenerator.matrixUnit_mem_algebraic
#print axioms rankFreeArsenalInvariant_of_geometryFirstTwoGenerators
#print axioms algebraicHodgeSubspace_eq_top_of_geometryFirstTwoGenerators

end GSTClassicalHodgeGeometryFirstTwoGenerator
