import GSTClassicalHodgeTwoGeneratorNativeArsenal
import GSTClassicalHodgeAlgebraicArsenalSaturation
import GSTClassicalHodgeNativeGeneratorNaturality

/-!
# GST CLASSICAL HODGE — TWO PRIMITIVE POINT KERNELS SATURATE ONE HODGE WEIGHT

The geometry-first route can be weakened to the exact generator-level data
actually consumed by algebraic saturation.

For an ordered pair of genuine Hodge sheets `(i,j)`, consider the two ambient
operators already fixed by the GST two-slot construction:

* the code observable `D = diag(0,1)`;
* the two-step finite-world Lefschetz operator `L²`.

Their ambient extensions are defined independently of algebraicity and have the
correct Hodge-fiber restrictions by construction.  Therefore we do NOT need a
native operator whose independently reconstructed ambient extension agrees on
all Hodge vectors.  It is enough to prove generatorwise native lifts for these
two fixed ambient maps.

The existing native-generator theorem turns those lifts into atomic stability.
Operator closure then gives atomic stability of the normalized word

    D ∘ L² ∘ (I-D),

and the finite GST computation identifies that word on the genuine Hodge fiber
with the rank-free matrix unit `E_{i,j}`.  Thus every algebraic Hodge seed has
its complete one-step matrix-unit orbit algebraic.  One nonzero seed therefore
saturates the entire weight.

Finally, chosen `NativePointTransition`s package the remaining geometry as two
explicit pointwise cycle equations.  This is strictly weaker than the earlier
`GeometryFirstTwoGenerator`: no independently reconstructed ambient operator is
required to agree on non-algebraic Hodge vectors.
-/

set_option maxHeartbeats 70000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeGeneratorwiseAtomicStability
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeFullArsenalIrreducibility
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeRankFreePrimitiveGeneration
open GSTClassicalHodgeExplicitArsenalGeneration
open GSTClassicalHodgeUniversalTwoSlotNativeClosure
open GSTClassicalHodgeTwoGeneratorNativeArsenal
open GSTClassicalHodgeNativeGeneratorNaturality
open GSTClassicalHodgeAlgebraicArsenalSaturation

namespace GSTClassicalHodgeTwoGeneratorPointKernelSaturation

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

abbrev HFiber := ClassicalHodgeFiber V H p

/-- The exact normalized two-generator ambient word. -/
noncomputable def twoGeneratorAmbientWord
    (i j : ClassicalHodgeBasisIndex V H p) :
    Module.End ℚ
      (GSTGeometricRealizationStage2F.RationalSingularCohomology
        H.analytification (2 * p)) :=
  (forwardScalar sourceSlot targetSlot : ℚ)⁻¹ •
    ((ambientTwoSlotCode i j).comp
      ((ambientTwoStepLefschetz i j).comp
        (LinearMap.id - ambientTwoSlotCode i j)))

/-- **THE TWO-GENERATOR WORD IS THE HODGE MATRIX UNIT.**
This is a pure GST/Hodge calculation; no algebraicity or native-cycle witness
is used. -/
theorem twoGeneratorAmbientWord_on_hodge
    (i j : ClassicalHodgeBasisIndex V H p)
    (alpha : HFiber) :
    twoGeneratorAmbientWord i j alpha.1 =
      (hodgeMatrixUnit i j alpha).1 := by
  let src : HFiber :=
    (LinearMap.id - twoSlotCodeHodge i j) alpha
  let mid : HFiber :=
    twoSlotHodgeOperator i j (diagonalLefschetzQ 2 2) src
  have hcode0 := extendHodgeEndomorphism_on_hodge
    (V := V) (H := H) (twoSlotCodeHodge i j) alpha
  have hsrc :
      (LinearMap.id - ambientTwoSlotCode i j) alpha.1 = src.1 := by
    simp only [LinearMap.sub_apply, LinearMap.id_apply]
    rw [hcode0]
    rfl
  have hL := extendHodgeEndomorphism_on_hodge
    (V := V) (H := H)
    (twoSlotHodgeOperator i j (diagonalLefschetzQ 2 2)) src
  have htgt := extendHodgeEndomorphism_on_hodge
    (V := V) (H := H) (twoSlotCodeHodge i j) mid
  unfold twoGeneratorAmbientWord
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [hsrc, hL, htgt]
  have hfinite :
      ((forwardScalar sourceSlot targetSlot : ℚ)⁻¹ •
        (twoSlotCode.comp
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
    exact liftFiniteHodgeOperator_matrixUnit
      (pairBasisIndex i j) sourceSlot targetSlot
  simpa [src, mid, twoSlotCodeHodge, twoSlotHodgeOperator,
    hfinite, pairBasisIndex_source, pairBasisIndex_target] using
      LinearMap.congr_fun hlift alpha

/-- Native two-generator point lifts force the corresponding matrix-unit image
of every already-algebraic Hodge vector to remain algebraic. -/
theorem TwoGeneratorNative.matrixUnit_mem_algebraic
    {i j : ClassicalHodgeBasisIndex V H p}
    (R : TwoGeneratorNative (V := V) (H := H) i j)
    (alpha : HFiber)
    (halpha : alpha ∈ AlgebraicHodgeSubspace V H p) :
    hodgeMatrixUnit i j alpha ∈ AlgebraicHodgeSubspace V H p := by
  have hstable : AtomicSpanStable (p := p) (cl := H.cycleClass p)
      (twoGeneratorAmbientWord i j) := by
    rw [smoothProjective_atomicStable_iff_nativePointLifts]
    simpa [twoGeneratorAmbientWord] using R.normalizedWord_nativePointLifts
  have himage := hstable alpha.1 halpha
  rw [twoGeneratorAmbientWord_on_hodge i j alpha] at himage
  exact himage

/-- A family of two-generator native point-lift packages makes the actual
algebraic Hodge subspace invariant under every rank-free matrix unit. -/
theorem rankFreeArsenalInvariant_of_twoGeneratorNative
    (R : ∀ i j : ClassicalHodgeBasisIndex V H p,
      TwoGeneratorNative (V := V) (H := H) i j) :
    RankFreeArsenalInvariant (AlgebraicHodgeSubspace V H p) := by
  intro i j alpha halpha
  exact (R i j).matrixUnit_mem_algebraic alpha halpha

/-- One nonzero algebraic seed plus the two primitive native point-lift laws
saturates the whole genuine Hodge fiber. -/
theorem algebraicHodgeSubspace_eq_top_of_twoGeneratorNative
    (hseed : AlgebraicHodgeSubspace V H p ≠ ⊥)
    (R : ∀ i j : ClassicalHodgeBasisIndex V H p,
      TwoGeneratorNative (V := V) (H := H) i j) :
    AlgebraicHodgeSubspace V H p = ⊤ := by
  exact rankFreeArsenalInvariant_eq_top
    (AlgebraicHodgeSubspace V H p)
    (rankFreeArsenalInvariant_of_twoGeneratorNative R)
    hseed

/-- The same hypotheses give the exact weight-p Hodge landing. -/
theorem hodge_weight_of_twoGeneratorNative
    (hseed : AlgebraicHodgeSubspace V H p ≠ ⊥)
    (R : ∀ i j : ClassicalHodgeBasisIndex V H p,
      TwoGeneratorNative (V := V) (H := H) i j) :
    rationalHodgeSubspace (H.hodgeBigrading p) ≤
      LinearMap.range (H.cycleClass p) := by
  have htop := algebraicHodgeSubspace_eq_top_of_twoGeneratorNative hseed R
  intro alpha halpha
  let a : HFiber := ⟨alpha, halpha⟩
  have ha : a ∈ AlgebraicHodgeSubspace V H p := by
    rw [htop]
    trivial
  rw [GSTClassicalHodgeAtomicSpan.smoothProjective_cycleClass_range_eq_atomic_span V H p]
  exact ha

/-- Generator-level data for the two fixed ambient GST primitives. -/
structure TwoPrimitivePointTransitions
    (i j : ClassicalHodgeBasisIndex V H p) where
  code : NativePointTransition
    (p := p) (cl := H.cycleClass p) (ambientTwoSlotCode i j)
  lefschetz : NativePointTransition
    (p := p) (cl := H.cycleClass p) (ambientTwoStepLefschetz i j)

namespace TwoPrimitivePointTransitions

/-- Pointwise native transitions immediately supply the older existential
`TwoGeneratorNative` package. -/
def toTwoGeneratorNative
    {i j : ClassicalHodgeBasisIndex V H p}
    (K : TwoPrimitivePointTransitions (V := V) (H := H) i j) :
    TwoGeneratorNative (V := V) (H := H) i j where
  code := K.code.hasNativePointLifts
  lefschetz := K.lefschetz.hasNativePointLifts

end TwoPrimitivePointTransitions

/-- **POINT-KERNEL SATURATION CROWN.**
The complete fixed-weight Hodge target follows from one nonzero algebraic seed
and, for every ordered pair of Hodge sheets, two concrete pointwise native
transition constructions: the GST code observable and the GST two-step
Lefschetz observable. -/
theorem hodge_weight_of_two_primitive_point_transitions
    (hseed : AlgebraicHodgeSubspace V H p ≠ ⊥)
    (K : ∀ i j : ClassicalHodgeBasisIndex V H p,
      TwoPrimitivePointTransitions (V := V) (H := H) i j) :
    rationalHodgeSubspace (H.hodgeBigrading p) ≤
      LinearMap.range (H.cycleClass p) := by
  exact hodge_weight_of_twoGeneratorNative hseed
    (fun i j => (K i j).toTwoGeneratorNative)

#check twoGeneratorAmbientWord
#check twoGeneratorAmbientWord_on_hodge
#check TwoGeneratorNative.matrixUnit_mem_algebraic
#check rankFreeArsenalInvariant_of_twoGeneratorNative
#check algebraicHodgeSubspace_eq_top_of_twoGeneratorNative
#check hodge_weight_of_twoGeneratorNative
#check TwoPrimitivePointTransitions
#check hodge_weight_of_two_primitive_point_transitions

#print axioms twoGeneratorAmbientWord_on_hodge
#print axioms TwoGeneratorNative.matrixUnit_mem_algebraic
#print axioms hodge_weight_of_twoGeneratorNative
#print axioms hodge_weight_of_two_primitive_point_transitions

end GSTClassicalHodgeTwoGeneratorPointKernelSaturation
