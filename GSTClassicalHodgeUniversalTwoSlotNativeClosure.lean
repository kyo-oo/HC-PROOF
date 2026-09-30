import Mathlib.Algebra.Module.Projective
import GSTClassicalHodgeUniversalTwoSlotSaturation
import GSTClassicalHodgeAtomicOperatorAlgebra
import GSTClassicalHodgeCanonicalAmbientArsenal
import GSTClassicalHodgeExplicitArsenalGeneration

/-!
# GST CLASSICAL HODGE — UNIVERSAL TWO-SLOT NATIVE CLOSURE

Every rank-free Hodge matrix unit is the lift of the same finite two-slot GST
word.  This module pushes that compression through the native point-cycle
naturality calculus.

For an ordered pair `(i,j)` of genuine Hodge basis directions, the selected
2-slot Hodge fiber carries three primitive finite operators:

* source projector `P_0`;
* the actual rationalized GST Lefschetz step `L^2`;
* target projector `P_1`.

Their normalized composition is `forwardArsenalWord 0 1`, hence exactly the
rank-free matrix unit `E_{i,j}` after finite read/write conjugation.

Each primitive is extended linearly from the Hodge subspace to ambient
cohomology.  If the three ambient primitives admit native point lifts, the
existing atomic-operator algebra closes the property under composition and
rational scaling, yielding native naturality for the entire universal word.
Thus the unrestricted arsenal externalization reduces to three primitive
geometric point-transition laws in one universal 2-slot chart.
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
open GSTClassicalHodgeFullArsenalIrreducibility
open GSTClassicalHodgeExplicitArsenalGeneration
open GSTClassicalHodgeRankFreePrimitiveGeneration
open GSTClassicalHodgeGeneratorwiseAtomicStability
open GSTClassicalHodgeAtomicOperatorAlgebra
open GSTClassicalHodgeNativeGeneratorNaturality
open GSTClassicalHodgeRankFreeArsenalIrreducibility

namespace GSTClassicalHodgeUniversalTwoSlotNativeClosure

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

abbrev Coh (H : HodgeBigradedBettiData V) (p : Nat) :=
  RationalSingularCohomology H.analytification (2 * p)
abbrev HFiber (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) (p : Nat) := ClassicalHodgeFiber V H p

/-- Extend an arbitrary endomorphism of the genuine Hodge fiber to ambient
rational cohomology. -/
noncomputable def extendHodgeEndomorphism
    (T : Module.End ℚ (HFiber V H p)) :
    Coh H p →ₗ[ℚ] Coh H p :=
  Classical.choose
    (LinearMap.exists_extend
      ((rationalHodgeSubspace (H.hodgeBigrading p)).subtype.comp T))

/-- Exact restriction law of the ambient extension. -/
theorem extendHodgeEndomorphism_on_hodge
    (T : Module.End ℚ (HFiber V H p))
    (alpha : HFiber V H p) :
    extendHodgeEndomorphism (V:=V) (H:=H) T alpha.1 = (T alpha).1 := by
  have h := Classical.choose_spec
    (LinearMap.exists_extend
      ((rationalHodgeSubspace (H.hodgeBigrading p)).subtype.comp T))
  exact LinearMap.congr_fun h alpha

/-- Lift one finite 2-slot GST operator to the genuine Hodge fiber for the
ordered basis pair `(i,j)`. -/
noncomputable def twoSlotHodgeOperator
    (i j : ClassicalHodgeBasisIndex V H p)
    (T : Module.End ℚ (RationalPureWindow 2)) :
    Module.End ℚ (HFiber V H p) :=
  liftFiniteHodgeOperator (pairBasisIndex i j) T

/-- Ambient source projector. -/
noncomputable def ambientSourceProjector
    (i j : ClassicalHodgeBasisIndex V H p) :
    Coh H p →ₗ[ℚ] Coh H p :=
  extendHodgeEndomorphism (V:=V) (H:=H)
    (twoSlotHodgeOperator i j (sheetProjectorQ sourceSlot))

/-- Ambient two-step GST Lefschetz primitive. -/
noncomputable def ambientTwoStepLefschetz
    (i j : ClassicalHodgeBasisIndex V H p) :
    Coh H p →ₗ[ℚ] Coh H p :=
  extendHodgeEndomorphism (V:=V) (H:=H)
    (twoSlotHodgeOperator i j (diagonalLefschetzQ 2 2))

/-- Ambient target projector. -/
noncomputable def ambientTargetProjector
    (i j : ClassicalHodgeBasisIndex V H p) :
    Coh H p →ₗ[ℚ] Coh H p :=
  extendHodgeEndomorphism (V:=V) (H:=H)
    (twoSlotHodgeOperator i j (sheetProjectorQ targetSlot))

/-- Ambient normalized universal 2-slot word, assembled from the three
primitive ambient operators. -/
noncomputable def ambientUniversalTwoSlotWord
    (i j : ClassicalHodgeBasisIndex V H p) :
    Coh H p →ₗ[ℚ] Coh H p :=
  (forwardScalar sourceSlot targetSlot : ℚ)⁻¹ •
    ((ambientTargetProjector i j).comp
      ((ambientTwoStepLefschetz i j).comp
        (ambientSourceProjector i j)))

/-- On the genuine Hodge fiber, the ambient universal word is exactly the
rank-free matrix unit. -/
theorem ambientUniversalTwoSlotWord_on_hodge
    (i j : ClassicalHodgeBasisIndex V H p)
    (alpha : HFiber V H p) :
    ambientUniversalTwoSlotWord i j alpha.1 =
      (hodgeMatrixUnit i j alpha).1 := by
  have hword :
      forwardArsenalWord sourceSlot targetSlot =
        pureMatrixUnit sourceSlot targetSlot :=
    forwardArsenalWord_eq_matrixUnit sourceSlot targetSlot (by decide)
  have hlift :
      liftFiniteHodgeOperator (pairBasisIndex i j)
          (forwardArsenalWord sourceSlot targetSlot) =
        hodgeMatrixUnit i j := by
    exact rankFreeMatrixUnit_eq_lifted_GST_word i j |>.symm
  have hsrc := extendHodgeEndomorphism_on_hodge
    (V:=V) (H:=H)
    (twoSlotHodgeOperator i j (sheetProjectorQ sourceSlot)) alpha
  have hL := extendHodgeEndomorphism_on_hodge
    (V:=V) (H:=H)
    (twoSlotHodgeOperator i j (diagonalLefschetzQ 2 2))
    ((twoSlotHodgeOperator i j (sheetProjectorQ sourceSlot)) alpha)
  have htgt := extendHodgeEndomorphism_on_hodge
    (V:=V) (H:=H)
    (twoSlotHodgeOperator i j (sheetProjectorQ targetSlot))
    ((twoSlotHodgeOperator i j (diagonalLefschetzQ 2 2))
      ((twoSlotHodgeOperator i j (sheetProjectorQ sourceSlot)) alpha))
  change _ = _
  rw [ambientUniversalTwoSlotWord]
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  simp only [ambientSourceProjector, ambientTwoStepLefschetz,
    ambientTargetProjector]
  rw [hsrc, hL, htgt]
  change
    ((forwardScalar sourceSlot targetSlot : ℚ)⁻¹ •
      (twoSlotHodgeOperator i j (sheetProjectorQ targetSlot))
        ((twoSlotHodgeOperator i j (diagonalLefschetzQ 2 2))
          ((twoSlotHodgeOperator i j (sheetProjectorQ sourceSlot)) alpha))).1 = _
  -- The write map on pure basis sheets.
  have hW : ∀ (k : ℚ) (r : Fin 2),
      finiteHodgeWrite (pairBasisIndex i j) (k • rationalPureBasis r) =
        k • classicalHodgeBasis V H p (pairBasisIndex i j r) := by
    intro k r
    simp only [finiteHodgeWrite, map_smul, Fin.sum_univ_two]
    fin_cases r <;> simp [rationalPureBasis]
  -- The normalized forward Lefschetz word moves the source sheet to the
  -- target sheet with the exact forward scalar, and kills the target sheet.
  have hb0 : diagonalLefschetzQ 2 2 (rationalPureBasis sourceSlot)
      = (forwardScalar sourceSlot targetSlot : ℚ)
        • rationalPureBasis targetSlot := by
    have hop : diagonalLefschetzQ 2 2
        = diagonalLefschetzQ 2 (2 * GSTPureHodgeLefschetzKernel.pureWeightGap
            (Fin.castLE (show 2 ≤ min 2 2 by omega) (0 : Fin 2))
            (Fin.castLE (show 2 ≤ min 2 2 by omega) (1 : Fin 2))) := rfl
    rw [hop]
    funext q
    fin_cases q <;>
      simp [diagonalLefschetzQ, Fin.sum_univ_two, rationalPureBasis]
    · rw [GSTPureHodgeLefschetzKernel.pure_diagonal_lefschetz_wrong_time_zero
        (A := 2) (B := 2)
        (0 : Fin 2) (0 : Fin 2)
        (show (0 : ℕ) ≤ 0 by decide)
        (show 2 * GSTPureHodgeLefschetzKernel.pureWeightGap (A := 2) (B := 2)
            (0 : Fin 2) (1 : Fin 2)
          ≠ 2 * GSTPureHodgeLefschetzKernel.pureWeightGap (A := 2) (B := 2)
            (0 : Fin 2) (0 : Fin 2) by decide)]
      norm_num [forwardScalar, sourceSlot, targetSlot]
    · rw [GSTPureHodgeLefschetzKernel.pure_diagonal_lefschetz_kernel
        (A := 2) (B := 2)
        (n := 2 * GSTPureHodgeLefschetzKernel.pureWeightGap (A := 2) (B := 2) (0 : Fin 2) (1 : Fin 2))
        (0 : Fin 2) (1 : Fin 2)]
      norm_num [forwardScalar, sourceSlot, targetSlot,
        GSTPureHodgeLefschetzKernel.pureWeightGap]
  have hb1 : diagonalLefschetzQ 2 2 (rationalPureBasis targetSlot) = 0 := by
    have hop : diagonalLefschetzQ 2 2
        = diagonalLefschetzQ 2 (2 * GSTPureHodgeLefschetzKernel.pureWeightGap
            (Fin.castLE (show 2 ≤ min 2 2 by omega) (0 : Fin 2))
            (Fin.castLE (show 2 ≤ min 2 2 by omega) (1 : Fin 2))) := rfl
    rw [hop]
    funext q
    fin_cases q <;>
      simp [diagonalLefschetzQ, Fin.sum_univ_two, rationalPureBasis]
    · rw [GSTPureHodgeLefschetzKernel.pure_diagonal_lefschetz_backward_zero
        (A := 2) (B := 2)
        (1 : Fin 2) (0 : Fin 2)
        (show (0:ℕ) < 1 by decide)]
      norm_num [forwardScalar, sourceSlot, targetSlot]
    · rw [GSTPureHodgeLefschetzKernel.pure_diagonal_lefschetz_wrong_time_zero
        (A := 2) (B := 2)
        (1 : Fin 2) (1 : Fin 2)
        (show (1 : ℕ) ≤ 1 by decide)
        (show 2 * GSTPureHodgeLefschetzKernel.pureWeightGap (A := 2) (B := 2)
            (0 : Fin 2) (1 : Fin 2)
          ≠ 2 * GSTPureHodgeLefschetzKernel.pureWeightGap (A := 2) (B := 2)
            (1 : Fin 2) (1 : Fin 2) by decide)]
      norm_num [forwardScalar, sourceSlot, targetSlot]
  -- Hence the two-slot Lefschetz word reads only the source sheet.
  have hdiag : ∀ w : RationalPureWindow 2,
      diagonalLefschetzQ 2 2 w
        = ((w sourceSlot) * (forwardScalar sourceSlot targetSlot : ℚ))
          • rationalPureBasis targetSlot := by
    intro w
    have hw : w = (w sourceSlot) • rationalPureBasis sourceSlot
        + (w targetSlot) • rationalPureBasis targetSlot := by
      classical
      funext r
      fin_cases r <;> simp [rationalPureBasis, sourceSlot, targetSlot]
    rw [hw]
    simp only [map_add, map_smul, hb0, hb1, smul_zero, add_zero, smul_smul]
    simp [rationalPureBasis, sourceSlot, targetSlot]
  -- The three fiber-level steps of the ambient universal two-slot word.
  have hstep1 : (twoSlotHodgeOperator i j (sheetProjectorQ sourceSlot)) alpha
      = (hodgeCoordinate i) alpha • classicalHodgeBasis V H p i := by
    have hsrc : (sheetProjectorQ sourceSlot)
        ((finiteHodgeRead (pairBasisIndex i j)) alpha)
        = ((hodgeCoordinate i) alpha) • rationalPureBasis sourceSlot := by
      rfl
    simp only [twoSlotHodgeOperator, liftFiniteHodgeOperator,
      LinearMap.comp_apply, hsrc, hW, pairBasisIndex_source]
  have hstep2 : (twoSlotHodgeOperator i j (diagonalLefschetzQ 2 2))
        ((hodgeCoordinate i) alpha • classicalHodgeBasis V H p i)
      = (((hodgeCoordinate i) alpha)
          * (forwardScalar sourceSlot targetSlot : ℚ))
        • classicalHodgeBasis V H p j := by
    have hread : (finiteHodgeRead (pairBasisIndex i j))
        ((hodgeCoordinate i) alpha • classicalHodgeBasis V H p i) sourceSlot
        = (hodgeCoordinate i) alpha := by
      simp [finiteHodgeRead]
    simp only [twoSlotHodgeOperator, liftFiniteHodgeOperator,
      LinearMap.comp_apply, hdiag, hread, hW, pairBasisIndex_target]
  have hstep3 : (twoSlotHodgeOperator i j (sheetProjectorQ targetSlot))
        ((((hodgeCoordinate i) alpha)
          * (forwardScalar sourceSlot targetSlot : ℚ))
          • classicalHodgeBasis V H p j)
      = (((hodgeCoordinate i) alpha)
          * (forwardScalar sourceSlot targetSlot : ℚ))
        • classicalHodgeBasis V H p j := by
    have hread2 : (finiteHodgeRead (pairBasisIndex i j))
        ((((hodgeCoordinate i) alpha)
          * (forwardScalar sourceSlot targetSlot : ℚ))
          • classicalHodgeBasis V H p j) targetSlot
        = ((hodgeCoordinate i) alpha)
          * (forwardScalar sourceSlot targetSlot : ℚ) := by
      simp [finiteHodgeRead]
    simp only [twoSlotHodgeOperator, liftFiniteHodgeOperator,
      LinearMap.comp_apply, sheetProjectorQ_apply, hread2, hW,
      pairBasisIndex_target]
  rw [hstep1, hstep2, hstep3, hodgeMatrixUnit_apply]
  have hc : (forwardScalar sourceSlot targetSlot : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (forwardScalar_pos sourceSlot targetSlot))
  have hscalar : (forwardScalar sourceSlot targetSlot : ℚ)⁻¹ *
      ((hodgeCoordinate i) alpha *
        (forwardScalar sourceSlot targetSlot : ℚ)) =
      (hodgeCoordinate i) alpha := by
    field_simp
  show ((forwardScalar sourceSlot targetSlot : ℚ)⁻¹ •
      (((hodgeCoordinate i) alpha *
        (forwardScalar sourceSlot targetSlot : ℚ)) •
        classicalHodgeBasis V H p j)).1 =
    ((hodgeCoordinate i) alpha • classicalHodgeBasis V H p j).1
  rw [Submodule.coe_smul, Submodule.coe_smul, smul_smul, hscalar]
  simp [Submodule.coe_smul]

/-- Primitive native-natural data for the universal two-slot machine. -/
structure PrimitiveNativeTwoSlot
    (i j : ClassicalHodgeBasisIndex V H p) where
  source : HasNativePointLifts
    (p:=p) (cl:=H.cycleClass p) (ambientSourceProjector i j)
  lefschetz : HasNativePointLifts
    (p:=p) (cl:=H.cycleClass p) (ambientTwoStepLefschetz i j)
  target : HasNativePointLifts
    (p:=p) (cl:=H.cycleClass p) (ambientTargetProjector i j)

namespace PrimitiveNativeTwoSlot

/-- Native point-lift naturality of the complete universal word follows from
the three primitive point-lift laws. -/
theorem universalWord_nativePointLifts
    {i j : ClassicalHodgeBasisIndex V H p}
    (R : PrimitiveNativeTwoSlot (V:=V) (H:=H) i j) :
    HasNativePointLifts (p:=p) (cl:=H.cycleClass p)
      (ambientUniversalTwoSlotWord i j) := by
  have hS : AtomicSpanStable (p:=p) (cl:=H.cycleClass p)
      (ambientSourceProjector i j) :=
    (smoothProjective_atomicStable_iff_nativePointLifts
      (ambientSourceProjector i j)).mpr R.source
  have hL : AtomicSpanStable (p:=p) (cl:=H.cycleClass p)
      (ambientTwoStepLefschetz i j) :=
    (smoothProjective_atomicStable_iff_nativePointLifts
      (ambientTwoStepLefschetz i j)).mpr R.lefschetz
  have hT : AtomicSpanStable (p:=p) (cl:=H.cycleClass p)
      (ambientTargetProjector i j) :=
    (smoothProjective_atomicStable_iff_nativePointLifts
      (ambientTargetProjector i j)).mpr R.target
  have hcomp : AtomicSpanStable (p:=p) (cl:=H.cycleClass p)
      ((ambientTargetProjector i j).comp
        ((ambientTwoStepLefschetz i j).comp
          (ambientSourceProjector i j))) :=
    fun _ hy => hT _ (hL _ (hS _ hy))
  have hsmul : AtomicSpanStable (p:=p) (cl:=H.cycleClass p)
      ((forwardScalar sourceSlot targetSlot : ℚ)⁻¹ •
        ((ambientTargetProjector i j).comp
          ((ambientTwoStepLefschetz i j).comp
            (ambientSourceProjector i j)))) := by
    intro y hy
    rw [LinearMap.smul_apply]
    exact (GSTClassicalHodgeAtomicSpan.pointCycleClassSpan p
      (H.cycleClass p)).smul_mem _ (hcomp y hy)
  exact nativePointLifts_of_atomicSpanStable
    (ambientUniversalTwoSlotWord i j) hsmul

/-- The full universal two-slot word therefore preserves the entire atomic
cycle-class span. -/
theorem universalWord_atomicStable
    {i j : ClassicalHodgeBasisIndex V H p}
    (R : PrimitiveNativeTwoSlot (V:=V) (H:=H) i j) :
    AtomicSpanStable (p:=p) (cl:=H.cycleClass p)
      (ambientUniversalTwoSlotWord i j) := by
  rw [smoothProjective_atomicStable_iff_nativePointLifts]
  exact R.universalWord_nativePointLifts

end PrimitiveNativeTwoSlot

#check extendHodgeEndomorphism
#check extendHodgeEndomorphism_on_hodge
#check twoSlotHodgeOperator
#check ambientSourceProjector
#check ambientTwoStepLefschetz
#check ambientTargetProjector
#check ambientUniversalTwoSlotWord
#check ambientUniversalTwoSlotWord_on_hodge
#check PrimitiveNativeTwoSlot
#check PrimitiveNativeTwoSlot.universalWord_nativePointLifts
#check PrimitiveNativeTwoSlot.universalWord_atomicStable

#print axioms extendHodgeEndomorphism_on_hodge
#print axioms ambientUniversalTwoSlotWord_on_hodge
#print axioms PrimitiveNativeTwoSlot.universalWord_nativePointLifts
#print axioms PrimitiveNativeTwoSlot.universalWord_atomicStable

end GSTClassicalHodgeUniversalTwoSlotNativeClosure
