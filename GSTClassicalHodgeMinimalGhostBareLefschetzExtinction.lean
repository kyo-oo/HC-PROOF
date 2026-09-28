import GSTClassicalHodgeTwoSlotLefschetzCollapse
import GSTClassicalHodgeMinimalGhostNativeOrbitAnnihilation
import GSTClassicalHodgeLimitlessSpinePropagation

/-!
# GST CLASSICAL HODGE — MINIMAL GHOST BARE LEFSCHETZ EXTINCTION

After the two-slot collapse, the least-weight primitive obstruction no longer
needs projector externalization or a complete geometry-first word.

For any ordered pair of genuine Hodge basis directions `(i,j)`, the actual
rationalized GST operator `diagonalLefschetzQ 2 2`, lifted through the canonical
2-slot read/write chart, is already

  forwardScalar(0,1) * E_ij.

The scalar is nonzero.  Hence on any algebraic Hodge source whose i-th
coordinate is nonzero, this one GST primitive lands at a nonzero multiple of
the target basis sheet j.

If the ambient realization of this bare GST `L^2` primitive has native point
lifts, it preserves the actual algebraic cycle-class span.  A minimal separator
must therefore annihilate the image.  But when j is the detected ghost sheet,
the explicit `L^2` formula says the same image is a nonzero scalar multiple of
that detected sheet.  Contradiction.

Thus the least-bad externalization frontier has collapsed to ONE primitive
law: native naturality of the actual two-step GST Lefschetz mixer, plus one
nonzero algebraic source.
-/

set_option maxHeartbeats 90000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeMinimalGhostBareLefschetzExtinction

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeRankFreePrimitiveGeneration
open GSTClassicalHodgeExplicitArsenalGeneration
open GSTClassicalHodgeUniversalTwoSlotNativeClosure
open GSTClassicalHodgeMinimalPrimitiveSeparatorGhost
open GSTClassicalHodgePrimitiveAlgebraicDefect
open GSTClassicalHodgeNativeGeneratorNaturality
open GSTClassicalHodgeMinimalGhostNativeOrbitAnnihilation
open GSTClassicalHodgeTwoSlotLefschetzCollapse
open GSTClassicalHodgeLimitlessSpinePropagation

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Exact action of the ambient two-slot GST `L^2` primitive on any genuine
Hodge vector. -/
theorem ambientTwoStepLefschetz_on_hodge_scaled_matrixUnit
    {p : Nat}
    (i j : ClassicalHodgeBasisIndex V H p)
    (alpha : ClassicalHodgeFiber V H p) :
    ambientTwoStepLefschetz i j alpha.1 =
      (forwardScalar sourceSlot targetSlot : ℚ) •
        (hodgeMatrixUnit i j alpha).1 := by
  rw [ambientTwoStepLefschetz]
  rw [extendHodgeEndomorphism_on_hodge]
  have h := lifted_twoSlotLefschetz_eq_scaled_hodgeMatrixUnit
    (V := V) (H := H) (p := p) i j
  have hfun := LinearMap.congr_fun h alpha
  exact congrArg Subtype.val hfun

/-- Coordinate form: bare GST `L^2` reads coordinate i and writes it directly
into target sheet j with the fixed nonzero forward scalar. -/
theorem ambientTwoStepLefschetz_on_hodge_coordinate
    {p : Nat}
    (i j : ClassicalHodgeBasisIndex V H p)
    (alpha : ClassicalHodgeFiber V H p) :
    ambientTwoStepLefschetz i j alpha.1 =
      ((forwardScalar sourceSlot targetSlot : ℚ) * hodgeCoordinate i alpha) •
        (classicalHodgeBasis V H p j).1 := by
  rw [ambientTwoStepLefschetz_on_hodge_scaled_matrixUnit]
  rw [hodgeMatrixUnit_apply]
  simp [smul_smul]

/-- The exact minimal data for bare-Lefschetz extinction: one algebraic source,
one live source coordinate, and native point lifts for the actual two-step GST
Lefschetz primitive aimed at the detected ghost sheet. -/
structure MinimalGhostBareLefschetzMixing
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G) where
  source : ClassicalHodgeFiber V H M.weight
  source_algebraic : source ∈ AlgebraicHodgeSubspace V H M.weight
  sourceIndex : ClassicalHodgeBasisIndex V H M.weight
  sourceCoefficient_ne_zero : hodgeCoordinate sourceIndex source ≠ 0
  lefschetz_native :
    HasNativePointLifts
      (p := M.weight) (cl := H.cycleClass M.weight)
      (ambientTwoStepLefschetz sourceIndex M.sheet)

/-- **BARE GST LEFSCHETZ EXTINCTION.**
One native-natural two-step GST Lefschetz mixer destroys the minimal ghost. -/
theorem minimalGhost_false_of_bareLefschetzMixing
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    (L : MinimalGhostBareLefschetzMixing G M) : False := by
  have hzero := minimalGhost_annihilates_nativeNatural_image G M
    (ambientTwoStepLefschetz L.sourceIndex M.sheet)
    L.lefschetz_native L.source L.source_algebraic
  rw [ambientTwoStepLefschetz_on_hodge_coordinate] at hzero
  have hscalar :
      (forwardScalar sourceSlot targetSlot : ℚ) *
          hodgeCoordinate L.sourceIndex L.source ≠ 0 :=
    mul_ne_zero twoSlot_forwardScalar_ne_zero L.sourceCoefficient_ne_zero
  exact (smul_ne_zero hscalar M.separator.detects_basis) hzero

/-- Complete Stage-2G landing if every hypothetical least-weight ghost admits
one bare-Lefschetz mixing packet. -/
theorem bigradedBettiHodge_of_minimalGhost_bareLefschetzMixing
    (G : GeometricCycleClassSpine V H)
    (L : ∀ M : MinimalPrimitiveGhost G,
      Nonempty (MinimalGhostBareLefschetzMixing G M)) :
    BigradedBettiHodgeStatement V H := by
  by_contra hnot
  let M : MinimalPrimitiveGhost G := minimalPrimitiveGhostOfFailure G hnot
  exact minimalGhost_false_of_bareLefschetzMixing G M (L M).some

/-- Spine specialization: once the canonical algebraic spine is nonzero at the
least bad weight, any live spine coordinate may serve as the source.  The only
remaining operator input is native naturality of bare two-slot GST `L^2`. -/
theorem minimalGhost_false_of_spine_bareLefschetz
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    (hspine : spineHodgeSeed G M.weight ≠ 0)
    (hL : ∀ i : ClassicalHodgeBasisIndex V H M.weight,
      hodgeCoordinate i (spineHodgeSeed G M.weight) ≠ 0 →
        HasNativePointLifts
          (p := M.weight) (cl := H.cycleClass M.weight)
          (ambientTwoStepLefschetz i M.sheet)) : False := by
  obtain ⟨i, hi⟩ := exists_nonzero_hodgeCoordinate hspine
  exact minimalGhost_false_of_bareLefschetzMixing G M {
    source := spineHodgeSeed G M.weight
    source_algebraic := spineHodgeSeed_algebraic G M.weight
    sourceIndex := i
    sourceCoefficient_ne_zero := hi
    lefschetz_native := hL i hi
  }

/-- Conserved spine charge removes the source-nonvanishing side; only bare GST
`L^2` native naturality remains at the hypothetical least bad weight. -/
theorem bigradedBettiHodge_of_conservedSpine_and_bareLefschetz
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge G)
    (hL : ∀ M : MinimalPrimitiveGhost G,
      ∀ i : ClassicalHodgeBasisIndex V H M.weight,
      hodgeCoordinate i (spineHodgeSeed G M.weight) ≠ 0 →
        HasNativePointLifts
          (p := M.weight) (cl := H.cycleClass M.weight)
          (ambientTwoStepLefschetz i M.sheet)) :
    BigradedBettiHodgeStatement V H := by
  by_contra hnot
  let M : MinimalPrimitiveGhost G := minimalPrimitiveGhostOfFailure G hnot
  exact minimalGhost_false_of_spine_bareLefschetz G M
    (D.spineHodgeSeed_ne_zero M.weight) (hL M)

#check ambientTwoStepLefschetz_on_hodge_scaled_matrixUnit
#check ambientTwoStepLefschetz_on_hodge_coordinate
#check MinimalGhostBareLefschetzMixing
#check minimalGhost_false_of_bareLefschetzMixing
#check bigradedBettiHodge_of_minimalGhost_bareLefschetzMixing
#check minimalGhost_false_of_spine_bareLefschetz
#check bigradedBettiHodge_of_conservedSpine_and_bareLefschetz

#print axioms ambientTwoStepLefschetz_on_hodge_scaled_matrixUnit
#print axioms minimalGhost_false_of_bareLefschetzMixing
#print axioms bigradedBettiHodge_of_minimalGhost_bareLefschetzMixing
#print axioms bigradedBettiHodge_of_conservedSpine_and_bareLefschetz

end GSTClassicalHodgeMinimalGhostBareLefschetzExtinction
