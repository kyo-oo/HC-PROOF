import GSTClassicalHodgeGhostSpineCosmicLeak
import GSTClassicalHodgeFiberedNativeTensorArsenal
import GSTClassicalHodgeAtomicSpan

/-!
# GST CLASSICAL HODGE — CANONICAL LEAK REALIZATION BARRIER

The transformed counterexample now supplies one completely explicit GST value:
the universal two-slot image of the canonical native spine from its selected
live source coordinate to the ghost-detected sheet.  This file records two
sharp non-circularity facts about that value.

First, because the live source coefficient is nonzero, asking for an actual
native cycle whose cycle class equals the leak is exactly as strong as asking
for an actual native cycle representing the ghost basis sheet itself.  Thus an
"exact leak realization" must not be introduced as a renamed final input.

Second, the existing tensor-product pullback cannot manufacture such a
realization merely by applying a multiplicity rewrite independently of a native
operator and then forgetting the multiplicity label.  The repo's exact descent
theorem forces every such descended tensor native operator to be zero, and its
cycle-class version forces the entire native image to be homologically zero.

Therefore a genuine completion must construct a *coupled* geometric operator:
the target multiplicity transition has to be encoded in the geometry itself,
not appended as an independent GST label rewrite.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeCanonicalLeakRealizationBarrier

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeLimitlessSpinePropagation
open GSTClassicalHodgeSynchronizedDefectOrbit
open GSTClassicalHodgeGhostSpineCosmicLeak
open GSTClassicalHodgeOmniversalSeparatorGhostCrown
open GSTClassicalHodgeFiberedNativePullback
open GSTClassicalHodgeFiberedNativeTensorArsenal

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- The exact cohomology value of the canonical transformed leak. -/
noncomputable def canonicalLeakValue
    (G : GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (E : OmniversalSeparatorGhost G) :
    GSTGeometricRealizationStage2F.RationalSingularCohomology
      H.analytification (2 * E.weight) :=
  (liftFiniteHodgeOperator
    (pairBasisIndex (ghostSpineSeed G M E).sourceIndex E.sheet)
    (forwardArsenalWord sourceSlot targetSlot)
    (ghostSpineSeed G M E).hodge).1

/-- The canonical leak is the nonzero live source coefficient times the ghost
basis vector. -/
theorem canonicalLeakValue_eq
    (G : GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (E : OmniversalSeparatorGhost G) :
    canonicalLeakValue G M E =
      (classicalHodgeBasis V H E.weight).repr
          (ghostSpineSeed G M E).hodge
          (ghostSpineSeed G M E).sourceIndex •
        (classicalHodgeBasis V H E.weight E.sheet).1 := by
  exact ghostSpine_twoSlot_exact G M E

/-- Exact native realization of the canonical leak is equivalent to native
realization of the ghost basis itself.  Division by the live source coefficient
is legal because that coefficient was chosen nonzero. -/
theorem canonicalLeak_in_cycleClassRange_iff_ghostBasis
    (G : GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (E : OmniversalSeparatorGhost G) :
    canonicalLeakValue G M E ∈ LinearMap.range (H.cycleClass E.weight) ↔
      (classicalHodgeBasis V H E.weight E.sheet).1 ∈
        LinearMap.range (H.cycleClass E.weight) := by
  let c : ℚ :=
    (classicalHodgeBasis V H E.weight).repr
      (ghostSpineSeed G M E).hodge
      (ghostSpineSeed G M E).sourceIndex
  have hc : c ≠ 0 := (ghostSpineSeed G M E).sourceCoefficient_ne_zero
  rw [canonicalLeakValue_eq]
  constructor
  · rintro ⟨Z, hZ⟩
    refine ⟨c⁻¹ • Z, ?_⟩
    rw [LinearMap.map_smul, hZ, smul_smul]
    simp [hc]
  · rintro ⟨Z, hZ⟩
    refine ⟨c • Z, ?_⟩
    rw [LinearMap.map_smul, hZ]

/-- For an actual ghost, neither the target basis nor the canonical leak belongs
to the genuine cycle-class range. -/
theorem canonicalLeak_not_in_cycleClassRange
    (G : GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (E : OmniversalSeparatorGhost G) :
    canonicalLeakValue G M E ∉ LinearMap.range (H.cycleClass E.weight) := by
  intro hrange
  have hatomic :
      canonicalLeakValue G M E ∈
        pointCycleClassSpan E.weight (H.cycleClass E.weight) := by
    rw [← smoothProjective_cycleClass_range_eq_atomic_span V H E.weight]
    exact hrange
  have hker :
      pointCycleClassSpan E.weight (H.cycleClass E.weight) ≤
        LinearMap.ker E.separator.detector :=
    (GSTClassicalHodgeAtomicAnnihilator.annihilatesPointCycles_iff_atomicSpan_le_ker
      E.weight (H.cycleClass E.weight) E.separator.detector).mp
      E.separator.annihilates_atoms
  exact ghostSpine_twoSlot_detector_ne_zero G M E (hker hatomic)

/-- A pure multiplicity/native tensor word cannot descend to a nonzero native
operator when there is a second source label.  This is the exact barrier to
externalizing the canonical leak by independent tensor factors. -/
theorem independentTensor_nativeDescent_forces_zero
    {p : Nat}
    (i j k : ClassicalHodgeBasisIndex V H p)
    (hki : k ≠ i)
    (A : Module.End ℚ (codimensionCycles V.X p))
    (hdesc : ∃ B : Module.End ℚ (codimensionCycles V.X p),
      (toNativeCycle V H p).comp (tensorWord i j A) =
        B.comp (toNativeCycle V H p)) :
    A = 0 := by
  exact (tensorWord_descends_native_iff_zero i j k hki A).mp hdesc

/-- Even the weaker demand that an independent tensor word descend only after
cycle class forces the native operator to have identically zero cycle-class
image. -/
theorem independentTensor_cycleClassDescent_forces_homologicalZero
    {p : Nat}
    (i j k : ClassicalHodgeBasisIndex V H p)
    (hki : k ≠ i)
    (A : Module.End ℚ (codimensionCycles V.X p))
    (hdesc : ∃ T : Module.End ℚ
        (GSTGeometricRealizationStage2F.RationalSingularCohomology
          H.analytification (2*p)),
      ((H.cycleClass p).comp (toNativeCycle V H p)).comp (tensorWord i j A) =
        T.comp ((H.cycleClass p).comp (toNativeCycle V H p))) :
    (H.cycleClass p).comp A = 0 := by
  exact (tensorWord_descends_cycleClass_iff_zero i j k hki A).mp hdesc

#check canonicalLeakValue
#check canonicalLeakValue_eq
#check canonicalLeak_in_cycleClassRange_iff_ghostBasis
#check canonicalLeak_not_in_cycleClassRange
#check independentTensor_nativeDescent_forces_zero
#check independentTensor_cycleClassDescent_forces_homologicalZero

#print axioms canonicalLeakValue_eq
#print axioms canonicalLeak_in_cycleClassRange_iff_ghostBasis
#print axioms canonicalLeak_not_in_cycleClassRange
#print axioms independentTensor_nativeDescent_forces_zero
#print axioms independentTensor_cycleClassDescent_forces_homologicalZero

end GSTClassicalHodgeCanonicalLeakRealizationBarrier
