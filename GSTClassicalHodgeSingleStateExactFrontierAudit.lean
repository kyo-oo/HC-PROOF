import GSTClassicalHodgeSingleStateBareLefschetzExtinction

/-!
# GST CLASSICAL HODGE — SINGLE-STATE EXACT FRONTIER AUDIT

The single-state bare-Lefschetz reduction is intentionally tiny, but that makes
it important to identify exactly how much mathematics remains in its one image
condition.

For a minimal primitive ghost `M` and any nonzero algebraic local seed `S`, the
finite two-slot GST calculation already proves

  L^2(S.source) = c * basis(M.sheet)

with `c != 0`.  Since the atomic algebraic cycle-class span is a rational
submodule, membership of the left side is therefore equivalent to membership
of the detected basis sheet itself.

The separator carried by `M` annihilates the entire atomic span and detects
that basis sheet nontrivially.  Consequently the target sheet is not algebraic,
and the single-state image is not algebraic either, under the hypothetical
minimal ghost.

This is an audit theorem, not a negative result about the Hodge conjecture.  It
locates the exact frontier: proving the single-state image algebraic from a
hypothetical failure requires genuinely new geometric input that creates a
native representative of the detected sheet; it cannot be obtained merely by
rearranging the existing two-slot linear algebra.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeSingleStateExactFrontierAudit

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeAtomicAnnihilator
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeMinimalPrimitiveSeparatorGhost
open GSTClassicalHodgeLocalSeedBareLefschetzExtinction
open GSTClassicalHodgeUniversalTwoSlotNativeClosure

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- The basis sheet detected by a minimal primitive ghost is outside the actual
atomic algebraic cycle-class span. -/
theorem minimalGhost_targetBasis_not_mem_atomic
    (G : GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G) :
    (classicalHodgeBasis V H M.weight M.sheet).1 ∉
      pointCycleClassSpan M.weight (H.cycleClass M.weight) := by
  intro hmem
  have hker :
      pointCycleClassSpan M.weight (H.cycleClass M.weight) ≤
        LinearMap.ker M.separator.detector :=
    (annihilatesPointCycles_iff_atomicSpan_le_ker
      M.weight (H.cycleClass M.weight) M.separator.detector).mp
      M.separator.annihilates_atoms
  have hzero := hker hmem
  exact M.separator.detects_basis hzero

/-- Exact audit of the one-state `L^2` frontier: because its scalar is nonzero,
the image is algebraic exactly when the detected target basis sheet is
algebraic. -/
theorem singleState_image_mem_atomic_iff_targetBasis_mem_atomic
    (G : GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    (S : MinimalGhostLocalSeed G M) :
    ambientTwoStepLefschetz S.sourceIndex M.sheet S.source.1 ∈
        pointCycleClassSpan M.weight (H.cycleClass M.weight) ↔
      (classicalHodgeBasis V H M.weight M.sheet).1 ∈
        pointCycleClassSpan M.weight (H.cycleClass M.weight) := by
  let A := pointCycleClassSpan M.weight (H.cycleClass M.weight)
  let c : ℚ :=
    (forwardScalar sourceSlot targetSlot : ℚ) *
      hodgeCoordinate S.sourceIndex S.source
  have hc : c ≠ 0 := by
    exact mul_ne_zero twoSlot_forwardScalar_ne_zero S.sourceCoefficient_ne_zero
  rw [ambientTwoStepLefschetz_on_hodge_coordinate]
  change c • (classicalHodgeBasis V H M.weight M.sheet).1 ∈ A ↔
    (classicalHodgeBasis V H M.weight M.sheet).1 ∈ A
  constructor
  · intro hscaled
    have hinv := A.smul_mem c⁻¹ hscaled
    simpa [hc] using hinv
  · intro htarget
    exact A.smul_mem c htarget

/-- Under the hypothetical minimal ghost, the exact single bare-`L^2` image
used by the extinction theorem is necessarily outside the atomic algebraic
span.  Any proof that puts it back inside must therefore use a genuinely new
geometric construction and immediately destroys the ghost. -/
theorem minimalGhost_singleState_image_not_mem_atomic
    (G : GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    (S : MinimalGhostLocalSeed G M) :
    ambientTwoStepLefschetz S.sourceIndex M.sheet S.source.1 ∉
      pointCycleClassSpan M.weight (H.cycleClass M.weight) := by
  intro himage
  have htarget :=
    (singleState_image_mem_atomic_iff_targetBasis_mem_atomic G M S).mp himage
  exact minimalGhost_targetBasis_not_mem_atomic G M htarget

#check minimalGhost_targetBasis_not_mem_atomic
#check singleState_image_mem_atomic_iff_targetBasis_mem_atomic
#check minimalGhost_singleState_image_not_mem_atomic

#print axioms minimalGhost_targetBasis_not_mem_atomic
#print axioms singleState_image_mem_atomic_iff_targetBasis_mem_atomic
#print axioms minimalGhost_singleState_image_not_mem_atomic

end GSTClassicalHodgeSingleStateExactFrontierAudit
