import GSTClassicalHodgeExplicitArsenalGeneration
import GSTClassicalHodgeUniversalTwoSlotNativeClosure

/-!
# GST CLASSICAL HODGE — TWO-SLOT LEFSCHETZ COLLAPSE

The general finite-window matrix-unit construction uses

  P_target ∘ L^(2 gap) ∘ P_source.

In the universal two-slot window there are only two pure diagonal states,
`sourceSlot = 0` and `targetSlot = 1`.  A two-step Lefschetz path can only move
from the first diagonal state to the second.  Therefore `L^2` itself already
has rank one: it is the central-binomial forward scalar times `E_01`.

This removes both spectral projectors from the least-bad Hodge attack.  The
only nontrivial GST primitive that must acquire classical native naturality is
the actual rationalized two-step world Lefschetz operator.
-/

set_option maxHeartbeats 90000000
set_option maxRecDepth 1000000

noncomputable section

namespace GSTClassicalHodgeTwoSlotLefschetzCollapse

open GSTWorldCosmology
open GSTTruncatedWorldCohomologyRing
open GSTClassicalHodgeFullArsenalIrreducibility
open GSTClassicalHodgeExplicitArsenalGeneration
open GSTClassicalHodgePrimitiveArsenalRationalization
open GSTClassicalHodgeRankFreePrimitiveGeneration
open GSTClassicalHodgeUniversalTwoSlotNativeClosure

/-- In the two-slot pure diagonal, bare `L^2` is exactly the nonzero forward
scalar times the unique forward matrix unit. -/
theorem diagonalLefschetzQ_two_two_eq_scaled_matrixUnit :
    diagonalLefschetzQ 2 2 =
      (forwardScalar sourceSlot targetSlot : ℚ) •
        pureMatrixUnit sourceSlot targetSlot := by
  apply LinearMap.ext
  intro a
  rw [rationalPureWindow_eq_sum_basis a]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro r _
  fin_cases r
  · have hsrc := rawForwardWord_basis_source
      sourceSlot targetSlot (by simp [sourceSlot, targetSlot])
    have hsourceProj :
        sheetProjectorQ sourceSlot (rationalPureBasis sourceSlot) =
          rationalPureBasis sourceSlot := by
      simp [sheetProjectorQ, rationalPureBasis]
    have htargetProj :
        sheetProjectorQ targetSlot
          (diagonalLefschetzQ 2 2 (rationalPureBasis sourceSlot)) =
        diagonalLefschetzQ 2 2 (rationalPureBasis sourceSlot) := by
      funext q
      fin_cases q <;>
        simp [sheetProjectorQ, diagonalLefschetzQ, rationalPureBasis,
          GSTUniversalLefschetzKernel.worldAct_L_pow_basis_kernel]
    change a sourceSlot • diagonalLefschetzQ 2 2
      (rationalPureBasis sourceSlot) = _
    have hraw :
        diagonalLefschetzQ 2 2 (rationalPureBasis sourceSlot) =
          (forwardScalar sourceSlot targetSlot : ℚ) •
            rationalPureBasis targetSlot := by
      simpa [rawForwardWord, hsourceProj, htargetProj, sourceSlot, targetSlot,
        GSTPureHodgeLefschetzKernel.pureWeightGap] using hsrc
    rw [hraw]
    simp [pureMatrixUnit_basis_source, smul_smul]
  · have hzero :
        diagonalLefschetzQ 2 2 (rationalPureBasis targetSlot) = 0 := by
      funext q
      fin_cases q <;>
        simp [diagonalLefschetzQ, rationalPureBasis,
          GSTUniversalLefschetzKernel.worldAct_L_pow_basis_kernel]
    change a targetSlot • diagonalLefschetzQ 2 2
      (rationalPureBasis targetSlot) = _
    rw [hzero]
    simp [pureMatrixUnit_basis_other]

/-- The forward scalar in the universal two-slot window is nonzero. -/
theorem twoSlot_forwardScalar_ne_zero :
    (forwardScalar sourceSlot targetSlot : ℚ) ≠ 0 := by
  exact_mod_cast (ne_of_gt (forwardScalar_pos sourceSlot targetSlot))

/-- Lifted to any ordered pair of genuine Hodge basis directions, the bare
GST `L^2` primitive is already the same nonzero scalar times the rank-free
matrix unit. -/
theorem lifted_twoSlotLefschetz_eq_scaled_hodgeMatrixUnit
    {V : GSTProjectiveOverC.SmoothProjectiveComplexScheme}
    {H : GSTGeometricRealizationStage2G.HodgeBigradedBettiData V}
    {p : Nat}
    (i j : GSTClassicalHodgeFiberedCosmology.ClassicalHodgeBasisIndex V H p) :
    GSTClassicalHodgeRankFreePrimitiveGeneration.liftFiniteHodgeOperator
        (pairBasisIndex i j) (diagonalLefschetzQ 2 2) =
      (forwardScalar sourceSlot targetSlot : ℚ) •
        GSTClassicalHodgeRankFreeArsenalIrreducibility.hodgeMatrixUnit i j := by
  rw [diagonalLefschetzQ_two_two_eq_scaled_matrixUnit]
  have hsmul : ∀ (c : ℚ) (T : Module.End ℚ (RationalPureWindow 2)),
      liftFiniteHodgeOperator (pairBasisIndex i j) (c • T) =
        c • liftFiniteHodgeOperator (pairBasisIndex i j) T := by
    intro c T
    ext a
    simp [liftFiniteHodgeOperator]
  rw [hsmul]
  rw [liftFiniteHodgeOperator_matrixUnit]
  simp [pairBasisIndex]

#check diagonalLefschetzQ_two_two_eq_scaled_matrixUnit
#check twoSlot_forwardScalar_ne_zero
#check lifted_twoSlotLefschetz_eq_scaled_hodgeMatrixUnit

#print axioms diagonalLefschetzQ_two_two_eq_scaled_matrixUnit
#print axioms lifted_twoSlotLefschetz_eq_scaled_hodgeMatrixUnit

end GSTClassicalHodgeTwoSlotLefschetzCollapse
