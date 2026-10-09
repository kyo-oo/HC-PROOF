import GSTClassicalHodgeLefschetzPoincareMatrixGeneration
import GSTClassicalHodgeRankFreePrimitiveGeneration

/-!
# GST CLASSICAL HODGE — RANK-FREE LEFSCHETZ/POINCARE GENERATION

The finite pure-window theorem shows that Lefschetz and Poincare alone
generate every matrix unit.  This module transports that exact identity into
an arbitrary genuine classical Hodge fiber through finite coordinate
localization.

The theorem is deliberately an operator identity, not yet a claim that the
coordinate localization is algebraic.  The latter is the geometric theorem
to be derived on the native-cycle side.
-/

set_option maxHeartbeats 30000000
set_option maxRecDepth 1000000

noncomputable section

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeFullArsenalIrreducibility
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeRankFreePrimitiveGeneration
open GSTClassicalHodgeLefschetzPoincareMatrixGeneration

namespace GSTClassicalHodgeRankFreeLefschetzPoincareGeneration

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Lift of the finite Lefschetz/Poincare word associated to two local slots. -/
noncomputable def liftedLefschetzPoincareWord
    {N : Nat}
    (e : Fin N → ClassicalHodgeBasisIndex V H p)
    (r s : Fin N) :
    Module.End ℚ (ClassicalHodgeFiber V H p) :=
  liftFiniteHodgeOperator e (lefschetzPoincareMatrixWord r s)

/-- Exact finite-to-rank-free conjugation of the LP word. -/
theorem liftedLefschetzPoincareWord_eq_matrixUnit
    {N : Nat}
    (e : Fin N → ClassicalHodgeBasisIndex V H p)
    (r s : Fin N) :
    liftedLefschetzPoincareWord e r s =
      hodgeMatrixUnit (e r) (e s) := by
  unfold liftedLefschetzPoincareWord
  rw [lefschetzPoincareMatrixWord_eq]
  exact liftFiniteHodgeOperator_matrixUnit e r s

/-- Every global matrix unit is the two-slot lift of an operator word built
only from the native GST Lefschetz and Poincare primitives. -/
theorem rankFreeMatrixUnit_eq_twoSlot_LP_word
    (i j : ClassicalHodgeBasisIndex V H p) :
    hodgeMatrixUnit i j =
      liftedLefschetzPoincareWord
        (pairBasisIndex i j) sourceSlot targetSlot := by
  symm
  simpa using
    liftedLefschetzPoincareWord_eq_matrixUnit
      (pairBasisIndex i j) sourceSlot targetSlot

/-- In the universal 2-slot chart, the LP word equals the normalized
one-step Lefschetz shift; Poincare is needed for general finite words but not
for this ordered local source-target chart. -/
theorem universalTwoSlot_LP_word_eq_forwardShift :
    lefschetzPoincareMatrixWord sourceSlot targetSlot =
      pureForwardShift 2 := by
  rw [lefschetzPoincareMatrixWord_eq]
  apply LinearMap.ext
  intro a
  rw [rationalPureWindow_eq_sum_basis a]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro r _
  fin_cases r
  · simp [pureMatrixUnit_basis_source, pureForwardShift_basis,
      sourceSlot, targetSlot]
  · simp [pureMatrixUnit_basis_other, pureForwardShift_basis,
      sourceSlot, targetSlot]

/-- **UNIVERSAL TWO-SLOT LEFSCHETZ FORMULA.**  Every rank-free matrix unit is
the finite localization of the same normalized `L^2` operator. -/
theorem rankFreeMatrixUnit_eq_twoSlot_Lefschetz
    (i j : ClassicalHodgeBasisIndex V H p) :
    hodgeMatrixUnit i j =
      liftFiniteHodgeOperator (pairBasisIndex i j)
        (pureForwardShift 2) := by
  rw [rankFreeMatrixUnit_eq_twoSlot_LP_word,
    liftedLefschetzPoincareWord,
    universalTwoSlot_LP_word_eq_forwardShift]

/-- Rank-free Lefschetz/Poincare generation crown. -/
theorem rank_free_lefschetz_poincare_generation_crown :
    ∀ i j : ClassicalHodgeBasisIndex V H p,
      hodgeMatrixUnit i j =
        liftFiniteHodgeOperator (pairBasisIndex i j)
          (pureForwardShift 2) :=
  rankFreeMatrixUnit_eq_twoSlot_Lefschetz

#check liftedLefschetzPoincareWord
#check liftedLefschetzPoincareWord_eq_matrixUnit
#check rankFreeMatrixUnit_eq_twoSlot_LP_word
#check universalTwoSlot_LP_word_eq_forwardShift
#check rankFreeMatrixUnit_eq_twoSlot_Lefschetz

#print axioms liftedLefschetzPoincareWord_eq_matrixUnit
#print axioms rankFreeMatrixUnit_eq_twoSlot_LP_word
#print axioms universalTwoSlot_LP_word_eq_forwardShift
#print axioms rankFreeMatrixUnit_eq_twoSlot_Lefschetz

end GSTClassicalHodgeRankFreeLefschetzPoincareGeneration
