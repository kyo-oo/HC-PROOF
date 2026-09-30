import Mathlib
import GSTUniversalLefschetzCausalGeometry
import GSTHodgePoincareStrands

/-!
# GST UNIVERSAL LEFSCHETZ — POINCARE TRANSPOSE GEOMETRY

The universal Lefschetz kernel is causal, but its transpose should not be
interpreted as a second backwards-time law.  The dimension-free GST Poincare
involution already supplies the correct geometric reverse chart.

For every finite rectangular world and every time `n`, complement reverses the
causal order while preserving the two coordinate differences.  Hence the exact
binomial Lefschetz kernel satisfies

    K_n(s,t) = K_n(D t, D s).

Equivalently, at matrix level,

    K_n^t = D K_n D.

Thus a transpose coefficient is an ordinary forward Lefschetz coefficient in
the Poincare-dual chart.  This is intrinsic GST geometry; no abstract adjoint
or Hodge realization is introduced.

The same involution turns a forward row into its canonical Gram probe:

    <r, D^* r>_top = sum_c r(c)^2.

This is the dimension-free geometric form of the positive normal energy used
by the principal-cut flag attack.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

namespace GSTUniversalLefschetzPoincareTranspose

open GSTWorldCosmology
open GSTGradedWorldAlgebra
open GSTWorldPoincareDuality
open GSTUniversalLefschetzKernel
open GSTUniversalLefschetzCausalGeometry
open GSTHodgePoincareStrands
open scoped BigOperators

/-- Poincare complement reverses the exact GST causal order. -/
theorem worldForward_dual_reverse_iff
    {A B : Nat} (s t : WorldCell A B) :
    worldForward (worldDual t) (worldDual s) ↔ worldForward s t := by
  rcases s with ⟨⟨Cs,hCs⟩,⟨ds,hds⟩⟩
  rcases t with ⟨⟨Ct,hCt⟩,⟨dt,hdt⟩⟩
  unfold worldForward worldDual complementFin
  dsimp only
  omega

/-- Carry displacement is unchanged by reversing both endpoints through
Poincare complement. -/
theorem carryDistance_dual_reverse
    {A B : Nat} (s t : WorldCell A B) :
    carryDistance (worldDual t) (worldDual s) = carryDistance s t := by
  rcases s with ⟨⟨Cs,hCs⟩,⟨ds,hds⟩⟩
  rcases t with ⟨⟨Ct,hCt⟩,⟨dt,hdt⟩⟩
  unfold carryDistance worldDual complementFin
  dsimp only
  omega

/-- Digit displacement is unchanged by the same Poincare reversal. -/
theorem digitDistance_dual_reverse
    {A B : Nat} (s t : WorldCell A B) :
    digitDistance (worldDual t) (worldDual s) = digitDistance s t := by
  rcases s with ⟨⟨Cs,hCs⟩,⟨ds,hds⟩⟩
  rcases t with ⟨⟨Ct,hCt⟩,⟨dt,hdt⟩⟩
  unfold digitDistance worldDual complementFin
  dsimp only
  omega

/-- Therefore the intrinsic causal time is Poincare-reversal invariant. -/
theorem worldCausalDistance_dual_reverse
    {A B : Nat} (s t : WorldCell A B) :
    worldCausalDistance (worldDual t) (worldDual s) =
      worldCausalDistance s t := by
  unfold worldCausalDistance
  rw [carryDistance_dual_reverse, digitDistance_dual_reverse]

/-- **POINCARE TRANSPOSE KERNEL LAW.**

Every matrix coefficient of `L^n` equals the reversed coefficient in the
Poincare-dual chart.  In matrix language this is `(L^n)^t = D (L^n) D`. -/
theorem worldAct_L_pow_basis_poincare_transpose
    (A B n : Nat) (s t : WorldCell A B) :
    worldAct A B ((L A B)^n) (worldBasis s) t =
      worldAct A B ((L A B)^n)
        (worldBasis (worldDual t)) (worldDual s) := by
  rw [worldAct_L_pow_basis_kernel, worldAct_L_pow_basis_kernel]
  by_cases hfuture : worldForward s t
  · have hdual : worldForward (worldDual t) (worldDual s) :=
      (worldForward_dual_reverse_iff s t).2 hfuture
    simp [hfuture, hdual, worldCausalDistance_dual_reverse,
      digitDistance_dual_reverse]
  · have hdual : ¬ worldForward (worldDual t) (worldDual s) := by
      intro h
      exact hfuture ((worldForward_dual_reverse_iff s t).1 h)
    simp [hfuture, hdual]

/-- A forward row of the exact universal Lefschetz kernel. -/
def lefschetzForwardRow
    (A B n : Nat) (s : WorldCell A B) : WorldCoef A B :=
  fun t => worldAct A B ((L A B)^n) (worldBasis s) t

/-- Poincare duality converts a coefficient field into its exact Gram probe.
The top pairing is the sum of coordinate squares in every dimension. -/
theorem worldTopPairing_dualPullback_self
    {A B : Nat} (f : WorldCoef A B) :
    worldTopPairing f (worldDualPullback f) =
      ∑ c : WorldCell A B, f c * f c := by
  classical
  unfold worldTopPairing worldDualPullback
  simp

/-- **LIMITLESS LEFSCHETZ GRAM/POINCARE LAW.**
The squared energy of an entire forward `L^n` row is one native Poincare top
pairing against the dualized copy of that same forward row. -/
theorem lefschetzForwardRow_gram_eq_poincare
    (A B n : Nat) (s : WorldCell A B) :
    worldTopPairing
        (lefschetzForwardRow A B n s)
        (worldDualPullback (lefschetzForwardRow A B n s)) =
      ∑ t : WorldCell A B,
        worldAct A B ((L A B)^n) (worldBasis s) t *
          worldAct A B ((L A B)^n) (worldBasis s) t := by
  simpa [lefschetzForwardRow] using
    (worldTopPairing_dualPullback_self (lefschetzForwardRow A B n s))

/-- Crown collecting the two geometric facts needed by a flag-normal attack:
transpose is dual forward propagation, and its diagonal Gram return is a native
Poincare energy. -/
theorem universal_lefschetz_poincare_transpose_crown :
    (∀ A B n (s t : WorldCell A B),
      worldAct A B ((L A B)^n) (worldBasis s) t =
        worldAct A B ((L A B)^n)
          (worldBasis (worldDual t)) (worldDual s))
    ∧ (∀ A B n (s : WorldCell A B),
      worldTopPairing
          (lefschetzForwardRow A B n s)
          (worldDualPullback (lefschetzForwardRow A B n s)) =
        ∑ t : WorldCell A B,
          worldAct A B ((L A B)^n) (worldBasis s) t *
            worldAct A B ((L A B)^n) (worldBasis s) t) := by
  exact ⟨
    fun A B n s t => worldAct_L_pow_basis_poincare_transpose A B n s t,
    fun A B n s => lefschetzForwardRow_gram_eq_poincare A B n s⟩

#check worldForward_dual_reverse_iff
#check carryDistance_dual_reverse
#check digitDistance_dual_reverse
#check worldCausalDistance_dual_reverse
#check worldAct_L_pow_basis_poincare_transpose
#check lefschetzForwardRow
#check worldTopPairing_dualPullback_self
#check lefschetzForwardRow_gram_eq_poincare
#check universal_lefschetz_poincare_transpose_crown

#print axioms worldForward_dual_reverse_iff
#print axioms worldAct_L_pow_basis_poincare_transpose
#print axioms worldTopPairing_dualPullback_self
#print axioms lefschetzForwardRow_gram_eq_poincare
#print axioms universal_lefschetz_poincare_transpose_crown

end GSTUniversalLefschetzPoincareTranspose
