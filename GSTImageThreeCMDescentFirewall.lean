import GSTGraphV2CMWaveFusion
import Mathlib

/-!
# GST Image 3 — exact original CM complex-structure descent firewall

The owner's original CM mirror J is a RATIONAL complex structure on
the ORIGINAL twelve-state information world: J(Ju)=-u.

The new rank-adaptive ORIGINAL GST F quotient is valid at all finite
rational ranks, but DOES NOT assert that J itself descends to that
quotient. The following proves this distinction for target rank ONE.

This is NOT a negative result on the user's conditional Hodge
implication. It identifies an impossible extra requirement that
must be REMOVED from the proposed universal geometric compiler:
a rank-one rational Hodge space cannot carry J²=-I.

The original CM operator remains intact on its original source world.
A correct rank-adaptive realization may intertwine the complete
F-function without requiring every source operator to descend.
-/

set_option maxHeartbeats 1000000
noncomputable section

namespace GSTImageThreeCMDescentFirewall

open GSTGraphV2CMWaveFusion

/-- No rational linear endomorphism of a one-dimensional rational
carrier can square to minus the identity. -/
theorem no_rational_CM_on_rank_one
    (j : ℚ →ₗ[ℚ] ℚ)
    (hj : ∀ x : ℚ, j (j x) = -x) : False := by
  let a : ℚ := j 1
  have hs (x : ℚ) : j x = x * a := by
    calc
      j x = j (x • (1 : ℚ)) := by simp
      _ = x • j 1 := by rw [map_smul]
      _ = x * a := by simp [a, smul_eq_mul]
  have ha : a * a = -1 := by
    have h := hj 1
    rw [hs] at h
    simpa only [a, neg_one] using h
  nlinarith [sq_nonneg a]

/-- The ORIGINAL owner's J²=-I cannot be faithfully transported
through ANY surjective rational rank-one quotient together with a
complex-structure action on that quotient. This applies even if an
F-compatible quotient was constructed by the rank-adaptive companion. -/
theorem original_J_cannot_descend_to_rank_one
    (q : WaveSignal →ₗ[ℚ] ℚ)
    (hq : Function.Surjective q)
    (jtarget : ℚ →ₗ[ℚ] ℚ)
    (hintertwine : ∀ u : WaveSignal,
      q (J u) = jtarget (q u)) : False := by
  apply no_rational_CM_on_rank_one jtarget
  intro x
  obtain ⟨u, rfl⟩ := hq x
  calc
    jtarget (jtarget (q u)) =
        jtarget (q (J u)) := by rw [hintertwine u]
    _ = q (J (J u)) := by rw [hintertwine (J u)]
    _ = q (-u) := by rw [J_square]
    _ = -(q u) := by rw [map_neg]

#check no_rational_CM_on_rank_one
#check original_J_cannot_descend_to_rank_one
#print axioms no_rational_CM_on_rank_one
#print axioms original_J_cannot_descend_to_rank_one

end GSTImageThreeCMDescentFirewall
