import GSTMultiAxisCosmology

/-!
# Arbitrarily weighted GST sectors and universal causal extinction

A finite native world supports every nonnegative axis weighting. Any integer
linear operator raising this grading has a dimension-derived extinction
bound. The result is independent of the operator's coefficients or formula.
-/
noncomputable section
namespace GSTMultiAxisGradedDynamics
open GSTMultiAxisCosmology
open scoped BigOperators
variable {I : Type*} [Fintype I] (d w : I → ℕ)

def degree (c : Cell d) : ℕ := ∑ i, w i * (c i).val

def topDegree : ℕ := ∑ i, w i * (d i - 1)

def sector (k : ℕ) (g : Coef d) : Coef d :=
  fun c => if degree d w c = k then g c else 0

theorem degree_le_top (c : Cell d) : degree d w c ≤ topDegree d w := by
  apply Finset.sum_le_sum
  intro i hi
  apply Nat.mul_le_mul_left
  have := (c i).isLt
  omega

@[simp] theorem sector_idempotent (k : ℕ) (g : Coef d) :
    sector d w k (sector d w k g) = sector d w k g := by
  funext c
  simp only [sector]
  split_ifs <;> rfl

theorem sector_orthogonal (k l : ℕ) (h : k ≠ l) (g : Coef d) :
    sector d w k (sector d w l g) = 0 := by
  funext c
  by_cases hc : degree d w c = k
  · simp [sector, hc, h]
  · simp [sector, hc]

/-- All weighted sectors reconstruct the entire native coefficient world. -/
theorem sector_sum (g : Coef d) :
    (∑ k ∈ Finset.range (topDegree d w + 1), sector d w k g) = g := by
  classical
  funext c
  simp only [Finset.sum_apply, sector]
  have hc : degree d w c ∈ Finset.range (topDegree d w+1) :=
    Finset.mem_range.mpr (by have := degree_le_top d w c; omega)
  simp [hc]

theorem sector_zero_above (k : ℕ) (hk : topDegree d w < k) (g : Coef d) :
    sector d w k g = 0 := by
  funext c
  have hn : degree d w c ≠ k := by have := degree_le_top d w c; omega
  simp [sector, hn]

/-- The weighted degree shift is exactly the weighted displacement. -/
theorem shift_sector (m : I → ℕ) (k : ℕ) (g : Coef d) :
    shift d m (sector d w k g) =
      sector d w (k + ∑ i, w i * m i) (shift d m g) := by
  classical
  funext c
  by_cases h : ∀ i, m i ≤ (c i).val
  · let b : Cell d := fun i => ⟨(c i).val - m i,
        lt_of_le_of_lt (Nat.sub_le _ _) (c i).isLt⟩
    have hb : degree d w b + (∑ i, w i * m i) = degree d w c := by
      unfold degree
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      change w i * ((c i).val - m i) + w i * m i = w i * (c i).val
      rw [← Nat.mul_add, Nat.sub_add_cancel (h i)]
    have he : degree d w b = k ↔ degree d w c = k + ∑ i, w i * m i := by omega
    simp only [shift, dif_pos h, sector]
    change (if degree d w b = k then g b else 0) =
      if degree d w c = k + ∑ i, w i * m i then g b else 0
    rw [he]
  · simp [shift, sector, h]

/-- Every weighting has an exact complementary degree reflection. -/
theorem weighted_dual_degree (c : Cell d) :
    degree d w (dual d c) + degree d w c = topDegree d w := by
  unfold degree topDegree
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Nat.mul_add]
  congr 1
  have := (c i).isLt
  simp only [dual]
  omega

/-- An operator's native degree-raising law. -/
def Raises (r : ℕ) (T : Module.End ℤ (Coef d)) : Prop :=
  ∀ k g, T (sector d w k g) = sector d w (k+r) (T g)

/-- Degree laws compose for every operator, not just a polarization sum. -/
theorem raises_pow (r : ℕ) (T : Module.End ℤ (Coef d))
    (hT : Raises d w r T) (n : ℕ) : Raises d w (n*r) (T^n) := by
  intro k g
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih, hT]
    rw [Module.End.mul_apply]
    congr 1
    omega

/-- Universal extinction: every positive-degree native operator dies when
its accumulated degree exceeds the world's weighted top degree. -/
theorem raising_operator_extinction (r n : ℕ) (T : Module.End ℤ (Coef d))
    (hT : Raises d w r T) (hn : topDegree d w < n*r) : T^n = 0 := by
  apply LinearMap.ext
  intro g
  rw [← sector_sum d w g, map_sum]
  apply Finset.sum_eq_zero
  intro k hk
  rw [raises_pow d w r T hT n k g, sector_zero_above d w (k+n*r) (by omega)]

/-- Uniform extinction at top+1 steps for any positive degree increment. -/
theorem raising_operator_nilpotent (r : ℕ) (hr : 0 < r)
    (T : Module.End ℤ (Coef d)) (hT : Raises d w r T) :
    T^(topDegree d w+1) = 0 := by
  apply raising_operator_extinction d w r _ T hT
  have h := Nat.mul_le_mul_left (topDegree d w+1) hr
  nlinarith

#print axioms sector_sum
#print axioms shift_sector
#print axioms weighted_dual_degree
#print axioms raises_pow
#print axioms raising_operator_extinction
#print axioms raising_operator_nilpotent
end GSTMultiAxisGradedDynamics
