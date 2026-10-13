import Mathlib

/-!
# CM four-factor switch arithmetic and finite period extraction

A mathematically independent piece of the four-factor reduction in
OpenAI's 2026-09-30 manuscript "The rational Hodge conjecture for
CM abelian varieties", build/sections/02-tensors.tex and
03-surface.tex.

This file proves only the combinatorial sign preservation and finite
nonvanishing selection consumed by the geometric argument. It DOES NOT
assert that a balanced CM tensor is algebraic, DOES NOT import the
unformalized theta/surface theorem, and does not assume Hodge.

Reference:
https://github.com/openai/math/tree/main/preprints/The-rational-Hodge-conjecture-for-CM-abelian-varieties-September-30-2026
-/

noncomputable section
namespace GSTClassicalHodgeCMFourFactorGeometry

universe u
variable {Ω : Type u} [DecidableEq Ω]

/-- Exchange two CM sign rows at one Galois coordinate AND its complex
conjugate. Pairwise swapping is the arithmetic move in the four-factor
switch reduction; algebraicity of the corresponding tensor is separate. -/
def pairedSwitchLeft (c : Ω → Ω) (i : Ω) (a b : Ω → ℤ) : Ω → ℤ :=
  fun j => if j = i ∨ j = c i then b j else a j

def pairedSwitchRight (c : Ω → Ω) (i : Ω) (a b : Ω → ℤ) : Ω → ℤ :=
  fun j => if j = i ∨ j = c i then a j else b j

/-- Every paired switch conserves the pointwise sum of the two CM signs. -/
theorem pairedSwitch_preserves_balance
    (c : Ω → Ω) (i : Ω) (a b : Ω → ℤ) (j : Ω) :
    pairedSwitchLeft c i a b j + pairedSwitchRight c i a b j =
      a j + b j := by
  by_cases h : j = i ∨ j = c i
  · simp [pairedSwitchLeft, pairedSwitchRight, h, add_comm]
  · simp [pairedSwitchLeft, pairedSwitchRight, h]

/-- Conjugate coordinate selection is invariant under an involution. -/
theorem conjugate_selection_iff
    (c : Ω → Ω) (hc : ∀ x, c (c x) = x) (i j : Ω) :
    (c j = i ∨ c j = c i) ↔ (j = i ∨ j = c i) := by
  constructor
  · intro h
    rcases h with h | h
    · right
      calc
        j = c (c j) := (hc j).symm
        _ = c i := congrArg c h
    · left
      calc
        j = c (c j) := (hc j).symm
        _ = c (c i) := congrArg c h
        _ = i := hc i
  · intro h
    rcases h with h | h
    · right
      exact congrArg c h
    · left
      simpa [h, hc i]

/-- CM oddness means antipodal signs at conjugate embeddings. -/
def IsCMOdd (c : Ω → Ω) (a : Ω → ℤ) : Prop :=
  ∀ j, a (c j) = -a j

/-- Switching both conjugate coordinates preserves oddness of the left row. -/
theorem pairedSwitchLeft_odd
    (c : Ω → Ω) (hc : ∀ x, c (c x) = x)
    (i : Ω) (a b : Ω → ℤ)
    (ha : IsCMOdd c a) (hb : IsCMOdd c b) :
    IsCMOdd c (pairedSwitchLeft c i a b) := by
  intro j
  change
    (if c j = i ∨ c j = c i then b (c j) else a (c j)) =
      -(if j = i ∨ j = c i then b j else a j)
  by_cases h : j = i ∨ j = c i
  · have hconj : c j = i ∨ c j = c i :=
      (conjugate_selection_iff c hc i j).2 h
    simp [h, hconj, hb j]
  · have hconj : ¬ (c j = i ∨ c j = c i) := by
      intro h'
      exact h ((conjugate_selection_iff c hc i j).1 h')
    simp [h, hconj, ha j]

/-- Switching both conjugate coordinates preserves oddness of the right row. -/
theorem pairedSwitchRight_odd
    (c : Ω → Ω) (hc : ∀ x, c (c x) = x)
    (i : Ω) (a b : Ω → ℤ)
    (ha : IsCMOdd c a) (hb : IsCMOdd c b) :
    IsCMOdd c (pairedSwitchRight c i a b) := by
  intro j
  change
    (if c j = i ∨ c j = c i then a (c j) else b (c j)) =
      -(if j = i ∨ j = c i then a j else b j)
  by_cases h : j = i ∨ j = c i
  · have hconj : c j = i ∨ c j = c i :=
      (conjugate_selection_iff c hc i j).2 h
    simp [h, hconj, ha j]
  · have hconj : ¬ (c j = i ∨ c j = c i) := by
      intro h'
      exact h ((conjugate_selection_iff c hc i j).1 h')
    simp [h, hconj, hb j]

/-- A four-row Hodge-balance relation is preserved by a paired exchange
of its first two rows (the exact algebraic equality used before a switch). -/
theorem fourFactor_balance_after_switch
    (c : Ω → Ω) (i : Ω) (a b d e : Ω → ℤ)
    (h : ∀ j, a j + b j = d j + e j) :
    ∀ j, pairedSwitchLeft c i a b j + pairedSwitchRight c i a b j =
      d j + e j := by
  intro j
  rw [pairedSwitch_preserves_balance]
  exact h j

/-- The coordinate exchange is an involution on the ordered pair of rows. -/
theorem pairedSwitchLeft_twice
    (c : Ω → Ω) (i : Ω) (a b : Ω → ℤ) :
    pairedSwitchLeft c i
        (pairedSwitchLeft c i a b) (pairedSwitchRight c i a b) = a := by
  funext j
  by_cases h : j = i ∨ j = c i
  · simp [pairedSwitchLeft, pairedSwitchRight, h]
  · simp [pairedSwitchLeft, pairedSwitchRight, h]

theorem pairedSwitchRight_twice
    (c : Ω → Ω) (i : Ω) (a b : Ω → ℤ) :
    pairedSwitchRight c i
        (pairedSwitchLeft c i a b) (pairedSwitchRight c i a b) = b := by
  funext j
  by_cases h : j = i ∨ j = c i
  · simp [pairedSwitchLeft, pairedSwitchRight, h]
  · simp [pairedSwitchLeft, pairedSwitchRight, h]

/-- A nonzero finite mixed surface period has at least one nonzero pure
cup-product contribution. This is the exact finite-sum extraction used
in the last assembly step of the CM manuscript. -/
theorem nonzero_mixed_period_has_nonzero_pure_term
    {I J R : Type*} [CommRing R]
    (s : Finset I) (t : Finset J)
    (a : I → R) (b : J → R) (cup : I → J → R)
    (hperiod :
      (∑ i ∈ s, ∑ j ∈ t, a i * b j * cup i j) ≠ 0) :
    ∃ i ∈ s, ∃ j ∈ t, cup i j ≠ 0 := by
  classical
  by_contra hnone
  have hzero : ∀ i ∈ s, ∀ j ∈ t, cup i j = 0 := by
    intro i hi j hj
    by_contra hne
    exact hnone ⟨i, hi, j, hj, hne⟩
  apply hperiod
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j hj
  simp [hzero i hi j hj]

end GSTClassicalHodgeCMFourFactorGeometry
