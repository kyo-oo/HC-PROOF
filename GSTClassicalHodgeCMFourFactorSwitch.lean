import Mathlib

/-!
# CM four-factor sign-switch geometry

Mathematical source:
OpenAI/math (2026), "The rational Hodge conjecture for CM abelian varieties",
Section 2, four-factor switches, and Section 3, surface criterion.

An elementary four-factor switch replaces a pair of CM sign assignments
with another pair having EXACTLY the same sum at every Galois label.
The tensor type balance follows from this identity, but **algebraicity does
not**.  This file formalizes the unconditionally valid sign combinatorics,
including the conjugation symmetry relevant for CM-type assignments.

This is independent of the Hodge conjecture and uses no new axioms, sorry,
or assumptions about geometric realization.

NEEDS CI RUN LATER.  No Lean compilation is performed in this work session.
-/

set_option maxHeartbeats 2000000

namespace GSTClassicalHodgeCMFourFactorSwitch

variable {I : Type*}

/-- Boolean CM sign assignments indexed by embeddings of a CM field.
`true` represents +1 and `false` represents -1. -/
abbrev SignType (I : Type*) := I → Bool

/-- Each Boolean sign becomes an honest integer sign. -/
def signed (b : Bool) : ℤ := if b then 1 else -1

@[simp] theorem signed_true : signed true = 1 := rfl
@[simp] theorem signed_false : signed false = -1 := rfl

/-- Integer charge of a two-factor CM tensor at a particular embedding. -/
def pairCharge (a b : SignType I) (i : I) : ℤ :=
  signed (a i) + signed (b i)

/-- Four factors are balanced when the two initial charges coincide with
the two final charges at every embedding. -/
def FourFactorBalanced
    (a b u v : SignType I) : Prop :=
  ∀ i, pairCharge a b i = pairCharge u v i

/-- Exchange the two CM sign assignments on an arbitrary subset of
embedding labels.  This is the generalized local square-switch. -/
def splice
    (a b : SignType I) (mask : I → Bool) : SignType I :=
  fun i => if mask i then b i else a i

/-- The complementary splice chooses the other input on each label. -/
def complementarySplice
    (a b : SignType I) (mask : I → Bool) : SignType I :=
  fun i => if mask i then a i else b i

/-- Fundamental four-factor relation: coordinatewise swapping conserves
the exact signed tensor charge for every Galois label. -/
theorem splice_fourFactorBalanced
    (a b : SignType I) (mask : I → Bool) :
    FourFactorBalanced a b (splice a b mask)
      (complementarySplice a b mask) := by
  intro i
  cases hm : mask i with
  | false =>
      simp [pairCharge, splice, complementarySplice, hm]
  | true =>
      simp [pairCharge, splice, complementarySplice, hm, add_comm]

/-- Conservation holds for every integer-weighted linear detector of charge,
not just an individual coordinate. -/
theorem splice_pairCharge_eq
    (a b : SignType I) (mask : I → Bool) :
    pairCharge (splice a b mask) (complementarySplice a b mask) =
      pairCharge a b := by
  funext i
  exact (splice_fourFactorBalanced a b mask i).symm

/-- Oddness under complex conjugation is the CM Hodge-type constraint. -/
def IsOddCMType (conj : I → I) (a : SignType I) : Prop :=
  ∀ i, a (conj i) = ! a i

/-- Allowed switch masks are stable under complex conjugation. -/
def ConjugationInvariant (conj : I → I) (mask : I → Bool) : Prop :=
  ∀ i, mask (conj i) = mask i

/-- Switching conjugate embedding pairs preserves the CM oddness law. -/
theorem splice_preserves_oddCM
    (conj : I → I) (a b : SignType I) (mask : I → Bool)
    (ha : IsOddCMType conj a)
    (hb : IsOddCMType conj b)
    (hm : ConjugationInvariant conj mask) :
    IsOddCMType conj (splice a b mask) := by
  intro i
  cases h : mask i with
  | false =>
      simp [splice, hm i, h, ha i]
  | true =>
      simp [splice, hm i, h, hb i]

/-- The other half of the switch is likewise a legitimate CM assignment. -/
theorem complementarySplice_preserves_oddCM
    (conj : I → I) (a b : SignType I) (mask : I → Bool)
    (ha : IsOddCMType conj a)
    (hb : IsOddCMType conj b)
    (hm : ConjugationInvariant conj mask) :
    IsOddCMType conj (complementarySplice a b mask) := by
  intro i
  cases h : mask i with
  | false =>
      simp [complementarySplice, hm i, h, hb i]
  | true =>
      simp [complementarySplice, hm i, h, ha i]

/-- The full four-switch theorem, with charge and conjugation symmetry proved
simultaneously for the two resulting CM type functions. -/
theorem CM_fourFactor_geometric_switch
    (conj : I → I) (a b : SignType I) (mask : I → Bool)
    (ha : IsOddCMType conj a)
    (hb : IsOddCMType conj b)
    (hm : ConjugationInvariant conj mask) :
    FourFactorBalanced a b
      (splice a b mask) (complementarySplice a b mask) ∧
    IsOddCMType conj (splice a b mask) ∧
    IsOddCMType conj (complementarySplice a b mask) := by
  exact ⟨splice_fourFactorBalanced a b mask,
    splice_preserves_oddCM conj a b mask ha hb hm,
    complementarySplice_preserves_oddCM conj a b mask ha hb hm⟩

/-- Equality of the signed charges is symmetric. -/
theorem fourFactorBalanced_symm
    {a b u v : SignType I}
    (h : FourFactorBalanced a b u v) :
    FourFactorBalanced u v a b := by
  intro i
  exact (h i).symm

/-- Consecutive four-factor replacements preserve balance by transitivity. -/
theorem fourFactorBalanced_trans
    {a b u v x y : SignType I}
    (h₁ : FourFactorBalanced a b u v)
    (h₂ : FourFactorBalanced u v x y) :
    FourFactorBalanced a b x y := by
  intro i
  exact (h₁ i).trans (h₂ i)

/-- The four-factor balance relation is invariant under switching either
pair's factor order; the tensor signs come only from Koszul ordering in the
separate cup-product calculation. -/
theorem fourFactorBalanced_swap_right
    {a b u v : SignType I}
    (h : FourFactorBalanced a b u v) :
    FourFactorBalanced a b v u := by
  intro i
  calc
    pairCharge a b i = pairCharge u v i := h i
    _ = pairCharge v u i := by simp [pairCharge, add_comm]

/-- The conserved charge is independent of whether the embedding signatures
are recorded in `(a,b)` or the swapped `(b,a)` order. -/
theorem pairCharge_comm (a b : SignType I) :
    pairCharge a b = pairCharge b a := by
  funext i
  simp [pairCharge, add_comm]

#check CM_fourFactor_geometric_switch
#check fourFactorBalanced_trans
#print axioms CM_fourFactor_geometric_switch

end GSTClassicalHodgeCMFourFactorSwitch
