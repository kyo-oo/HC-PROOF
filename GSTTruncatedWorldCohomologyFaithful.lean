import Mathlib
import Mathlib.RingTheory.MvPolynomial.Ideal
import GSTTruncatedWorldCohomologyRing

/-!
# GST TRUNCATED COHOMOLOGY — EXACT MONOMIAL NORMAL FORM

This file begins the faithfulness upgrade for the universal GST cohomology
ring.  The first step is an exact support criterion for the truncation ideal

    (H^B, V^A) ⊂ ℤ[H,V].

A polynomial lies in this ideal exactly when every monomial in its support
crosses at least one rectangular world boundary.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

namespace GSTTruncatedWorldCohomologyFaithful

open MvPolynomial
open GSTTruncatedWorldCohomologyRing

/-- The two exponent vectors generating the rectangular truncation ideal. -/
def truncExponentSet (A B : Nat) : Set (Fin 2 →₀ Nat) :=
  {Finsupp.single (0 : Fin 2) B, Finsupp.single (1 : Fin 2) A}

/-- The existing truncation ideal is literally the monomial ideal generated
by the two rectangular boundary exponent vectors. -/
theorem truncIdeal_eq_monomial_span (A B : Nat) :
    truncIdeal A B =
      Ideal.span
        ((fun s : Fin 2 →₀ Nat => monomial s (1 : ℤ)) ''
          truncExponentSet A B) := by
  unfold truncIdeal truncExponentSet Hpoly Vpoly
  rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.X_pow_eq_monomial]
  congr 1
  ext p
  simp

/-- **EXACT TRUNCATION SUPPORT CRITERION.**
Every supported monomial crosses the H-boundary or the V-boundary, and this
condition is also sufficient for ideal membership. -/
theorem mem_truncIdeal_iff_support_boundary
    (A B : Nat) (p : WorldPoly) :
    p ∈ truncIdeal A B ↔
      ∀ m ∈ p.support,
        B ≤ m (0 : Fin 2) ∨ A ≤ m (1 : Fin 2) := by
  rw [truncIdeal_eq_monomial_span]
  rw [MvPolynomial.mem_ideal_span_monomial_image]
  constructor
  · intro h m hm
    obtain ⟨s, hs, hsm⟩ := h m hm
    rcases hs with hs | hs
    · left
      subst s
      simpa [Finsupp.single_le_iff] using
        (show Finsupp.single (0 : Fin 2) B ≤ m from hsm)
    · right
      subst s
      simpa [Finsupp.single_le_iff] using
        (show Finsupp.single (1 : Fin 2) A ≤ m from hsm)
  · intro h m hm
    rcases h m hm with hB | hA
    · refine ⟨Finsupp.single (0 : Fin 2) B, ?_, ?_⟩
      · exact Or.inl rfl
      · simpa [Finsupp.single_le_iff] using hB
    · refine ⟨Finsupp.single (1 : Fin 2) A, ?_, ?_⟩
      · exact Or.inr rfl
      · simpa [Finsupp.single_le_iff] using hA

/-- Equivalent normal-form statement: outside the ideal there is a surviving
monomial whose two exponents are simultaneously inside the rectangle. -/
theorem not_mem_truncIdeal_iff_exists_live_monomial
    (A B : Nat) (p : WorldPoly) :
    p ∉ truncIdeal A B ↔
      ∃ m ∈ p.support,
        m (0 : Fin 2) < B ∧ m (1 : Fin 2) < A := by
  rw [mem_truncIdeal_iff_support_boundary]
  push_neg
  constructor
  · rintro ⟨m, hm, hB, hA⟩
    exact ⟨m, hm, by omega, by omega⟩
  · rintro ⟨m, hm, hB, hA⟩
    exact ⟨m, hm, by omega, by omega⟩

#check truncIdeal_eq_monomial_span
#check mem_truncIdeal_iff_support_boundary
#check not_mem_truncIdeal_iff_exists_live_monomial

#print axioms truncIdeal_eq_monomial_span
#print axioms mem_truncIdeal_iff_support_boundary
#print axioms not_mem_truncIdeal_iff_exists_live_monomial

end GSTTruncatedWorldCohomologyFaithful
