import GSTClassicalHodgeProjectiveSeparatorKrull
import GSTClassicalHodgeHomogeneousQuotientNonunit

/-!
# GST CLASSICAL HODGE — UNCONDITIONAL HEIGHT-ONE PROJECTIVE SEPARATOR

The projective-separator Krull layer originally retained a formal dichotomy:
a surviving separator class in the point-prime quotient was either a unit or
its principal ideal had height one.

That unit branch is impossible for the separator actually constructed by the
projective geometry.  The separator is homogeneous of strictly positive degree
and the source point is represented by a proper homogeneous prime.  The general
homogeneous-quotient theorem therefore says that its image modulo the source
prime cannot be invertible.

Consequently every relevance-selected projective separator is
unconditionally a genuine height-one equation in the source-prime quotient.
Moreover its principal ideal is proper and therefore has an actual minimal
prime.  This upgrades the earlier dichotomy into an existence-bearing
height-one geometric package.
-/

set_option maxHeartbeats 40000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTClassicalHodgeProjectivePrincipalSection
open GSTClassicalHodgeProjectiveSeparatorKrull
open GSTClassicalHodgeHomogeneousQuotientNonunit

namespace GSTClassicalHodgeProjectiveSeparatorUnconditionalHeightOne

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The relevance-selected positive homogeneous separator cannot become a unit
in the homogeneous prime quotient of its source projective point. -/
theorem separatorClass_not_isUnit
    (n : Nat) (x : projectiveSpace n) :
    ¬ IsUnit (separatorClass n x) := by
  haveI : (x.asHomogeneousIdeal.toIdeal).IsPrime := x.isPrime
  exact quotient_mk_not_isUnit_of_positive_prime
    (ProjectiveGrading n)
    x.asHomogeneousIdeal
    (positiveHomogeneousSeparator_homogeneous n x)
    (positiveHomogeneousSeparator_degree_pos n x)

/-- The separator principal ideal in the source-prime quotient is genuinely
proper. -/
theorem separatorPrincipal_ne_top
    (n : Nat) (x : projectiveSpace n) :
    Ideal.span ({separatorClass n x} : Set (pointQuotient n x)) ≠ ⊤ := by
  rw [Ideal.span_singleton_eq_top]
  exact separatorClass_not_isUnit n x

/-- **UNCONDITIONAL PROJECTIVE HEIGHT-ONE LAW.**
The actual separator chosen at every projective source point always lies in
the height-one branch of Krull's principal ideal theorem. -/
theorem separator_height_one
    (n : Nat) (x : projectiveSpace n) :
    (Ideal.span ({separatorClass n x} : Set (pointQuotient n x))).height = 1 := by
  exact separator_height_one_of_nonunit n x
    (separatorClass_not_isUnit n x)

/-- The old Krull dichotomy therefore canonically collapses to its geometric
height-one alternative. -/
theorem separator_unit_or_height_one_collapses
    (n : Nat) (x : projectiveSpace n) :
    ¬ IsUnit (separatorClass n x)
      ∧ (Ideal.span ({separatorClass n x} : Set (pointQuotient n x))).height = 1 := by
  exact ⟨separatorClass_not_isUnit n x, separator_height_one n x⟩

/-- Any minimal prime over the actual separator principal ideal is now known
unconditionally to lie over a height-one ideal and to be prime; callers no
longer need to thread a nonunit hypothesis. -/
theorem separator_minimalPrime_crown
    (n : Nat) (x : projectiveSpace n)
    {q : Ideal (pointQuotient n x)}
    (hq : q ∈ (Ideal.span ({separatorClass n x} : Set (pointQuotient n x))).minimalPrimes) :
    (Ideal.span ({separatorClass n x} : Set (pointQuotient n x))).height = 1
      ∧ Ideal.span ({separatorClass n x} : Set (pointQuotient n x)) ≤ q
      ∧ q.IsPrime := by
  exact separator_minimalPrime_height_one n x
    (separatorClass_not_isUnit n x) hq

/-- **MINIMAL-PRIME EXISTENCE OVER THE SEPARATOR.**
The proper height-one separator ideal has an actual minimal prime above it. -/
theorem exists_separator_minimalPrime
    (n : Nat) (x : projectiveSpace n) :
    ∃ q : Ideal (pointQuotient n x),
      q ∈ (Ideal.span ({separatorClass n x} : Set (pointQuotient n x))).minimalPrimes := by
  let I : Ideal (pointQuotient n x) :=
    Ideal.span ({separatorClass n x} : Set (pointQuotient n x))
  have hI : I ≠ ⊤ := by
    simpa [I] using separatorPrincipal_ne_top n x
  obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hI
  have hmPrime : m.IsPrime := hm.isPrime
  obtain ⟨q, hq, hqm⟩ := Ideal.exists_minimalPrimes_le hIm
  exact ⟨q, hq⟩

/-- Existence-bearing crown: every source point produces an actual prime above
the separator equation, and the principal equation underneath it has exact
height one. -/
theorem exists_heightOne_separatorPrime
    (n : Nat) (x : projectiveSpace n) :
    ∃ q : Ideal (pointQuotient n x),
      (Ideal.span ({separatorClass n x} : Set (pointQuotient n x))).height = 1
      ∧ Ideal.span ({separatorClass n x} : Set (pointQuotient n x)) ≤ q
      ∧ q.IsPrime := by
  obtain ⟨q,hq⟩ := exists_separator_minimalPrime n x
  exact ⟨q, separator_minimalPrime_crown n x hq⟩

#check separatorClass_not_isUnit
#check separatorPrincipal_ne_top
#check separator_height_one
#check separator_unit_or_height_one_collapses
#check separator_minimalPrime_crown
#check exists_separator_minimalPrime
#check exists_heightOne_separatorPrime

#print axioms separatorClass_not_isUnit
#print axioms separatorPrincipal_ne_top
#print axioms separator_height_one
#print axioms separator_unit_or_height_one_collapses
#print axioms separator_minimalPrime_crown
#print axioms exists_separator_minimalPrime
#print axioms exists_heightOne_separatorPrime

end GSTClassicalHodgeProjectiveSeparatorUnconditionalHeightOne
