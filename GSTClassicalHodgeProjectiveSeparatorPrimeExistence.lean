import GSTClassicalHodgeProjectiveSeparatorHeightOne
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic

/-!
# GST CLASSICAL HODGE — PROJECTIVE SEPARATOR PRIME EXISTENCE

The projective separator stack already proves three strong local facts in the
point-prime quotient:

* the positive homogeneous separator survives nontrivially;
* it is not a unit;
* every minimal prime over its principal ideal has height exactly one.

The remaining algebraic emptiness loophole is eliminated here.  Because the
separator is a nonunit, its principal ideal is proper.  Mathlib's minimal-prime
existence theorem then supplies an actual minimal prime above that principal
ideal.  The existing height theorem immediately upgrades the witness to exact
height one.

Thus every projective source point owns a genuine algebraic height-one prime
successor in its point-prime quotient.  No Hodge data, cycle-class map,
nonvanishing hypothesis or finiteness assumption is used.

This is an algebraic existence receipt.  A later scheme/Proj layer must still
identify the chosen quotient prime with a geometric point of the restricted
principal-cut carrier; that geometric realization is kept explicit rather
than silently assumed.
-/

set_option maxHeartbeats 30000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTClassicalHodgeProjectivePrincipalSection
open GSTClassicalHodgeProjectiveSeparatorKrull
open GSTClassicalHodgeProjectiveSeparatorHeightOne

namespace GSTClassicalHodgeProjectiveSeparatorPrimeExistence

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Principal separator ideal in the source-point quotient. -/
noncomputable def separatorPrincipalIdeal
    (n : Nat) (x : projectiveSpace n) : Ideal (pointQuotient n x) :=
  Ideal.span ({separatorClass n x} : Set (pointQuotient n x))

/-- The principal separator ideal is proper because the separator class is a
nonunit. -/
theorem separatorPrincipalIdeal_ne_top
    (n : Nat) (x : projectiveSpace n) :
    separatorPrincipalIdeal n x ≠ ⊤ := by
  intro htop
  have hu : IsUnit (separatorClass n x) := by
    exact (Ideal.span_singleton_eq_top.mp (by
      simpa [separatorPrincipalIdeal] using htop))
  exact separatorClass_not_isUnit n x hu

/-- The separator principal ideal therefore owns at least one minimal prime. -/
theorem separatorPrincipalIdeal_minimalPrimes_nonempty
    (n : Nat) (x : projectiveSpace n) :
    Nonempty (separatorPrincipalIdeal n x).minimalPrimes := by
  exact Ideal.nonempty_minimalPrimes (separatorPrincipalIdeal_ne_top n x)

/-- **EXISTENT HEIGHT-ONE SEPARATOR PRIME.**
At every projective source point there exists an actual minimal prime over the
surviving separator, and that prime has exact height one. -/
theorem exists_separator_minimalPrime_height_one
    (n : Nat) (x : projectiveSpace n) :
    ∃ q : Ideal (pointQuotient n x),
      q ∈ (separatorPrincipalIdeal n x).minimalPrimes
      ∧ q.height = 1 := by
  obtain ⟨q⟩ := separatorPrincipalIdeal_minimalPrimes_nonempty n x
  refine ⟨q.1, q.2, ?_⟩
  exact separator_minimalPrime_prime_height_one n x (by
    simpa [separatorPrincipalIdeal] using q.2)

/-- Chosen canonical-by-choice height-one prime successor. -/
noncomputable def separatorSuccessorPrime
    (n : Nat) (x : projectiveSpace n) : Ideal (pointQuotient n x) :=
  Classical.choose (exists_separator_minimalPrime_height_one n x)

/-- The chosen successor is minimal over the separator principal ideal. -/
theorem separatorSuccessorPrime_mem_minimalPrimes
    (n : Nat) (x : projectiveSpace n) :
    separatorSuccessorPrime n x ∈
      (separatorPrincipalIdeal n x).minimalPrimes :=
  (Classical.choose_spec (exists_separator_minimalPrime_height_one n x)).1

/-- The chosen successor has exact quotient height one. -/
theorem separatorSuccessorPrime_height_one
    (n : Nat) (x : projectiveSpace n) :
    (separatorSuccessorPrime n x).height = 1 :=
  (Classical.choose_spec (exists_separator_minimalPrime_height_one n x)).2

/-- The separator principal ideal lies below the chosen height-one successor. -/
theorem separatorPrincipalIdeal_le_successorPrime
    (n : Nat) (x : projectiveSpace n) :
    separatorPrincipalIdeal n x ≤ separatorSuccessorPrime n x :=
  (separatorSuccessorPrime_mem_minimalPrimes n x).le

/-- The chosen successor is a genuine prime ideal. -/
noncomputable instance separatorSuccessorPrime_isPrime
    (n : Nat) (x : projectiveSpace n) :
    (separatorSuccessorPrime n x).IsPrime :=
  (separatorSuccessorPrime_mem_minimalPrimes n x).isPrime

/-- **ALGEBRAIC SUCCESSOR CROWN.**
Every projective point has a proper principal separator and an actual
height-one minimal-prime successor above it. -/
theorem projective_separator_prime_existence_crown
    (n : Nat) (x : projectiveSpace n) :
    separatorPrincipalIdeal n x ≠ ⊤
    ∧ separatorSuccessorPrime n x ∈
        (separatorPrincipalIdeal n x).minimalPrimes
    ∧ (separatorSuccessorPrime n x).height = 1
    ∧ separatorPrincipalIdeal n x ≤ separatorSuccessorPrime n x := by
  exact ⟨separatorPrincipalIdeal_ne_top n x,
    separatorSuccessorPrime_mem_minimalPrimes n x,
    separatorSuccessorPrime_height_one n x,
    separatorPrincipalIdeal_le_successorPrime n x⟩

#check separatorPrincipalIdeal
#check separatorPrincipalIdeal_ne_top
#check separatorPrincipalIdeal_minimalPrimes_nonempty
#check exists_separator_minimalPrime_height_one
#check separatorSuccessorPrime
#check separatorSuccessorPrime_mem_minimalPrimes
#check separatorSuccessorPrime_height_one
#check separatorPrincipalIdeal_le_successorPrime
#check projective_separator_prime_existence_crown

#print axioms separatorPrincipalIdeal_ne_top
#print axioms exists_separator_minimalPrime_height_one
#print axioms separatorSuccessorPrime_height_one
#print axioms projective_separator_prime_existence_crown

end GSTClassicalHodgeProjectiveSeparatorPrimeExistence
