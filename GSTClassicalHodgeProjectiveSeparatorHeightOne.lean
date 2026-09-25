import GSTClassicalHodgeHomogeneousQuotientNonunit
import GSTClassicalHodgeProjectiveSeparatorKrull

/-!
# GST CLASSICAL HODGE — EXACT HEIGHT ONE OF THE PROJECTIVE SEPARATOR

The previous projective-Krull layer left a formal dichotomy: after quotienting
by the homogeneous prime represented by a Proj point, the selected positive
homogeneous separator was either a unit or generated a height-one principal
ideal.

The homogeneous quotient nonunit theorem removes the first branch.  A
positive-degree homogeneous element cannot become invertible modulo any
proper homogeneous ideal.  Since a Proj point carries a proper homogeneous
prime and the relevance-selected separator is homogeneous of strictly positive
degree, its quotient class is automatically a nonunit.

Consequently the projective separator has exact principal height one at every
Proj source point.  This is the unconditional local codimension-one receipt
needed by the recursive projective cutting engine.
-/

set_option maxHeartbeats 30000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTClassicalHodgeProjectivePrincipalSection
open GSTClassicalHodgeProjectiveSeparatorKrull
open GSTClassicalHodgeHomogeneousQuotientNonunit

namespace GSTClassicalHodgeProjectiveSeparatorHeightOne

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The selected projective separator cannot become a unit modulo the source
homogeneous prime. -/
theorem separatorClass_not_isUnit
    (n : Nat) (x : projectiveSpace n) :
    ¬ IsUnit (separatorClass n x) := by
  let P := x.asHomogeneousIdeal
  have hhom :
      (positiveHomogeneousSeparator n x).equation ∈
        ProjectiveGrading n (positiveHomogeneousSeparator n x).degree :=
    (positiveHomogeneousSeparator n x).homogeneous
  have hpos : 0 < (positiveHomogeneousSeparator n x).degree :=
    (positiveHomogeneousSeparator n x).degree_pos
  simpa [separatorClass, pointQuotient, P] using
    (quotient_mk_not_isUnit_of_positive_prime
      (ProjectiveGrading n) P hhom hpos)

/-- **UNCONDITIONAL PROJECTIVE HEIGHT-ONE THEOREM.** -/
theorem separatorClass_height_one
    (n : Nat) (x : projectiveSpace n) :
    (Ideal.span ({separatorClass n x} : Set (pointQuotient n x))).height = 1 := by
  exact separator_height_one_of_nonunit n x (separatorClass_not_isUnit n x)

/-- Every minimal prime over the projective separator lies over a genuinely
height-one principal ideal, without a nonunit hypothesis. -/
theorem separator_minimalPrime_height_one_unconditional
    (n : Nat) (x : projectiveSpace n)
    {q : Ideal (pointQuotient n x)}
    (hq : q ∈ (Ideal.span ({separatorClass n x} : Set (pointQuotient n x))).minimalPrimes) :
    (Ideal.span ({separatorClass n x} : Set (pointQuotient n x))).height = 1
      ∧ Ideal.span ({separatorClass n x} : Set (pointQuotient n x)) ≤ q
      ∧ q.IsPrime := by
  exact separator_minimalPrime_height_one n x
    (separatorClass_not_isUnit n x) hq

/-- The old projective Krull dichotomy collapses to its height-one branch. -/
theorem separator_unit_or_height_one_collapses
    (n : Nat) (x : projectiveSpace n) :
    ¬ IsUnit (separatorClass n x)
      ∧ (Ideal.span ({separatorClass n x} : Set (pointQuotient n x))).height = 1 := by
  exact ⟨separatorClass_not_isUnit n x, separatorClass_height_one n x⟩

#check separatorClass_not_isUnit
#check separatorClass_height_one
#check separator_minimalPrime_height_one_unconditional
#check separator_unit_or_height_one_collapses

#print axioms separatorClass_not_isUnit
#print axioms separatorClass_height_one
#print axioms separator_minimalPrime_height_one_unconditional
#print axioms separator_unit_or_height_one_collapses

end GSTClassicalHodgeProjectiveSeparatorHeightOne
