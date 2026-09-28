import GSTClassicalHodgeProjectiveSeparatorPrimeExistence
import GSTClassicalHodgeRelativeSuccessorProjectivePrime
import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology

/-!
# GST CLASSICAL HODGE — HOMOGENEOUS LIFT OF THE SEPARATOR SUCCESSOR

The quotient-prime existence layer produces an actual height-one minimal prime
in the point-prime quotient.  This file lifts that prime back to the original
projective coordinate ring and extracts its homogeneous core.

The construction is canonical from the data already proved:

* lift the chosen quotient prime by comapping the quotient map;
* the lifted ideal is prime;
* it contains the source homogeneous prime;
* it contains the positive homogeneous separator;
* taking homogeneous core preserves primality;
* the source homogeneous prime still lies below the homogeneous core;
* the separator still lies in the homogeneous core;
* because the separator was absent from the source prime, the inclusion is
  strict.

Thus every projective source owns a strict homogeneous-prime successor carrying
the separator.  The only extra condition needed to package this prime as an
actual `Proj` point is exactly the genuine projective relevance condition:
the successor must not contain the irrelevant ideal.  This condition is kept
explicit rather than hidden.

When relevance holds, the constructed `ProjectiveSpectrum` point lies in the
separator principal zero locus and strictly specializes the source point.
This is the precise converse direction to the existing theorem saying that an
already-selected geometric cut successor has the corresponding projective
prime incidence.
-/

set_option maxHeartbeats 40000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTClassicalHodgeProjectivePrincipalSection
open GSTClassicalHodgeProjectiveSeparatorKrull
open GSTClassicalHodgeProjectiveSeparatorHeightOne
open GSTClassicalHodgeProjectiveSeparatorPrimeExistence

namespace GSTClassicalHodgeProjectiveSuccessorRelevance

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The source homogeneous prime, viewed as an ordinary ideal. -/
abbrev sourceProjectivePrimeIdeal
    (n : Nat) (x : projectiveSpace n) : Ideal (ProjectiveCoordinateRing n) :=
  x.asHomogeneousIdeal.toIdeal

/-- Comap of the chosen quotient height-one separator prime to the original
projective coordinate ring. -/
noncomputable def liftedSeparatorPrime
    (n : Nat) (x : projectiveSpace n) : Ideal (ProjectiveCoordinateRing n) :=
  Ideal.comap
    (Ideal.Quotient.mk (sourceProjectivePrimeIdeal n x))
    (separatorSuccessorPrime n x)

/-- The raw lifted separator ideal is prime. -/
noncomputable instance liftedSeparatorPrime_isPrime
    (n : Nat) (x : projectiveSpace n) :
    (liftedSeparatorPrime n x).IsPrime := by
  unfold liftedSeparatorPrime
  exact Ideal.IsPrime.comap _

/-- The source projective prime lies below the raw lifted successor. -/
theorem sourcePrime_le_liftedSeparatorPrime
    (n : Nat) (x : projectiveSpace n) :
    sourceProjectivePrimeIdeal n x ≤ liftedSeparatorPrime n x := by
  intro f hf
  change Ideal.Quotient.mk (sourceProjectivePrimeIdeal n x) f ∈
    separatorSuccessorPrime n x
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hf]
  exact (separatorSuccessorPrime n x).zero_mem

/-- The selected positive homogeneous separator lies in the raw lifted prime. -/
theorem separator_mem_liftedSeparatorPrime
    (n : Nat) (x : projectiveSpace n) :
    (positiveHomogeneousSeparator n x).equation ∈ liftedSeparatorPrime n x := by
  change separatorClass n x ∈ separatorSuccessorPrime n x
  apply separatorPrincipalIdeal_le_successorPrime n x
  exact Ideal.subset_span (Set.mem_singleton (separatorClass n x))

/-- Homogeneous core of the raw lifted prime.  This is the canonical largest
homogeneous ideal contained in that prime. -/
noncomputable def homogeneousLiftedSeparatorPrime
    (n : Nat) (x : projectiveSpace n) :
    HomogeneousIdeal (ProjectiveGrading n) :=
  (liftedSeparatorPrime n x).homogeneousCore (ProjectiveGrading n)

/-- The homogeneous lift is still prime: homogeneous core preserves primality. -/
noncomputable instance homogeneousLiftedSeparatorPrime_isPrime
    (n : Nat) (x : projectiveSpace n) :
    (homogeneousLiftedSeparatorPrime n x).toIdeal.IsPrime := by
  exact Ideal.IsPrime.homogeneousCore
    (𝒜 := ProjectiveGrading n)
    (show (liftedSeparatorPrime n x).IsPrime from inferInstance)

/-- The source homogeneous prime remains below the homogeneous successor. -/
theorem sourcePrime_le_homogeneousLiftedSeparatorPrime
    (n : Nat) (x : projectiveSpace n) :
    x.asHomogeneousIdeal ≤ homogeneousLiftedSeparatorPrime n x := by
  have hmono := Ideal.homogeneousCore_mono (ProjectiveGrading n)
    (sourcePrime_le_liftedSeparatorPrime n x)
  simpa [sourceProjectivePrimeIdeal, homogeneousLiftedSeparatorPrime] using hmono

/-- The separator remains present after homogenization because it is itself
homogeneous. -/
theorem separator_mem_homogeneousLiftedSeparatorPrime
    (n : Nat) (x : projectiveSpace n) :
    (positiveHomogeneousSeparator n x).equation ∈
      homogeneousLiftedSeparatorPrime n x := by
  apply Ideal.mem_homogeneousCore_of_homogeneous_of_mem
    (𝒜 := ProjectiveGrading n)
  · exact ⟨(positiveHomogeneousSeparator n x).degree,
      (positiveHomogeneousSeparator n x).homogeneous⟩
  · exact separator_mem_liftedSeparatorPrime n x

/-- The source prime is strictly smaller than the homogeneous lifted successor.
The positive separator witnesses strictness. -/
theorem sourcePrime_lt_homogeneousLiftedSeparatorPrime
    (n : Nat) (x : projectiveSpace n) :
    x.asHomogeneousIdeal < homogeneousLiftedSeparatorPrime n x := by
  refine lt_of_le_of_ne
    (sourcePrime_le_homogeneousLiftedSeparatorPrime n x) ?_
  intro heq
  have hmem := separator_mem_homogeneousLiftedSeparatorPrime n x
  have hnot := positiveHomogeneousSeparator_not_mem n x
  exact hnot (by simpa [heq] using hmem)

/-- The homogeneous lifted successor remains below the raw lifted prime. -/
theorem homogeneousLiftedSeparatorPrime_le_raw
    (n : Nat) (x : projectiveSpace n) :
    (homogeneousLiftedSeparatorPrime n x).toIdeal ≤ liftedSeparatorPrime n x :=
  Ideal.toIdeal_homogeneousCore_le (ProjectiveGrading n)
    (liftedSeparatorPrime n x)

/-- Exact projective relevance condition for the homogeneous successor. -/
def HomogeneousSuccessorRelevant
    (n : Nat) (x : projectiveSpace n) : Prop :=
  ¬ HomogeneousIdeal.irrelevant (ProjectiveGrading n) ≤
    homogeneousLiftedSeparatorPrime n x

/-- Under the sole relevance condition, the homogeneous lifted prime is a
genuine projective-spectrum point. -/
noncomputable def projectiveSeparatorSuccessor
    (n : Nat) (x : projectiveSpace n)
    (hrel : HomogeneousSuccessorRelevant n x) :
    projectiveSpace n where
  asHomogeneousIdeal := homogeneousLiftedSeparatorPrime n x
  isPrime := inferInstance
  not_irrelevant_le := hrel

/-- The projective successor has exactly the constructed homogeneous prime. -/
@[simp]
theorem projectiveSeparatorSuccessor_asHomogeneousIdeal
    (n : Nat) (x : projectiveSpace n)
    (hrel : HomogeneousSuccessorRelevant n x) :
    (projectiveSeparatorSuccessor n x hrel).asHomogeneousIdeal =
      homogeneousLiftedSeparatorPrime n x := rfl

/-- The source prime is strictly contained in the genuine projective successor
prime whenever relevance holds. -/
theorem sourcePrime_lt_projectiveSeparatorSuccessorPrime
    (n : Nat) (x : projectiveSpace n)
    (hrel : HomogeneousSuccessorRelevant n x) :
    x.asHomogeneousIdeal <
      (projectiveSeparatorSuccessor n x hrel).asHomogeneousIdeal :=
  sourcePrime_lt_homogeneousLiftedSeparatorPrime n x

/-- The separator vanishes at the genuine projective successor. -/
theorem separator_mem_projectiveSeparatorSuccessorPrime
    (n : Nat) (x : projectiveSpace n)
    (hrel : HomogeneousSuccessorRelevant n x) :
    (positiveHomogeneousSeparator n x).equation ∈
      (projectiveSeparatorSuccessor n x hrel).asHomogeneousIdeal :=
  separator_mem_homogeneousLiftedSeparatorPrime n x

/-- Therefore the genuine projective successor lies in the intended principal
zero locus. -/
theorem projectiveSeparatorSuccessor_mem_principalSet
    (n : Nat) (x : projectiveSpace n)
    (hrel : HomogeneousSuccessorRelevant n x) :
    projectiveSeparatorSuccessor n x hrel ∈
      projectivePrincipalSet n
        (positiveHomogeneousSeparator n x).equation := by
  change ({(positiveHomogeneousSeparator n x).equation} :
      Set (ProjectiveCoordinateRing n)) ⊆
    (projectiveSeparatorSuccessor n x hrel).asHomogeneousIdeal
  simpa using separator_mem_projectiveSeparatorSuccessorPrime n x hrel

/-- **HOMOGENEOUS SUCCESSOR CROWN.**
Every source has a strict prime homogeneous successor carrying the separator;
relevance is exactly the remaining condition needed to promote that successor
to an actual projective point in the principal section. -/
theorem homogeneous_projective_successor_crown
    (n : Nat) (x : projectiveSpace n) :
    x.asHomogeneousIdeal < homogeneousLiftedSeparatorPrime n x
    ∧ (positiveHomogeneousSeparator n x).equation ∈
        homogeneousLiftedSeparatorPrime n x
    ∧ (HomogeneousSuccessorRelevant n x →
        ∃ y : projectiveSpace n,
          x.asHomogeneousIdeal < y.asHomogeneousIdeal
          ∧ (positiveHomogeneousSeparator n x).equation ∈ y.asHomogeneousIdeal) := by
  refine ⟨sourcePrime_lt_homogeneousLiftedSeparatorPrime n x,
    separator_mem_homogeneousLiftedSeparatorPrime n x, ?_⟩
  intro hrel
  exact ⟨projectiveSeparatorSuccessor n x hrel,
    sourcePrime_lt_projectiveSeparatorSuccessorPrime n x hrel,
    separator_mem_projectiveSeparatorSuccessorPrime n x hrel⟩

#check liftedSeparatorPrime
#check sourcePrime_le_liftedSeparatorPrime
#check separator_mem_liftedSeparatorPrime
#check homogeneousLiftedSeparatorPrime
#check sourcePrime_le_homogeneousLiftedSeparatorPrime
#check separator_mem_homogeneousLiftedSeparatorPrime
#check sourcePrime_lt_homogeneousLiftedSeparatorPrime
#check HomogeneousSuccessorRelevant
#check projectiveSeparatorSuccessor
#check projectiveSeparatorSuccessor_mem_principalSet
#check homogeneous_projective_successor_crown

#print axioms sourcePrime_le_liftedSeparatorPrime
#print axioms separator_mem_liftedSeparatorPrime
#print axioms sourcePrime_lt_homogeneousLiftedSeparatorPrime
#print axioms projectiveSeparatorSuccessor_mem_principalSet
#print axioms homogeneous_projective_successor_crown

end GSTClassicalHodgeProjectiveSuccessorRelevance
