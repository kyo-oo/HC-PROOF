import GSTClassicalHodgeAtomicAnnihilator
import GSTClassicalHodgeDefectModuloAtomicReciprocity
import GSTClassicalHodgeGradedFiniteClosedCorrespondence

/-!
# GST CLASSICAL HODGE — DEFECT RECIPROCITY BY ATOMIC ANNIHILATORS

The preferred complementary return law only asks that the round-trip error be
algebraic, i.e. lie in the complete atomic cycle-class span.  This file dualizes
that remaining membership statement.

A class lies in the atomic span exactly when every rational linear detector
which annihilates all genuine point-cycle classes also annihilates that class.
Therefore a complementary return may be verified purely by detector identities:

  ell (R (L^n alpha) - lambda alpha) = 0

for every atomic annihilator ell.

This is the natural interface for the repo's Poincare, separator, pairing and
tomography machinery.  It avoids constructing an algebraic error term by hand.

The final section specializes the return operator to an actual graded finite
closed correspondence from the previous module, leaving no abstract native
cycle operator in the return carrier.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeDefectAnnihilatorReciprocity

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeAtomicDefectDuality
open GSTClassicalHodgeAtomicAnnihilator
open GSTClassicalHodgeCrossWeightNativePropagation
open GSTClassicalHodgeComplementaryDefectReciprocity
open GSTClassicalHodgeDefectModuloAtomicReciprocity
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeFiniteClosedCorrespondence
open GSTClassicalHodgeGradedFiniteClosedCorrespondence

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p q n : Nat}

/-- **POINTWISE ATOMIC SEPARATION CRITERION.**
A rational cohomology class lies in the span of genuine codimension-p point
cycle classes iff every rational detector vanishing on those point classes
vanishes on the class. -/
theorem mem_atomicSpan_iff_all_annihilators_zero
    (x : RationalSingularCohomology H.analytification (2 * p)) :
    x ∈ pointCycleClassSpan p (H.cycleClass p) ↔
      ∀ ell :
          RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ] ℚ,
        AnnihilatesPointCycleClasses p (H.cycleClass p) ell →
          ell x = 0 := by
  constructor
  · intro hx ell hell
    have hker :
        pointCycleClassSpan p (H.cycleClass p) ≤ LinearMap.ker ell :=
      (annihilatesPointCycles_iff_atomicSpan_le_ker
        p (H.cycleClass p) ell).mp hell
    exact hker hx
  · intro hall
    by_contra hx
    obtain ⟨ell, hellSpan, hellx⟩ :=
      exists_linearFunctional_separating_submodule
        (pointCycleClassSpan p (H.cycleClass p)) x hx
    have hellAtoms :
        AnnihilatesPointCycleClasses p (H.cycleClass p) ell := by
      intro a
      apply hellSpan
      exact Submodule.subset_span ⟨a, rfl⟩
    exact hellx (hall ell hellAtoms)

/-- Detector form of a nonzero-scaled Hodge return law. -/
structure HodgeDefectReturnByAnnihilators
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p q : Nat) where
  forward : GradedCycleClassOperatorPair V H p q
  backward : GradedCycleClassOperatorPair V H q p
  forward_hodge :
    ∀ alpha : GSTClassicalHodgeCrossWeightAtomicDefectDescent.CohAt H p,
      alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p) →
        forward.cohomologyOperator alpha ∈
          rationalHodgeSubspace (H.hodgeBigrading q)
  scalar : ℚ
  scalar_ne_zero : scalar ≠ 0
  annihilator_roundtrip :
    ∀ alpha : GSTClassicalHodgeCrossWeightAtomicDefectDescent.CohAt H p,
      alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p) →
      ∀ ell :
          RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ] ℚ,
        AnnihilatesPointCycleClasses p (H.cycleClass p) ell →
          ell
            (backward.cohomologyOperator
                (forward.cohomologyOperator alpha) -
              scalar • alpha) = 0

namespace HodgeDefectReturnByAnnihilators

/-- Atomic annihilator identities are exactly enough to manufacture the
preferred modulo-atomic return package. -/
noncomputable def toModuloAtomic
    (R : HodgeDefectReturnByAnnihilators V H p q) :
    HodgeDefectReturnModuloAtomic V H p q where
  forward := R.forward
  backward := R.backward
  forward_hodge := R.forward_hodge
  scalar := R.scalar
  scalar_ne_zero := R.scalar_ne_zero
  roundtrip_mod_atomic := by
    intro alpha halpha
    apply (mem_atomicSpan_iff_all_annihilators_zero
      (V := V) (H := H) (p := p) _).2
    intro ell hell
    exact R.annihilator_roundtrip alpha halpha ell hell

/-- Hence target Hodge-defect vanishing propagates backwards using only the
detector identities. -/
theorem source_hodge_of_target_hodge
    (R : HodgeDefectReturnByAnnihilators V H p q)
    (htarget : atomicDefectLinearMap V H q = 0) :
    atomicDefectLinearMap V H p = 0 :=
  R.toModuloAtomic.source_hodge_of_target_hodge htarget

end HodgeDefectReturnByAnnihilators

/-- A complementary principal-cut return carried by one actual finite closed
correspondence.  Naturality is required only on genuine target point cycles;
the graded-correspondence module upgrades it to the full native operator. -/
structure PrincipalCutCorrespondenceAnnihilatorReturn
    (G : GeometricCycleClassSpine V H)
    (K : FiniteClosedCorrespondence V)
    (p n : Nat) where
  naturality :
    GradedCorrespondencePointNaturality K H (p + n) p
  scalar : ℚ
  scalar_ne_zero : scalar ≠ 0
  annihilator_roundtrip :
    ∀ alpha : GSTClassicalHodgeCrossWeightAtomicDefectDescent.CohAt H p,
      alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p) →
      ∀ ell :
          RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ] ℚ,
        AnnihilatesPointCycleClasses p (H.cycleClass p) ell →
          ell
            (naturality.cohomologyOperator
                ((principalCutPairIterate G p n).cohomologyOperator alpha) -
              scalar • alpha) = 0

namespace PrincipalCutCorrespondenceAnnihilatorReturn

/-- Build the preferred complementary return package directly from the
geometry-built graded correspondence operator. -/
noncomputable def toPrincipalCutPowerReturnModuloAtomic
    {K : FiniteClosedCorrespondence V}
    (R : PrincipalCutCorrespondenceAnnihilatorReturn G K p n) :
    PrincipalCutPowerReturnModuloAtomic G p n where
  returnPair := R.naturality.toGradedCycleClassOperatorPair
  scalar := R.scalar
  scalar_ne_zero := R.scalar_ne_zero
  roundtrip_mod_atomic := by
    intro alpha halpha
    apply (mem_atomicSpan_iff_all_annihilators_zero
      (V := V) (H := H) (p := p) _).2
    intro ell hell
    exact R.annihilator_roundtrip alpha halpha ell hell

/-- A genuine correspondence whose detector round-trip law is known therefore
propagates Hodge algebraicity from the complementary target back to the source. -/
theorem source_hodge_of_target_hodge
    {K : FiniteClosedCorrespondence V}
    (R : PrincipalCutCorrespondenceAnnihilatorReturn G K p n)
    (htarget : atomicDefectLinearMap V H (p + n) = 0) :
    atomicDefectLinearMap V H p = 0 :=
  R.toPrincipalCutPowerReturnModuloAtomic.source_hodge_of_target_hodge htarget

end PrincipalCutCorrespondenceAnnihilatorReturn

/-- Hard-Lefschetz-shaped correspondence/detector frontier. -/
abbrev ComplementaryCorrespondenceAnnihilatorReturn
    (G : GeometricCycleClassSpine V H)
    (K : FiniteClosedCorrespondence V)
    (d p : Nat) :=
  PrincipalCutCorrespondenceAnnihilatorReturn
    G K p (complementaryExponent d p)

#check mem_atomicSpan_iff_all_annihilators_zero
#check HodgeDefectReturnByAnnihilators
#check HodgeDefectReturnByAnnihilators.toModuloAtomic
#check HodgeDefectReturnByAnnihilators.source_hodge_of_target_hodge
#check PrincipalCutCorrespondenceAnnihilatorReturn
#check PrincipalCutCorrespondenceAnnihilatorReturn.toPrincipalCutPowerReturnModuloAtomic
#check PrincipalCutCorrespondenceAnnihilatorReturn.source_hodge_of_target_hodge
#check ComplementaryCorrespondenceAnnihilatorReturn

#print axioms mem_atomicSpan_iff_all_annihilators_zero
#print axioms HodgeDefectReturnByAnnihilators.toModuloAtomic
#print axioms HodgeDefectReturnByAnnihilators.source_hodge_of_target_hodge
#print axioms PrincipalCutCorrespondenceAnnihilatorReturn.toPrincipalCutPowerReturnModuloAtomic
#print axioms PrincipalCutCorrespondenceAnnihilatorReturn.source_hodge_of_target_hodge

end GSTClassicalHodgeDefectAnnihilatorReciprocity
