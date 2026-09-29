import GSTClassicalHodgeCrossWeightDefectRetraction

/-!
# GST CLASSICAL HODGE — COMPLEMENTARY DEFECT RECIPROCITY

A return map for every one-step principal cut is stronger than the actual
Lefschetz geometry requires.  The natural projective statement is instead a
return for the complementary Lefschetz power.

This file therefore builds the genuine n-fold principal-cut operator pair
itself and proves that its descended defect action is exactly the previously
constructed principal-cut defect iterate.  A single nonzero-scaled return for
that n-fold operator then makes the whole n-step defect transport injective.

For a projective dimension parameter d and a weight p with 2p <= d, the
complementary exponent is d - 2p and the target weight is

  p + (d - 2p) = d - p.

Thus the classical hard-Lefschetz-shaped frontier is represented without
postulating injectivity of each one-step cut.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeComplementaryDefectReciprocity

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeCrossWeightNativePropagation
open GSTClassicalHodgeCrossWeightAtomicDefectDescent
open GSTClassicalHodgeCrossWeightDefectRetraction
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeAtomicDefectDuality

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Identity graded cycle-class pair. -/
noncomputable def gradedIdentityPair
    (p : Nat) : GradedCycleClassOperatorPair V H p p where
  cycleOperator := LinearMap.id
  cohomologyOperator := LinearMap.id
  cycleClass_natural := by
    intro Z
    rfl

/-- The genuine n-fold principal-cut cycle/cohomology pair. -/
noncomputable def principalCutPairIterate
    (G : GeometricCycleClassSpine V H) :
    (p n : Nat) → GradedCycleClassOperatorPair V H p (p + n)
  | p, 0 => gradedIdentityPair p
  | p, n + 1 =>
      (G.principalCutPair (p + n)).comp
        (principalCutPairIterate G p n)

@[simp]
theorem principalCutPairIterate_zero
    (G : GeometricCycleClassSpine V H)
    (p : Nat) :
    principalCutPairIterate G p 0 = gradedIdentityPair p := by
  rfl

@[simp]
theorem principalCutPairIterate_succ
    (G : GeometricCycleClassSpine V H)
    (p n : Nat) :
    principalCutPairIterate G p (n + 1) =
      (G.principalCutPair (p + n)).comp
        (principalCutPairIterate G p n) := by
  rfl

/-- The defect action of the genuine n-fold pair is exactly the finite defect
ladder already constructed from one-step descents. -/
theorem principalCutPairIterate_defectOperator
    (G : GeometricCycleClassSpine V H)
    (p n : Nat) :
    (principalCutPairIterate G p n).defectOperator =
      principalCutDefectIterate G p n := by
  induction n with
  | zero =>
      apply LinearMap.ext
      intro z
      refine Submodule.Quotient.induction_on z ?_
      intro alpha
      rfl
  | succ n ih =>
      rw [principalCutPairIterate_succ,
        GradedCycleClassOperatorPair.defectOperator_comp,
        principalCutDefectIterate_succ,
        ih]
      rfl

/-- Iterated principal cuts preserve the genuine Hodge sector. -/
theorem principalCutPairIterate_hodge
    (G : GeometricCycleClassSpine V H)
    (p n : Nat)
    (alpha : CohAt H p)
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p)) :
    (principalCutPairIterate G p n).cohomologyOperator alpha ∈
      rationalHodgeSubspace (H.hodgeBigrading (p + n)) := by
  induction n generalizing alpha with
  | zero =>
      simpa [principalCutPairIterate, gradedIdentityPair] using halpha
  | succ n ih =>
      rw [principalCutPairIterate_succ]
      change
        (G.principalCutPair (p + n)).cohomologyOperator
            ((principalCutPairIterate G p n).cohomologyOperator alpha) ∈
          rationalHodgeSubspace (H.hodgeBigrading (p + (n + 1)))
      have hmid := ih alpha halpha
      have hnext := G.principalCut_hodge (p + n)
        ((principalCutPairIterate G p n).cohomologyOperator alpha) hmid
      simpa [Nat.add_assoc] using hnext

/-- One nonzero-scaled return for an entire principal-cut power. -/
structure PrincipalCutPowerReturnLaw
    (G : GeometricCycleClassSpine V H)
    (p n : Nat) where
  returnPair : GradedCycleClassOperatorPair V H (p + n) p
  scalar : ℚ
  scalar_ne_zero : scalar ≠ 0
  cohomology_roundtrip :
    ∀ alpha : CohAt H p,
      returnPair.cohomologyOperator
          ((principalCutPairIterate G p n).cohomologyOperator alpha) =
        scalar • alpha

namespace PrincipalCutPowerReturnLaw

/-- Package the power return law into the generic defect-retraction theorem. -/
noncomputable def toGradedDefectRetraction
    (R : PrincipalCutPowerReturnLaw G p n) :
    GradedDefectRetraction V H p (p + n) where
  forward := principalCutPairIterate G p n
  backward := R.returnPair
  scalar := R.scalar
  scalar_ne_zero := R.scalar_ne_zero
  cohomology_roundtrip := R.cohomology_roundtrip

/-- The full n-step principal-cut defect transport is injective whenever its
whole complementary power has one nonzero-scaled genuine return. -/
theorem principalCutDefectIterate_injective
    (R : PrincipalCutPowerReturnLaw G p n) :
    Function.Injective (principalCutDefectIterate G p n) := by
  rw [← principalCutPairIterate_defectOperator G p n]
  exact R.toGradedDefectRetraction.forward_defect_injective

/-- If the n-step image defect is zero then the original defect is zero. -/
theorem defect_eq_zero_of_power_image_zero
    (R : PrincipalCutPowerReturnLaw G p n)
    (z : DefectAt V H p)
    (hz : principalCutDefectIterate G p n z = 0) :
    z = 0 := by
  apply R.principalCutDefectIterate_injective
  simpa using hz

/-- Hodge algebraicity at the target weight propagates backwards to the source
Hodge class through a genuine complementary-power return. -/
theorem source_atomicDefect_zero_of_target_hodge
    (R : PrincipalCutPowerReturnLaw G p n)
    (alpha : GSTClassicalHodgeFiberedCosmology.ClassicalHodgeFiber V H p)
    (htarget : atomicDefectLinearMap V H (p + n) = 0) :
    atomicDefectLinearMap V H p alpha = 0 := by
  let beta : GSTClassicalHodgeFiberedCosmology.ClassicalHodgeFiber V H (p + n) :=
    ⟨(principalCutPairIterate G p n).cohomologyOperator alpha.1,
      principalCutPairIterate_hodge G p n alpha.1 alpha.2⟩
  have hbeta : atomicDefectLinearMap V H (p + n) beta = 0 := by
    rw [htarget]
    rfl
  have himage :
      principalCutDefectIterate G p n
          (atomicDefectLinearMap V H p alpha) = 0 := by
    rw [← principalCutPairIterate_defectOperator G p n]
    rw [← (principalCutPairIterate G p n).defect_equivariant alpha
      (principalCutPairIterate_hodge G p n alpha.1 alpha.2)]
    exact hbeta
  exact R.defect_eq_zero_of_power_image_zero
    (atomicDefectLinearMap V H p alpha) himage

/-- Consequently, vanishing of the Hodge defect map in the complementary
target weight forces vanishing in the source weight. -/
theorem source_hodge_of_target_hodge
    (R : PrincipalCutPowerReturnLaw G p n)
    (htarget : atomicDefectLinearMap V H (p + n) = 0) :
    atomicDefectLinearMap V H p = 0 := by
  apply LinearMap.ext
  intro alpha
  exact R.source_atomicDefect_zero_of_target_hodge alpha htarget

end PrincipalCutPowerReturnLaw

/-- Hard-Lefschetz-shaped complementary exponent. -/
def complementaryExponent (d p : Nat) : Nat := d - 2 * p

/-- A return law only for the complementary principal-cut power. -/
abbrev ComplementaryPrincipalCutReturnLaw
    (G : GeometricCycleClassSpine V H)
    (d p : Nat) :=
  PrincipalCutPowerReturnLaw G p (complementaryExponent d p)

/-- In the valid lower-half range the complementary target weight is d-p. -/
theorem complementary_target_weight
    (d p : Nat) (hp : 2 * p ≤ d) :
    p + complementaryExponent d p = d - p := by
  unfold complementaryExponent
  omega

#check gradedIdentityPair
#check principalCutPairIterate
#check principalCutPairIterate_defectOperator
#check principalCutPairIterate_hodge
#check PrincipalCutPowerReturnLaw
#check PrincipalCutPowerReturnLaw.principalCutDefectIterate_injective
#check PrincipalCutPowerReturnLaw.source_hodge_of_target_hodge
#check complementaryExponent
#check ComplementaryPrincipalCutReturnLaw
#check complementary_target_weight

#print axioms principalCutPairIterate_defectOperator
#print axioms principalCutPairIterate_hodge
#print axioms PrincipalCutPowerReturnLaw.principalCutDefectIterate_injective
#print axioms PrincipalCutPowerReturnLaw.source_hodge_of_target_hodge
#print axioms complementary_target_weight

end GSTClassicalHodgeComplementaryDefectReciprocity
