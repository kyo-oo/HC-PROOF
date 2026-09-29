import GSTClassicalHodgeDefectHamelPolarization
import GSTClassicalHodgeFirstFailureCokernelRigidity

/-!
# GST CLASSICAL HODGE — FIRST-FAILURE SCALAR DETECTOR COLLISION

The quotient coisometry theorem still asks for an identity on every target
defect.  A least Hodge failure needs much less.

Let `beta` be one Hodge class at the first bad successor weight and let

    z = atomicDefect(beta) != 0.

The unconditional Hamel polarization of the atomic-defect quotient supplies a
single rational linear detector `ell_z` with `ell_z z != 0`.

Now take one genuine cycle-class-natural return from weight `p+1` to `p` that
sends `beta` back into the Hodge sector.  Since the predecessor weight is good,
its returned Hodge defect is zero.  Therefore the descended return sends `z`
to zero, and every genuine principal-cut image of that returned defect is zero.

Consequently the first failure is destroyed by only ONE scalar reciprocity
identity

    ell_z (Lbar (Rbar z)) = lambda * ell_z z,

with `lambda != 0`.

No full quotient round trip, no perfect pairing law, no all-state adjointness,
no matrix-unit externalization, and no basis-cycle realization is needed.  This
is the smallest scalar collision currently exposed by the cross-weight GST
cosmology.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeFirstFailureScalarDetectorCollision

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeAtomicDefectDuality
open GSTClassicalHodgeCrossWeightNativePropagation
open GSTClassicalHodgeCrossWeightAtomicDefectDescent
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeFirstPrimitiveProjectiveFailure
open GSTClassicalHodgeDefectHamelPolarization

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Every nonzero atomic defect has a rational linear detector that reads it
nontrivially.  This is pure Hamel-coordinate separation. -/
theorem exists_defectDetector_of_ne_zero
    (z : DefectAt V H p)
    (hz : z ≠ 0) :
    ∃ ell : DefectAt V H p →ₗ[ℚ] ℚ, ell z ≠ 0 := by
  have hex : ∃ x : DefectAt V H p,
      hamelDefectPair (V := V) (H := H) p x z ≠ 0 := by
    by_contra hnone
    push_neg at hnone
    exact hz
      (hamelDefectPair_right_nondegenerate
        (V := V) (H := H) p z hnone)
  rcases hex with ⟨x, hx⟩
  exact ⟨hamelDefectPair (V := V) (H := H) p x, hx⟩

/-- Chosen separating detector for one nonzero atomic defect. -/
noncomputable def chosenDefectDetector
    (z : DefectAt V H p)
    (hz : z ≠ 0) : DefectAt V H p →ₗ[ℚ] ℚ :=
  Classical.choose (exists_defectDetector_of_ne_zero z hz)

/-- The chosen detector really reads the selected defect nontrivially. -/
theorem chosenDefectDetector_ne_zero_on
    (z : DefectAt V H p)
    (hz : z ≠ 0) :
    chosenDefectDetector z hz z ≠ 0 :=
  Classical.choose_spec (exists_defectDetector_of_ne_zero z hz)

/-- One scalar reciprocity packet for one nonzero target Hodge defect.

The return is fully genuine: it is a graded native/cohomological operator pair,
so its defect action is already the canonical descended action.  The only new
identity is the one scalar read needed to collide with predecessor goodness. -/
structure FirstFailureScalarReturn
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (beta : GSTClassicalHodgeFiberedCosmology.ClassicalHodgeFiber V H (p + 1))
    (hbeta : atomicDefectLinearMap V H (p + 1) beta ≠ 0) where
  returnPair : GradedCycleClassOperatorPair V H (p + 1) p
  return_hodge :
    returnPair.cohomologyOperator beta.1 ∈
      rationalHodgeSubspace (H.hodgeBigrading p)
  scalar : ℚ
  scalar_ne_zero : scalar ≠ 0
  scalar_roundtrip :
    let z := atomicDefectLinearMap V H (p + 1) beta
    chosenDefectDetector z hbeta
        (principalCutDefectOperator G p
          (returnPair.defectOperator z)) =
      scalar * chosenDefectDetector z hbeta z

namespace FirstFailureScalarReturn

/-- The returned target class packaged as a genuine predecessor Hodge class. -/
noncomputable def returnedHodgeClass
    {G : GeometricCycleClassSpine V H}
    {beta : GSTClassicalHodgeFiberedCosmology.ClassicalHodgeFiber V H (p + 1)}
    {hbeta : atomicDefectLinearMap V H (p + 1) beta ≠ 0}
    (R : FirstFailureScalarReturn G p beta hbeta) :
    GSTClassicalHodgeFiberedCosmology.ClassicalHodgeFiber V H p :=
  ⟨R.returnPair.cohomologyOperator beta.1, R.return_hodge⟩

/-- Its atomic defect is exactly the returned quotient defect. -/
theorem returnedHodgeClass_defect
    {G : GeometricCycleClassSpine V H}
    {beta : GSTClassicalHodgeFiberedCosmology.ClassicalHodgeFiber V H (p + 1)}
    {hbeta : atomicDefectLinearMap V H (p + 1) beta ≠ 0}
    (R : FirstFailureScalarReturn G p beta hbeta) :
    atomicDefectLinearMap V H p R.returnedHodgeClass =
      R.returnPair.defectOperator
        (atomicDefectLinearMap V H (p + 1) beta) := by
  exact R.returnPair.defect_equivariant beta R.return_hodge

/-- **ONE-SCALAR FIRST-FAILURE COLLISION.**
If the predecessor Hodge defect vanishes, the scalar reciprocity packet is
impossible. -/
theorem impossible_of_predecessor_defect_zero
    {G : GeometricCycleClassSpine V H}
    {beta : GSTClassicalHodgeFiberedCosmology.ClassicalHodgeFiber V H (p + 1)}
    {hbeta : atomicDefectLinearMap V H (p + 1) beta ≠ 0}
    (R : FirstFailureScalarReturn G p beta hbeta)
    (hsource : atomicDefectLinearMap V H p = 0) : False := by
  let z := atomicDefectLinearMap V H (p + 1) beta
  have hreturn : R.returnPair.defectOperator z = 0 := by
    rw [← R.returnedHodgeClass_defect]
    rw [hsource]
    rfl
  have hread := R.scalar_roundtrip
  dsimp only at hread
  rw [hreturn, map_zero, map_zero] at hread
  have hright :
      R.scalar * chosenDefectDetector z hbeta z ≠ 0 :=
    mul_ne_zero R.scalar_ne_zero
      (chosenDefectDetector_ne_zero_on z hbeta)
  exact hright hread.symm

/-- At the globally least bad successor weight, even this one-scalar return
packet is forbidden. -/
theorem firstFailure_forbids_scalar_return
    {G : GeometricCycleClassSpine V H}
    (F : FirstAtomicDefectWeight V H)
    (hp : F.weight = p + 1)
    {beta : GSTClassicalHodgeFiberedCosmology.ClassicalHodgeFiber V H (p + 1)}
    {hbeta : atomicDefectLinearMap V H (p + 1) beta ≠ 0}
    (R : FirstFailureScalarReturn G p beta hbeta) : False := by
  exact R.impossible_of_predecessor_defect_zero
    (firstAtomicDefect_predecessor_zero F hp)

end FirstFailureScalarReturn

/-- Every nonzero linear map has a point on which it is nonzero, specialized
to the first-bad Hodge defect map. -/
theorem exists_firstBadHodgeClass
    (F : FirstAtomicDefectWeight V H) :
    ∃ beta : GSTClassicalHodgeFiberedCosmology.ClassicalHodgeFiber V H F.weight,
      atomicDefectLinearMap V H F.weight beta ≠ 0 := by
  by_contra hnone
  push_neg at hnone
  apply F.defect_ne_zero
  apply LinearMap.ext
  intro beta
  simpa using hnone beta

/-- **SCALAR-RECIPROCITY HODGE CROWN.**
Weight zero plus existence of one scalar return packet for every possible
nonzero target Hodge defect excludes the least counterexample and proves the
full Stage-2G Hodge statement. -/
theorem bigradedBettiHodge_of_scalarReturnFamily
    (G : GeometricCycleClassSpine V H)
    (hzero : atomicDefectLinearMap V H 0 = 0)
    (R : ∀ p : Nat,
      ∀ beta : GSTClassicalHodgeFiberedCosmology.ClassicalHodgeFiber V H (p + 1),
      ∀ hbeta : atomicDefectLinearMap V H (p + 1) beta ≠ 0,
        Nonempty (FirstFailureScalarReturn G p beta hbeta)) :
    BigradedBettiHodgeStatement V H := by
  by_contra hnot
  let F := firstAtomicDefectWeightOfFailure
    (V := V) (H := H) hzero hnot
  obtain ⟨p, hp⟩ := firstAtomicDefectWeight_eq_succ F
  obtain ⟨betaF, hbetaF⟩ := exists_firstBadHodgeClass F
  let beta : GSTClassicalHodgeFiberedCosmology.ClassicalHodgeFiber V H (p + 1) := by
    simpa [hp] using betaF
  have hbeta : atomicDefectLinearMap V H (p + 1) beta ≠ 0 := by
    simpa [beta, hp] using hbetaF
  rcases R p beta hbeta with ⟨RR⟩
  exact RR.firstFailure_forbids_scalar_return F hp

#check exists_defectDetector_of_ne_zero
#check chosenDefectDetector
#check chosenDefectDetector_ne_zero_on
#check FirstFailureScalarReturn
#check FirstFailureScalarReturn.impossible_of_predecessor_defect_zero
#check FirstFailureScalarReturn.firstFailure_forbids_scalar_return
#check exists_firstBadHodgeClass
#check bigradedBettiHodge_of_scalarReturnFamily

#print axioms exists_defectDetector_of_ne_zero
#print axioms chosenDefectDetector_ne_zero_on
#print axioms FirstFailureScalarReturn.impossible_of_predecessor_defect_zero
#print axioms FirstFailureScalarReturn.firstFailure_forbids_scalar_return
#print axioms bigradedBettiHodge_of_scalarReturnFamily

end GSTClassicalHodgeFirstFailureScalarDetectorCollision
