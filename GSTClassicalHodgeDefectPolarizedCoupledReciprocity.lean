import GSTClassicalHodgeFirstFailureCokernelRigidity

/-!
# GST CLASSICAL HODGE — DEFECT-POLARIZED COUPLED RECIPROCITY

The ambient polarized-adjoint route still remembers algebraic correction terms
that are irrelevant to the genuine obstruction.  The natural GST object is the
atomic-defect quotient itself.

This file therefore moves the polarization/transpose mechanism directly onto

    DefectAt p = H^{2p}(X,Q) / AtomicSpanAt p.

At two adjacent weights, let

    Lbar : DefectAt p -> DefectAt (p+1)

be the already constructed genuine projective principal-cut transport, and let

    Rbar : DefectAt (p+1) -> DefectAt p

be the descended action of one genuine cycle-class-natural return operator.

The crucial orientation for a *first bad target weight* is not the ordinary
left-inverse identity Rbar Lbar = lambda I.  That only proves injectivity of
Lbar.  What kills the first bad class is the coisometric identity

    Lbar Rbar = lambda I

on the target defect quotient.

We derive exactly that identity from two quotient-level pairing laws:

* transpose adjointness

      <x, Lbar z>_target = <Rbar x, z>_source,

* scaled return pairing

      <Rbar x, Rbar y>_source = lambda <x,y>_target.

Right nondegeneracy of the target defect pairing then forces
`Lbar (Rbar y) = lambda • y` for every target defect `y`.

This is strictly weaker than an exact ambient cohomology round trip.  Any
algebraic correction has already disappeared in the quotient before the
pairing laws are stated.  No same-weight matrix unit, basis-cycle supply, or
cosmic algebraicity law is used.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeDefectPolarizedCoupledReciprocity

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeAtomicDefectDuality
open GSTClassicalHodgeCrossWeightNativePropagation
open GSTClassicalHodgeCrossWeightAtomicDefectDescent
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeFirstPrimitiveProjectiveFailure

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- A rational pairing on the genuine atomic-defect quotient that separates
its second input.  This is the exact nondegeneracy orientation needed for the
coisometric return argument below. -/
structure RightPerfectDefectPairing
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) where
  pair : DefectAt V H p →ₗ[ℚ] (DefectAt V H p →ₗ[ℚ] ℚ)
  right_nondegenerate :
    ∀ y : DefectAt V H p,
      (∀ x : DefectAt V H p, pair x y = 0) → y = 0

/-- One genuinely graded return together with a coupled polarization law on
the atomic-defect quotients.

The cohomological return is required to preserve the Hodge sector only because
that is what lets a first-bad Hodge defect descend to the already-good
predecessor Hodge fiber. -/
structure PrincipalCutDefectCoisometry
    (G : GeometricCycleClassSpine V H)
    (p : Nat) where
  returnPair : GradedCycleClassOperatorPair V H (p + 1) p
  sourcePairing : RightPerfectDefectPairing V H p
  targetPairing : RightPerfectDefectPairing V H (p + 1)
  scalar : ℚ
  scalar_ne_zero : scalar ≠ 0
  return_hodge :
    ∀ beta : GSTClassicalHodgeFiberedCosmology.ClassicalHodgeFiber V H (p + 1),
      returnPair.cohomologyOperator beta.1 ∈
        rationalHodgeSubspace (H.hodgeBigrading p)
  defect_adjoint :
    ∀ y : DefectAt V H (p + 1),
    ∀ z : DefectAt V H p,
      targetPairing.pair y (principalCutDefectOperator G p z) =
        sourcePairing.pair (returnPair.defectOperator y) z
  return_scaled_pairing :
    ∀ x y : DefectAt V H (p + 1),
      sourcePairing.pair
          (returnPair.defectOperator x)
          (returnPair.defectOperator y) =
        scalar * targetPairing.pair x y

namespace PrincipalCutDefectCoisometry

/-- **QUOTIENT COISOMETRIC ROUND TRIP.**
Transpose adjointness plus scaled return pairing force the desired orientation
`Lbar Rbar = lambda I` directly on the atomic-defect quotient. -/
theorem target_defect_roundtrip
    {G : GeometricCycleClassSpine V H}
    (R : PrincipalCutDefectCoisometry G p)
    (y : DefectAt V H (p + 1)) :
    principalCutDefectOperator G p (R.returnPair.defectOperator y) =
      R.scalar • y := by
  apply sub_eq_zero.mp
  apply R.targetPairing.right_nondegenerate
  intro x
  calc
    R.targetPairing.pair x
        (principalCutDefectOperator G p (R.returnPair.defectOperator y) -
          R.scalar • y)
        = R.targetPairing.pair x
            (principalCutDefectOperator G p (R.returnPair.defectOperator y)) -
          R.scalar * R.targetPairing.pair x y := by
            simp
    _ = R.sourcePairing.pair
          (R.returnPair.defectOperator x)
          (R.returnPair.defectOperator y) -
        R.scalar * R.targetPairing.pair x y := by
          rw [R.defect_adjoint x (R.returnPair.defectOperator y)]
    _ = 0 := by
          rw [R.return_scaled_pairing x y]
          ring

/-- The target principal-cut defect map is surjective.  This is stronger than
the injectivity obtained from the opposite round-trip orientation and is the
property relevant to first-failure extinction. -/
theorem principalCutDefectOperator_surjective
    {G : GeometricCycleClassSpine V H}
    (R : PrincipalCutDefectCoisometry G p) :
    Function.Surjective (principalCutDefectOperator G p) := by
  intro y
  refine ⟨R.scalar⁻¹ • R.returnPair.defectOperator y, ?_⟩
  rw [map_smul, R.target_defect_roundtrip y, smul_smul]
  simp [R.scalar_ne_zero]

/-- A target Hodge class descends through the genuine return pair to a genuine
source Hodge class. -/
noncomputable def returnedHodgeClass
    {G : GeometricCycleClassSpine V H}
    (R : PrincipalCutDefectCoisometry G p)
    (beta : GSTClassicalHodgeFiberedCosmology.ClassicalHodgeFiber V H (p + 1)) :
    GSTClassicalHodgeFiberedCosmology.ClassicalHodgeFiber V H p :=
  ⟨R.returnPair.cohomologyOperator beta.1, R.return_hodge beta⟩

/-- Exact identification of the returned Hodge defect with the descended
return action on the target defect. -/
theorem returnedHodgeClass_defect
    {G : GeometricCycleClassSpine V H}
    (R : PrincipalCutDefectCoisometry G p)
    (beta : GSTClassicalHodgeFiberedCosmology.ClassicalHodgeFiber V H (p + 1)) :
    atomicDefectLinearMap V H p (R.returnedHodgeClass beta) =
      R.returnPair.defectOperator
        (atomicDefectLinearMap V H (p + 1) beta) := by
  exact R.returnPair.defect_equivariant beta (R.return_hodge beta)

/-- **LOCAL FIRST-FAILURE EXTINCTION.**
If the predecessor Hodge defect is zero, the coisometric quotient return forces
every target Hodge defect to vanish. -/
theorem target_hodge_defect_zero_of_predecessor_zero
    {G : GeometricCycleClassSpine V H}
    (R : PrincipalCutDefectCoisometry G p)
    (hsource : atomicDefectLinearMap V H p = 0) :
    atomicDefectLinearMap V H (p + 1) = 0 := by
  apply LinearMap.ext
  intro beta
  let z := atomicDefectLinearMap V H (p + 1) beta
  have hdown : R.returnPair.defectOperator z = 0 := by
    rw [← R.returnedHodgeClass_defect beta]
    rw [hsource]
    rfl
  have hround := R.target_defect_roundtrip z
  rw [hdown, map_zero] at hround
  have hscaled : R.scalar • z = 0 := hround.symm
  have hz : z = 0 := by
    simpa [R.scalar_ne_zero] using hscaled
  exact hz

/-- A coisometric defect packet at the globally least bad successor weight is
impossible. -/
theorem firstFailure_forbids_defect_coisometry
    {G : GeometricCycleClassSpine V H}
    (F : FirstAtomicDefectWeight V H)
    (hp : F.weight = p + 1)
    (R : PrincipalCutDefectCoisometry G p) : False := by
  have hsource : atomicDefectLinearMap V H p = 0 :=
    firstAtomicDefect_predecessor_zero F hp
  have htarget : atomicDefectLinearMap V H (p + 1) = 0 :=
    R.target_hodge_defect_zero_of_predecessor_zero hsource
  apply F.defect_ne_zero
  simpa [hp] using htarget

end PrincipalCutDefectCoisometry

/-- **DEFECT-POLARIZED COUPLED HODGE CROWN.**
If weight zero is algebraic and every adjacent projective principal cut admits
a genuine Hodge-preserving coisometric return on the atomic-defect quotient,
then no least bad weight can exist and the full Stage-2G Hodge statement
follows. -/
theorem bigradedBettiHodge_of_defectCoisometryFamily
    (G : GeometricCycleClassSpine V H)
    (hzero : atomicDefectLinearMap V H 0 = 0)
    (R : ∀ p : Nat, PrincipalCutDefectCoisometry G p) :
    BigradedBettiHodgeStatement V H := by
  by_contra hnot
  let F := firstAtomicDefectWeightOfFailure
    (V := V) (H := H) hzero hnot
  obtain ⟨p, hp⟩ := firstAtomicDefectWeight_eq_succ F
  exact (R p).firstFailure_forbids_defect_coisometry F hp

/-- Crown: quotient pairing nondegeneracy, transpose adjointness, and scaled
return geometry imply target coisometry and hence global Hodge landing by
least-counterexample extinction. -/
theorem defect_polarized_coupled_reciprocity_crown
    (G : GeometricCycleClassSpine V H)
    (hzero : atomicDefectLinearMap V H 0 = 0)
    (R : ∀ p : Nat, PrincipalCutDefectCoisometry G p) :
    (∀ p : Nat, ∀ y : DefectAt V H (p + 1),
      principalCutDefectOperator G p
          ((R p).returnPair.defectOperator y) =
        (R p).scalar • y)
    ∧ BigradedBettiHodgeStatement V H := by
  exact ⟨
    fun p y => (R p).target_defect_roundtrip y,
    bigradedBettiHodge_of_defectCoisometryFamily G hzero R⟩

#check RightPerfectDefectPairing
#check PrincipalCutDefectCoisometry
#check PrincipalCutDefectCoisometry.target_defect_roundtrip
#check PrincipalCutDefectCoisometry.principalCutDefectOperator_surjective
#check PrincipalCutDefectCoisometry.target_hodge_defect_zero_of_predecessor_zero
#check PrincipalCutDefectCoisometry.firstFailure_forbids_defect_coisometry
#check bigradedBettiHodge_of_defectCoisometryFamily
#check defect_polarized_coupled_reciprocity_crown

#print axioms PrincipalCutDefectCoisometry.target_defect_roundtrip
#print axioms PrincipalCutDefectCoisometry.target_hodge_defect_zero_of_predecessor_zero
#print axioms PrincipalCutDefectCoisometry.firstFailure_forbids_defect_coisometry
#print axioms bigradedBettiHodge_of_defectCoisometryFamily
#print axioms defect_polarized_coupled_reciprocity_crown

end GSTClassicalHodgeDefectPolarizedCoupledReciprocity
