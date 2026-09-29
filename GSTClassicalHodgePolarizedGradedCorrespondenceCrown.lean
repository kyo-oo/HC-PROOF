import GSTClassicalHodgeGradedFiniteClosedCorrespondence
import GSTClassicalHodgeComplementaryDefectReciprocity
import GSTClassicalHodgePolarizedAdjointReciprocity

/-!
# GST CLASSICAL HODGE — POLARIZED GRADED CORRESPONDENCE CROWN

This file assembles the noncircular cross-weight route into one concrete
geometric package.

Forward transport is not abstract: it is the n-fold genuine principal-cut
operator from `GeometricCycleClassSpine`.

Backward transport is not abstract: it is the graded native operator of one
actual finite closed correspondence in X x X, with cycle-class naturality
verified on genuine point generators and promoted globally by compact point
normal form.

The remaining geometric identities are:

* the correspondence return preserves the target Hodge fiber;
* it is adjoint to the principal-cut power for chosen perfect Hodge pairings;
* the principal-cut power satisfies a nonzero-scaled pairing law.

Those identities imply reciprocity modulo algebraic classes by the previous
polarized defect theorem.  If the forward map is additionally surjective on
the target Hodge fiber (the hard-Lefschetz-shaped condition), Hodge-defect
vanishing is equivalent at the two weights.

Thus complementary Lefschetz transport is completely separated from the
primitive/middle obstruction: it can move a defect between complementary
weights but cannot, by itself, manufacture algebraicity of the residual
primitive sector.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgePolarizedGradedCorrespondenceCrown

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicDefectDuality
open GSTClassicalHodgeCrossWeightNativePropagation
open GSTClassicalHodgeCrossWeightAtomicDefectDescent
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeComplementaryDefectReciprocity
open GSTClassicalHodgeFiniteClosedCorrespondence
open GSTClassicalHodgeGradedFiniteClosedCorrespondence
open GSTClassicalHodgePolarizedHodgeGhost
open GSTClassicalHodgePolarizedDefectReciprocity
open GSTClassicalHodgePolarizedAdjointReciprocity

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p n : Nat}

/-- Concrete return data: the reverse operator is carried by one actual finite
closed correspondence and its pointwise Betti naturality law. -/
structure PrincipalCutGradedCorrespondenceReturn
    (G : GeometricCycleClassSpine V H)
    (K : FiniteClosedCorrespondence V)
    (p n : Nat) where
  naturality :
    GradedCorrespondencePointNaturality K H (p + n) p
  return_hodge :
    ∀ beta : CohAt H (p + n),
      beta ∈ rationalHodgeSubspace (H.hodgeBigrading (p + n)) →
        naturality.cohomologyOperator beta ∈
          rationalHodgeSubspace (H.hodgeBigrading p)
  scalar : ℚ
  scalar_ne_zero : scalar ≠ 0

namespace PrincipalCutGradedCorrespondenceReturn

/-- Forget only the concrete carrier and obtain the abstract Hodge-stable
forward/return datum used by polarized reciprocity. -/
noncomputable def toHodgeStableGradedReturnData
    {G : GeometricCycleClassSpine V H}
    {K : FiniteClosedCorrespondence V}
    (R : PrincipalCutGradedCorrespondenceReturn G K p n) :
    HodgeStableGradedReturnData V H p (p + n) where
  forward := principalCutPairIterate G p n
  backward := R.naturality.toGradedCycleClassOperatorPair
  forward_hodge := principalCutPairIterate_hodge G p n
  backward_hodge := R.return_hodge
  scalar := R.scalar
  scalar_ne_zero := R.scalar_ne_zero

/-- Projection-formula adjointness for the concrete correspondence return. -/
def PairingAdjointLaw
    {G : GeometricCycleClassSpine V H}
    {K : FiniteClosedCorrespondence V}
    (R : PrincipalCutGradedCorrespondenceReturn G K p n)
    (P : PerfectHodgeFiberPairing (V := V) (H := H) p)
    (Q : PerfectHodgeFiberPairing (V := V) (H := H) (p + n)) : Prop :=
  R.toHodgeStableGradedReturnData.PairingAdjointLaw P Q

/-- Polarized nonzero-scaled Lefschetz law for the genuine principal-cut power. -/
def ScaledLefschetzPairingLaw
    {G : GeometricCycleClassSpine V H}
    {K : FiniteClosedCorrespondence V}
    (R : PrincipalCutGradedCorrespondenceReturn G K p n)
    (P : PerfectHodgeFiberPairing (V := V) (H := H) p)
    (Q : PerfectHodgeFiberPairing (V := V) (H := H) (p + n)) : Prop :=
  R.toHodgeStableGradedReturnData.ScaledPairingLaw P Q

/-- Surjectivity of the principal-cut power on the genuine Hodge fibers. -/
def ForwardHodgeSurjective
    {G : GeometricCycleClassSpine V H}
    {K : FiniteClosedCorrespondence V}
    (R : PrincipalCutGradedCorrespondenceReturn G K p n) : Prop :=
  Function.Surjective R.toHodgeStableGradedReturnData.forwardOnHodge

/-- Adjointness plus the scaled pairing law propagate target Hodge algebraicity
backwards to the source weight. -/
theorem source_hodge_of_target_hodge
    {G : GeometricCycleClassSpine V H}
    {K : FiniteClosedCorrespondence V}
    (R : PrincipalCutGradedCorrespondenceReturn G K p n)
    (P : PerfectHodgeFiberPairing (V := V) (H := H) p)
    (Q : PerfectHodgeFiberPairing (V := V) (H := H) (p + n))
    (hadj : R.PairingAdjointLaw P Q)
    (hscale : R.ScaledLefschetzPairingLaw P Q)
    (htarget : atomicDefectLinearMap V H (p + n) = 0) :
    atomicDefectLinearMap V H p = 0 :=
  R.toHodgeStableGradedReturnData.source_hodge_of_adjoint_scaled_target_hodge
    P Q hadj hscale htarget

/-- Hard-Lefschetz surjectivity propagates source Hodge algebraicity forward to
the target weight using only the already-genuine cycle-class naturality of the
principal-cut power. -/
theorem target_hodge_of_source_hodge
    {G : GeometricCycleClassSpine V H}
    {K : FiniteClosedCorrespondence V}
    (R : PrincipalCutGradedCorrespondenceReturn G K p n)
    (hsurj : R.ForwardHodgeSurjective)
    (hsource : atomicDefectLinearMap V H p = 0) :
    atomicDefectLinearMap V H (p + n) = 0 := by
  apply LinearMap.ext
  intro beta
  rcases hsurj beta with ⟨alpha, halpha⟩
  have hsourceAlpha : atomicDefectLinearMap V H p alpha = 0 := by
    rw [hsource]
    rfl
  have heq :=
    (principalCutPairIterate G p n).defect_equivariant alpha
      (principalCutPairIterate_hodge G p n alpha.1 alpha.2)
  have himage :
      (principalCutPairIterate G p n).defectOperator
          (atomicDefectLinearMap V H p alpha) = 0 := by
    rw [hsourceAlpha]
    exact map_zero _
  rw [heq] at himage
  have hbeta :
      (⟨(principalCutPairIterate G p n).cohomologyOperator alpha.1,
          principalCutPairIterate_hodge G p n alpha.1 alpha.2⟩ :
        ClassicalHodgeFiber V H (p + n)) = beta := by
    exact halpha
  simpa [hbeta] using himage

/-- **COMPLEMENTARY TRANSPORT EQUIVALENCE.**
Under genuine correspondence adjointness, scaled pairing and Hodge-fiber
surjectivity, atomic Hodge-defect vanishing is equivalent at the two weights. -/
theorem hodge_defect_zero_iff
    {G : GeometricCycleClassSpine V H}
    {K : FiniteClosedCorrespondence V}
    (R : PrincipalCutGradedCorrespondenceReturn G K p n)
    (P : PerfectHodgeFiberPairing (V := V) (H := H) p)
    (Q : PerfectHodgeFiberPairing (V := V) (H := H) (p + n))
    (hadj : R.PairingAdjointLaw P Q)
    (hscale : R.ScaledLefschetzPairingLaw P Q)
    (hsurj : R.ForwardHodgeSurjective) :
    atomicDefectLinearMap V H p = 0 ↔
      atomicDefectLinearMap V H (p + n) = 0 := by
  constructor
  · exact R.target_hodge_of_source_hodge hsurj
  · exact R.source_hodge_of_target_hodge P Q hadj hscale

end PrincipalCutGradedCorrespondenceReturn

/-- Hard-Lefschetz-shaped concrete correspondence return. -/
abbrev ComplementaryGradedCorrespondenceReturn
    (G : GeometricCycleClassSpine V H)
    (K : FiniteClosedCorrespondence V)
    (d p : Nat) :=
  PrincipalCutGradedCorrespondenceReturn
    G K p (complementaryExponent d p)

#check PrincipalCutGradedCorrespondenceReturn
#check PrincipalCutGradedCorrespondenceReturn.toHodgeStableGradedReturnData
#check PrincipalCutGradedCorrespondenceReturn.PairingAdjointLaw
#check PrincipalCutGradedCorrespondenceReturn.ScaledLefschetzPairingLaw
#check PrincipalCutGradedCorrespondenceReturn.ForwardHodgeSurjective
#check PrincipalCutGradedCorrespondenceReturn.source_hodge_of_target_hodge
#check PrincipalCutGradedCorrespondenceReturn.target_hodge_of_source_hodge
#check PrincipalCutGradedCorrespondenceReturn.hodge_defect_zero_iff
#check ComplementaryGradedCorrespondenceReturn

#print axioms PrincipalCutGradedCorrespondenceReturn.source_hodge_of_target_hodge
#print axioms PrincipalCutGradedCorrespondenceReturn.target_hodge_of_source_hodge
#print axioms PrincipalCutGradedCorrespondenceReturn.hodge_defect_zero_iff

end GSTClassicalHodgePolarizedGradedCorrespondenceCrown
