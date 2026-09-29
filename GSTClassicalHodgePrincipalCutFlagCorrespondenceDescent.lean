import GSTClassicalHodgePrincipalCutFlagNativeReturn
import GSTClassicalHodgeFiniteClosedCorrespondenceTranspose
import GSTClassicalHodgeGradedFiniteClosedCorrespondence

/-!
# GST CLASSICAL HODGE — PRINCIPAL-CUT FLAG CORRESPONDENCE DESCENT

The native principal-cut flag already has a literal finite incidence transpose,
but coefficient transposition alone is not automatically invariant under Betti
homology.  In particular, no coefficient dot-product is silently identified
with a cohomological intersection pairing in this module.

This file gives the geometric replacement.

Suppose one actual bi-finite closed correspondence in `X × X` realizes the
principal-cut incidence kernel on a finite source chart, and its genuine
algebraic transpose realizes the reverse incidence columns.  Then the reverse
principal-cut operator is literally the graded native operator of that
transpose.  Consequently ordinary point-generator Betti naturality of the
transposed correspondence promotes, by the existing compact point normal form,
to a complete cohomological descent of the hand-written reverse flag.

Thus `PrincipalCutFlagProjectionFormula` is not needed on this route.  The
remaining obligation is purely geometric and auditable: construct the
bi-finite incidence correspondence and prove its forward/transpose transition
formulas.  No Hodge surjectivity, target-basis algebraicity, perfect pairing,
or coefficient/homology identification is assumed.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgePrincipalCutFlagCorrespondenceDescent

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgePointNormalForm
open GSTClassicalHodgePrincipalCutSuccessorOperator
open GSTClassicalHodgePrincipalCutIncidenceTransposeCosmology
open GSTClassicalHodgePrincipalCutFlagNativeReturn
open GSTClassicalHodgeFiniteClosedCorrespondence
open GSTClassicalHodgeFiniteClosedCorrespondenceTranspose
open GSTClassicalHodgeGradedFiniteClosedCorrespondence
open GSTClassicalHodgeCrossWeightNativePropagation

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/--
An honest geometric realization of one finite principal-cut incidence chart.

The forward equation identifies the left-fiber transition with the already
constructed principal-cut successor row.  The transpose equation identifies
the *actual algebraic factor-swap correspondence* with the finite reverse
incidence column.  Keeping both equations explicit prevents any accidental
replacement of geometric transpose by a formal coefficient adjoint.
-/
structure PrincipalCutFlagBiFiniteRealization
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (sigma : Finset (CodimensionPoint V.X p)) where
  correspondence : BiFiniteClosedCorrespondence V
  forward_transition :
    ∀ x : CodimensionPoint V.X p,
      x ∈ sigma →
        correspondence.toFiniteClosedCorrespondence.gradedTransition (p + 1) x =
          successorPresentation V p x
  transpose_transition :
    ∀ y : CodimensionPoint V.X (p + 1),
      correspondence.transpose.gradedTransition p y =
        localTransposeColumn V p sigma y

namespace PrincipalCutFlagBiFiniteRealization

/-- On a chart source atom, the genuine forward correspondence gives exactly
its principal-cut successor cycle. -/
theorem forward_point_cycle
    {sigma : Finset (CodimensionPoint V.X p)}
    (R : PrincipalCutFlagBiFiniteRealization V p sigma)
    (x : CodimensionPoint V.X p)
    (hx : x ∈ sigma) :
    R.correspondence.toFiniteClosedCorrespondence.gradedNativeCycleOperator
        p (p + 1) (codimensionPointCycle V.X p x) =
      successorNativeOperator V p (codimensionPointCycle V.X p x) := by
  rw [GSTClassicalHodgeFiniteClosedCorrespondence.FiniteClosedCorrespondence.gradedNativeCycleOperator_point]
  rw [successorNativeOperator_point]
  unfold GSTClassicalHodgeFiniteClosedCorrespondence.FiniteClosedCorrespondence.gradedNativePointImage
  rw [R.forward_transition x hx]

/-- The hand-written reverse flag sends a target point atom to realization of
its exact finite transpose column. -/
theorem localTransposeNativeOperator_point
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (sigma : Finset (CodimensionPoint V.X p))
    (y : CodimensionPoint V.X (p + 1)) :
    localTransposeNativeOperator V p sigma
        (codimensionPointCycle V.X (p + 1) y) =
      realizeFiniteCodimensionPresentation V.X p
        (localTransposeColumn V p sigma y) := by
  have h := localTransposeNativeOperator_realize
    V p sigma (Finsupp.single y (1 : ℚ))
  simpa [localSuccessorTranspose, localTransposeColumn,
    codimensionPointCycle, realizeFiniteCodimensionPresentation] using h

/-- On every target point atom, the genuine algebraic transpose correspondence
agrees with the finite reverse principal-cut flag. -/
theorem transpose_point_cycle
    {sigma : Finset (CodimensionPoint V.X p)}
    (R : PrincipalCutFlagBiFiniteRealization V p sigma)
    (y : CodimensionPoint V.X (p + 1)) :
    R.correspondence.transpose.gradedNativeCycleOperator
        (p + 1) p (codimensionPointCycle V.X (p + 1) y) =
      localTransposeNativeOperator V p sigma
        (codimensionPointCycle V.X (p + 1) y) := by
  rw [GSTClassicalHodgeFiniteClosedCorrespondence.FiniteClosedCorrespondence.gradedNativeCycleOperator_point]
  unfold GSTClassicalHodgeFiniteClosedCorrespondence.FiniteClosedCorrespondence.gradedNativePointImage
  rw [R.transpose_transition y]
  exact (localTransposeNativeOperator_point V p sigma y).symm

/-- **GEOMETRIC IDENTIFICATION OF THE REVERSE FLAG.**
The reverse principal-cut operator on all native cycles is exactly the graded
native operator of the actual transposed closed correspondence. -/
theorem transpose_cycleOperator_eq_localTranspose
    {sigma : Finset (CodimensionPoint V.X p)}
    (R : PrincipalCutFlagBiFiniteRealization V p sigma) :
    R.correspondence.transpose.gradedNativeCycleOperator (p + 1) p =
      localTransposeNativeOperator V p sigma := by
  have hzero :
      R.correspondence.transpose.gradedNativeCycleOperator (p + 1) p -
          localTransposeNativeOperator V p sigma = 0 := by
    apply nativeLinearMap_eq_zero_of_points V (p + 1)
    intro y
    rw [LinearMap.sub_apply, R.transpose_point_cycle y]
    simp
  exact sub_eq_zero.mp hzero

/-- Ordinary Betti naturality of the genuine transpose therefore gives an
exact cycle-class commuting square for the *existing* reverse flag. -/
theorem localTranspose_cycleClass_natural
    {sigma : Finset (CodimensionPoint V.X p)}
    (R : PrincipalCutFlagBiFiniteRealization V p sigma)
    (N : GradedCorrespondencePointNaturality
      R.correspondence.transpose H (p + 1) p)
    (Z : codimensionCycles V.X (p + 1)) :
    H.cycleClass p (localTransposeNativeOperator V p sigma Z) =
      N.cohomologyOperator (H.cycleClass (p + 1) Z) := by
  rw [← R.transpose_cycleOperator_eq_localTranspose]
  exact N.cycleClass_natural Z

/-- In particular the reverse flag kills every cycle-class kernel element.
This is precisely the homological-descent property previously obtained from
`PrincipalCutFlagProjectionFormula`, now supplied by genuine correspondence
geometry instead of a coefficient pairing. -/
theorem localTranspose_kernelStable
    {sigma : Finset (CodimensionPoint V.X p)}
    (R : PrincipalCutFlagBiFiniteRealization V p sigma)
    (N : GradedCorrespondencePointNaturality
      R.correspondence.transpose H (p + 1) p)
    (Z : codimensionCycles V.X (p + 1))
    (hZ : H.cycleClass (p + 1) Z = 0) :
    H.cycleClass p (localTransposeNativeOperator V p sigma Z) = 0 := by
  rw [R.localTranspose_cycleClass_natural N Z, hZ]
  exact N.cohomologyOperator.map_zero

/-- **CORRESPONDENCE-DESCENDED REVERSE FLAG PAIR.**
A bi-finite incidence realization plus ordinary pointwise Betti naturality of
its algebraic transpose manufactures the exact graded return operator consumed
by the cross-weight Hodge machinery. -/
noncomputable def reverseFlagOperatorPair
    {sigma : Finset (CodimensionPoint V.X p)}
    (R : PrincipalCutFlagBiFiniteRealization V p sigma)
    (N : GradedCorrespondencePointNaturality
      R.correspondence.transpose H (p + 1) p) :
    GradedCycleClassOperatorPair V H (p + 1) p where
  cycleOperator := localTransposeNativeOperator V p sigma
  cohomologyOperator := N.cohomologyOperator
  cycleClass_natural := fun Z => R.localTranspose_cycleClass_natural N Z

#check PrincipalCutFlagBiFiniteRealization
#check PrincipalCutFlagBiFiniteRealization.forward_point_cycle
#check PrincipalCutFlagBiFiniteRealization.transpose_point_cycle
#check PrincipalCutFlagBiFiniteRealization.transpose_cycleOperator_eq_localTranspose
#check PrincipalCutFlagBiFiniteRealization.localTranspose_cycleClass_natural
#check PrincipalCutFlagBiFiniteRealization.localTranspose_kernelStable
#check PrincipalCutFlagBiFiniteRealization.reverseFlagOperatorPair

#print axioms PrincipalCutFlagBiFiniteRealization.forward_point_cycle
#print axioms PrincipalCutFlagBiFiniteRealization.transpose_cycleOperator_eq_localTranspose
#print axioms PrincipalCutFlagBiFiniteRealization.localTranspose_cycleClass_natural
#print axioms PrincipalCutFlagBiFiniteRealization.reverseFlagOperatorPair

end PrincipalCutFlagBiFiniteRealization

end GSTClassicalHodgePrincipalCutFlagCorrespondenceDescent
