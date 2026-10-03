import GSTClassicalHodgeStrictCorrespondenceBettiTracePushPull

/-!
# GST CLASSICAL HODGE — STRICT FINITE CHAIN TRANSFER

The cohomological finite trace used by push-pull is itself not primitive.  The
more geometric object is a transfer on singular CHAINS for the finite analytic
right projection.  Dualizing that chain transfer by the same linear-Yoneda
construction already used by Stage 2F produces the cochain trace; homology of
that cochain map produces the full rational Betti trace.

Thus the complete correspondence action is reduced one level further:

  finite analytic chain transfer
      -> cochain trace
      -> Betti trace
      -> normalized push-pull Tr_r o l^*.

This layer never mentions Hodge algebraicity or the cycle-class range.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicTopology

namespace GSTClassicalHodgeStrictCorrespondenceChainTransfer

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTClassicalHodgeSchemeFiniteCorrespondenceFirewall
open GSTClassicalHodgeStrictCorrespondenceAnalyticSpan
open GSTClassicalHodgeStrictCorrespondenceBettiTracePushPull

variable {V : SmoothProjectiveComplexScheme}
variable (A : AnalytificationData V)
variable (K : SchemeBiFiniteClosedCorrespondence V)

/-- Primitive finite-transfer datum on actual rational singular chains.  The
transfer goes from the base `X^an` into the correspondence carrier; composing
with the right-projection chain map is multiplication by the nonzero finite
degree. -/
structure RightFiniteChainTransfer where
  transfer : rationalSingularChains A ⟶ carrierSingularChains A K
  degree : ℚ
  degree_ne_zero : degree ≠ 0
  transfer_right :
    transfer ≫ rightChainMap A K = degree • 𝟙 (rationalSingularChains A)

namespace RightFiniteChainTransfer

/-- Dualize the chain transfer.  Because linear Yoneda reverses arrows, this
is the desired covariant trace on cochains of the carrier. -/
noncomputable def cochainTrace
    (T : RightFiniteChainTransfer A K) :
    carrierSingularCochains A K ⟶ rationalSingularCochains A := by
  let F :=
    ((CategoryTheory.linearYoneda ℚ (ModuleCat ℚ)).obj rationalCoefficient).rightOp
      |>.mapHomologicalComplex (ComplexShape.down ℕ)
  exact (F.map T.transfer).unop

/-- Induced trace on the genuine rational singular cohomology object. -/
noncomputable def cohomologyTraceObj
    (T : RightFiniteChainTransfer A K)
    (n : Nat) :
    carrierCohomologyObj A K n ⟶ rationalSingularCohomologyObj A n :=
  HomologicalComplex.homologyMap T.cochainTrace n

/-- Underlying rational-linear Betti trace. -/
noncomputable def cohomologyTrace
    (T : RightFiniteChainTransfer A K)
    (n : Nat) :
    CarrierCohomology A K n →ₗ[ℚ] RationalSingularCohomology A n :=
  (T.cohomologyTraceObj n).hom

/-- The chain-level finite-degree identity descends through duality and
cohomology to the finite-degree trace identity. -/
theorem cohomologyTrace_rightPullback
    (T : RightFiniteChainTransfer A K)
    (n : Nat) :
    (T.cohomologyTrace n).comp (rightCohomologyPullback A K n) =
      T.degree • LinearMap.id := by
  ext alpha
  simp [cohomologyTrace, cohomologyTraceObj, cochainTrace,
    rightCohomologyPullback, rightCohomologyPullbackObj,
    rightCochainPullback, T.transfer_right]

/-- Every genuine chain transfer therefore manufactures the exact Betti trace
packet consumed by the whole-cohomology push-pull construction. -/
noncomputable def toRightFiniteBettiTrace
    (T : RightFiniteChainTransfer A K)
    (n : Nat) : RightFiniteBettiTrace A K n where
  trace := T.cohomologyTrace n
  degree := T.degree
  degree_ne_zero := T.degree_ne_zero
  trace_rightPullback := T.cohomologyTrace_rightPullback n

/-- **CHAIN-LEVEL WHOLE-BETTI PUSH-PULL.** -/
noncomputable def pushPull
    (T : RightFiniteChainTransfer A K)
    (n : Nat) :
    RationalSingularCohomology A n →ₗ[ℚ] RationalSingularCohomology A n :=
  (T.toRightFiniteBettiTrace n).pushPull

/-- The resulting action is explicitly normalized transfer after the genuine
left pullback. -/
theorem pushPull_apply
    (T : RightFiniteChainTransfer A K)
    (n : Nat)
    (alpha : RationalSingularCohomology A n) :
    T.pushPull n alpha =
      (T.toRightFiniteBettiTrace n).normalizedTrace
        (leftCohomologyPullback A K n alpha) := rfl

end RightFiniteChainTransfer

/-- A strict correspondence together with chain transfers for both it and its
actual algebraic transpose. -/
structure BiFiniteChainTransfer where
  forward : RightFiniteChainTransfer A K
  transpose : RightFiniteChainTransfer A K.transpose

namespace BiFiniteChainTransfer

/-- Canonical whole-Betti forward action. -/
noncomputable def forwardAction
    (T : BiFiniteChainTransfer A K)
    (n : Nat) :=
  T.forward.pushPull n

/-- Canonical whole-Betti action of the genuine factor-swap transpose. -/
noncomputable def transposeAction
    (T : BiFiniteChainTransfer A K)
    (n : Nat) :=
  T.transpose.pushPull n

end BiFiniteChainTransfer

#check RightFiniteChainTransfer
#check RightFiniteChainTransfer.cochainTrace
#check RightFiniteChainTransfer.cohomologyTrace
#check RightFiniteChainTransfer.cohomologyTrace_rightPullback
#check RightFiniteChainTransfer.toRightFiniteBettiTrace
#check RightFiniteChainTransfer.pushPull
#check BiFiniteChainTransfer
#check BiFiniteChainTransfer.forwardAction
#check BiFiniteChainTransfer.transposeAction

#print axioms RightFiniteChainTransfer.cohomologyTrace_rightPullback
#print axioms RightFiniteChainTransfer.toRightFiniteBettiTrace
#print axioms RightFiniteChainTransfer.pushPull

end GSTClassicalHodgeStrictCorrespondenceChainTransfer
