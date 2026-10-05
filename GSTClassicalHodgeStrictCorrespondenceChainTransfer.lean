import GSTClassicalHodgeStrictCorrespondenceBettiTracePushPull
import GSTClassicalHodgeStrictGraphCorrespondence

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
open GSTClassicalHodgeStrictCorrespondenceChainTranspose
open GSTClassicalHodgeStrictCorrespondenceBettiTracePushPull

variable {V : SmoothProjectiveComplexScheme}
variable (A : AnalytificationData V)
variable (K : SchemeBiFiniteClosedCorrespondence V)

/-- Primitive finite transfer on rational singular chains.  This is strictly
pre-Hodge geometric data. -/
structure RightFiniteChainTransfer where
  transfer : rationalSingularChains A ⟶ carrierSingularChains A K
  degree : ℚ
  degree_ne_zero : degree ≠ 0
  transfer_right :
    transfer ≫ rightChainMap A K = degree • 𝟙 (rationalSingularChains A)

namespace RightFiniteChainTransfer

/-- Dualizing the chain transfer reverses its arrow and produces the covariant
cochain trace required for push-pull. -/
noncomputable def cochainTrace
    (T : RightFiniteChainTransfer A K) :
    carrierSingularCochains A K ⟶ rationalSingularCochains A := by
  let F :=
    ((CategoryTheory.linearYoneda ℚ (ModuleCat ℚ)).obj rationalCoefficient).rightOp
      |>.mapHomologicalComplex (ComplexShape.down ℕ)
  exact (F.map T.transfer).unop

noncomputable def cohomologyTraceObj
    (T : RightFiniteChainTransfer A K)
    (n : Nat) :
    carrierCohomologyObj A K n ⟶ rationalSingularCohomologyObj A n :=
  HomologicalComplex.homologyMap T.cochainTrace n

noncomputable def cohomologyTrace
    (T : RightFiniteChainTransfer A K)
    (n : Nat) :
    CarrierCohomology A K n →ₗ[ℚ] RationalSingularCohomology A n :=
  (T.cohomologyTraceObj n).hom

/-- **CHAIN TRANSFER DESCENT.** The finite-degree chain identity descends
through linear-Yoneda duality and cohomology. -/
theorem cohomologyTrace_rightPullback
    (T : RightFiniteChainTransfer A K)
    (n : Nat) :
    (T.cohomologyTrace n).comp (rightCohomologyPullback A K n) =
      T.degree • LinearMap.id := by
  ext alpha
  simp [cohomologyTrace, cohomologyTraceObj, cochainTrace,
    rightCohomologyPullback, rightCohomologyPullbackObj,
    rightCochainPullback, T.transfer_right]

/-- Chain transfer manufactures the exact finite Betti trace consumed by the
whole-cohomology push-pull theorem. -/
noncomputable def toRightFiniteBettiTrace
    (T : RightFiniteChainTransfer A K)
    (n : Nat) : RightFiniteBettiTrace A K n where
  trace := T.cohomologyTrace n
  degree := T.degree
  degree_ne_zero := T.degree_ne_zero
  trace_rightPullback := T.cohomologyTrace_rightPullback n

/-- Canonical action on the entire rational singular cohomology carrier. -/
noncomputable def pushPull
    (T : RightFiniteChainTransfer A K)
    (n : Nat) :
    RationalSingularCohomology A n →ₗ[ℚ] RationalSingularCohomology A n :=
  (T.toRightFiniteBettiTrace n).pushPull

end RightFiniteChainTransfer

/-- Chain-transfer package for both the strict correspondence and its actual
algebraic transpose. -/
structure BiFiniteChainTransfer where
  forward : RightFiniteChainTransfer A K
  transpose : RightFiniteChainTransfer A K.transpose

namespace BiFiniteChainTransfer

noncomputable def forwardAction
    (T : BiFiniteChainTransfer A K) (n : Nat) :=
  T.forward.pushPull n

noncomputable def transposeAction
    (T : BiFiniteChainTransfer A K) (n : Nat) :=
  T.transpose.pushPull n

/-- Forget to the cohomological finite-trace package at one degree. -/
noncomputable def toBiFiniteBettiTrace
    (T : BiFiniteChainTransfer A K) (n : Nat) :
    BiFiniteBettiTrace A K n where
  forward := T.forward.toRightFiniteBettiTrace n
  transpose := T.transpose.toRightFiniteBettiTrace n

end BiFiniteChainTransfer

#check RightFiniteChainTransfer
#check RightFiniteChainTransfer.cochainTrace
#check RightFiniteChainTransfer.cohomologyTrace
#check RightFiniteChainTransfer.cohomologyTrace_rightPullback
#check RightFiniteChainTransfer.toRightFiniteBettiTrace
#check RightFiniteChainTransfer.pushPull
#check BiFiniteChainTransfer
#check BiFiniteChainTransfer.toBiFiniteBettiTrace

#print axioms RightFiniteChainTransfer.cohomologyTrace_rightPullback
#print axioms RightFiniteChainTransfer.toRightFiniteBettiTrace
#print axioms RightFiniteChainTransfer.pushPull

end GSTClassicalHodgeStrictCorrespondenceChainTransfer
