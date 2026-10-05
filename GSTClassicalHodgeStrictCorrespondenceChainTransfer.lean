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
open GSTClassicalHodgeAnalytificationFunctoriality
open GSTClassicalHodgeSchemeFiniteCorrespondenceFirewall
open GSTClassicalHodgeStrictGraphCorrespondence
open GSTClassicalHodgeStrictCorrespondenceAnalyticSpan
open GSTClassicalHodgeStrictCorrespondenceAnalyticTranspose
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

/-- A continuous section of the intrinsic analytic right projection produces
an honest degree-one finite chain transfer.  This removes any need to supply a
Betti trace independently whenever the right leg is analytically split.

The proof is pure singular-chain functoriality: map the section covariantly and
use `section ≫ right = id`. -/
noncomputable def ofRightSection
    (s : A.space ⟶ analyticCarrier A K)
    (hs : s ≫ analyticRight A K = 𝟙 A.space) :
    RightFiniteChainTransfer A K := by
  let F :=
    (singularChainComplexFunctor (ModuleCat ℚ)).obj rationalCoefficient
  refine {
    transfer := F.map s
    degree := 1
    degree_ne_zero := one_ne_zero
    transfer_right := ?_
  }
  change F.map s ≫ F.map (analyticRight A K) =
    (1 : ℚ) • 𝟙 (rationalSingularChains A)
  rw [← F.map_comp, hs, F.map_id]
  simp

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

/-- A point of the analytification determines the corresponding actual complex
point of the strict graph carrier. -/
noncomputable def strictGraphCarrierPoint
    (f : ComplexSchemeEndomorphism V)
    (hf : IsFinite f.hom)
    (x : A.space) :
    CarrierComplexPoint (strictGraph f hf) := by
  let cx := A.pointsEquiv.symm x
  refine ⟨cx.1, ?_⟩
  rw [strictGraph_left]
  simpa using cx.2

/-- The intrinsic analytic point of the strict graph is exactly `(x,f(x))`. -/
theorem strictGraph_carrierPointPair
    (f : ComplexSchemeEndomorphism V)
    (hf : IsFinite f.hom)
    (x : A.space) :
    carrierPointPair A (strictGraph f hf) (strictGraphCarrierPoint A f hf x) =
      (x, transportedPointMap A f x) := by
  apply Prod.ext
  · change A.pointsEquiv _ = x
    simp [carrierPointPair, leftComplexPoint, strictGraphCarrierPoint,
      strictGraph_left]
  · change A.pointsEquiv _ = transportedPointMap A f x
    simp [carrierPointPair, rightComplexPoint, strictGraphCarrierPoint,
      strictGraph_right, transportedPointMap,
      ComplexSchemeEndomorphism.complexPointMap]

/-- The same actual carrier point, viewed in the genuine factor-swap
transpose. -/
noncomputable def strictGraphTransposeCarrierPoint
    (f : ComplexSchemeEndomorphism V)
    (hf : IsFinite f.hom)
    (x : A.space) :
    CarrierComplexPoint (strictGraph f hf).transpose :=
  (transposeCarrierPointEquiv (strictGraph f hf)).symm
    (strictGraphCarrierPoint A f hf x)

/-- The intrinsic analytic point of the transposed strict graph is exactly
`(f(x),x)`. -/
theorem strictGraphTranspose_carrierPointPair
    (f : ComplexSchemeEndomorphism V)
    (hf : IsFinite f.hom)
    (x : A.space) :
    carrierPointPair A (strictGraph f hf).transpose
        (strictGraphTransposeCarrierPoint A f hf x) =
      (transportedPointMap A f x, x) := by
  rw [transpose_carrierPointPair]
  simp [strictGraphTransposeCarrierPoint, strictGraph_carrierPointPair]

/-- Canonical continuous section of the right analytic projection of the
transposed graph.  It is the genuine analytic graph map `x ↦ (f(x),x)`. -/
noncomputable def strictGraphTransposeRightSection
    (f : AnalyticEndomorphism A)
    (hf : IsFinite f.algebraic.hom) :
    A.space ⟶ analyticCarrier A (strictGraph f.algebraic hf).transpose :=
  ConcreteCategory.ofHom (C := TopCat) ⟨
    (fun x => ⟨(transportedPointMap A f.algebraic x, x),
      ⟨strictGraphTransposeCarrierPoint A f.algebraic hf x,
        strictGraphTranspose_carrierPointPair A f.algebraic hf x⟩⟩),
    by
      exact Continuous.subtype_mk
        (f.continuous_toFun.prod_mk continuous_id) _⟩

/-- The graph section is a literal right inverse. -/
@[simp]
theorem strictGraphTransposeRightSection_right
    (f : AnalyticEndomorphism A)
    (hf : IsFinite f.algebraic.hom) :
    strictGraphTransposeRightSection A f hf ≫
        analyticRight A (strictGraph f.algebraic hf).transpose =
      𝟙 A.space := by
  ext x
  rfl

/-- **CANONICAL GRAPH-TRANSPOSE CHAIN TRANSFER.**
A finite analytic endomorphism has a theorem-level degree-one transfer on the
transposed strict graph; no transfer field or Betti trace is supplied. -/
noncomputable def strictGraphTransposeChainTransfer
    (f : AnalyticEndomorphism A)
    (hf : IsFinite f.algebraic.hom) :
    RightFiniteChainTransfer A (strictGraph f.algebraic hf).transpose :=
  RightFiniteChainTransfer.ofRightSection A _
    (strictGraphTransposeRightSection A f hf)
    (strictGraphTransposeRightSection_right A f hf)

/-- Consequently the exact finite Betti trace consumed by strict push-pull is
canonical for every transposed finite analytic graph. -/
noncomputable def strictGraphTransposeBettiTrace
    (f : AnalyticEndomorphism A)
    (hf : IsFinite f.algebraic.hom)
    (n : Nat) :
    RightFiniteBettiTrace A (strictGraph f.algebraic hf).transpose n :=
  (strictGraphTransposeChainTransfer A f hf).toRightFiniteBettiTrace n

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
#check RightFiniteChainTransfer.ofRightSection
#check strictGraphCarrierPoint
#check strictGraph_carrierPointPair
#check strictGraphTransposeRightSection
#check strictGraphTransposeChainTransfer
#check strictGraphTransposeBettiTrace
#check RightFiniteChainTransfer.cochainTrace
#check RightFiniteChainTransfer.cohomologyTrace
#check RightFiniteChainTransfer.cohomologyTrace_rightPullback
#check RightFiniteChainTransfer.toRightFiniteBettiTrace
#check RightFiniteChainTransfer.pushPull
#check BiFiniteChainTransfer
#check BiFiniteChainTransfer.toBiFiniteBettiTrace

#print axioms RightFiniteChainTransfer.ofRightSection
#print axioms strictGraphTransposeChainTransfer
#print axioms strictGraphTransposeBettiTrace
#print axioms RightFiniteChainTransfer.cohomologyTrace_rightPullback
#print axioms RightFiniteChainTransfer.toRightFiniteBettiTrace
#print axioms RightFiniteChainTransfer.pushPull

end GSTClassicalHodgeStrictCorrespondenceChainTransfer
