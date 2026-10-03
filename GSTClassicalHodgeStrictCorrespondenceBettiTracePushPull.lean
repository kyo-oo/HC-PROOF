import GSTClassicalHodgeStrictCorrespondenceBettiObstruction
import GSTClassicalHodgeStrictCorrespondenceAnalyticTranspose
import GSTClassicalHodgeGradedFiniteClosedCorrespondence

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicGeometry

namespace GSTClassicalHodgeStrictCorrespondenceBettiTracePushPull

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeSchemeFiniteCorrespondenceFirewall
open GSTClassicalHodgeStrictCorrespondenceAnalyticSpan
open GSTClassicalHodgeStrictCorrespondenceAnalyticTranspose
open GSTClassicalHodgeStrictCorrespondenceBettiObstruction
open GSTClassicalHodgeFiniteClosedCorrespondence
open GSTClassicalHodgeGradedFiniteClosedCorrespondence

variable {V : SmoothProjectiveComplexScheme}
variable (A : AnalytificationData V)
variable (K : SchemeBiFiniteClosedCorrespondence V)
variable (n : Nat)

abbrev XCoh := RationalSingularCohomology A n
abbrev CCoh := CarrierCohomology A K n

/-- Finite-map Betti trace for the right projection. -/
structure RightFiniteBettiTrace where
  trace : CCoh A K n →ₗ[ℚ] XCoh A n
  degree : ℚ
  degree_ne_zero : degree ≠ 0
  trace_rightPullback :
    trace.comp (rightCohomologyPullback A K n) =
      degree • LinearMap.id

namespace RightFiniteBettiTrace

noncomputable def normalizedTrace
    (T : RightFiniteBettiTrace A K n) :
    CCoh A K n →ₗ[ℚ] XCoh A n :=
  T.degree⁻¹ • T.trace

/-- The normalized finite trace is a left inverse of right pullback. -/
theorem normalizedTrace_rightPullback
    (T : RightFiniteBettiTrace A K n) :
    T.normalizedTrace.comp (rightCohomologyPullback A K n) = LinearMap.id := by
  ext alpha
  have h := LinearMap.congr_fun T.trace_rightPullback alpha
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply] at h ⊢
  rw [h]
  field_simp [T.degree_ne_zero]

/-- Nonzero finite degree forces injectivity of pullback. -/
theorem rightPullback_injective
    (T : RightFiniteBettiTrace A K n) :
    Function.Injective (rightCohomologyPullback A K n) := by
  intro alpha beta h
  have h' := congrArg T.normalizedTrace h
  simpa [LinearMap.comp_apply, T.normalizedTrace_rightPullback] using h'

/-- Canonical full-Betti push-pull `Tr_r ∘ l^*`. -/
noncomputable def pushPull :
    XCoh A n →ₗ[ℚ] XCoh A n :=
  T.normalizedTrace.comp (leftCohomologyPullback A K n)

@[simp]
theorem pushPull_apply
    (T : RightFiniteBettiTrace A K n)
    (alpha : XCoh A n) :
    T.pushPull alpha =
      T.normalizedTrace (leftCohomologyPullback A K n alpha) := rfl

end RightFiniteBettiTrace

/-- Forward and genuine-transpose finite traces. -/
structure BiFiniteBettiTrace where
  forward : RightFiniteBettiTrace A K n
  transpose : RightFiniteBettiTrace A K.transpose n

namespace BiFiniteBettiTrace

noncomputable def forwardAction
    (T : BiFiniteBettiTrace A K n) : XCoh A n →ₗ[ℚ] XCoh A n :=
  T.forward.pushPull

noncomputable def transposeAction
    (T : BiFiniteBettiTrace A K n) : XCoh A n →ₗ[ℚ] XCoh A n :=
  T.transpose.pushPull

end BiFiniteBettiTrace

/-- Point-incidence compatibility for the independently constructed action. -/
structure PointCycleCompatibility
    {H : HodgeBigradedBettiData V}
    (K : SchemeBiFiniteClosedCorrespondence V)
    (T : RightFiniteBettiTrace H.analytification K (2 * n)) where
  point_natural :
    ∀ x : CodimensionPoint V.X n,
      H.cycleClass n
          (K.toBiFiniteClosedCorrespondence.toFiniteClosedCorrespondence
            |>.gradedNativePointImage n x) =
        T.pushPull
          (H.cycleClass n (codimensionPointCycle V.X n x))

namespace PointCycleCompatibility

noncomputable def toGradedCorrespondencePointNaturality
    {H : HodgeBigradedBettiData V}
    {K : SchemeBiFiniteClosedCorrespondence V}
    {T : RightFiniteBettiTrace H.analytification K (2 * n)}
    (C : PointCycleCompatibility (n := n) K T) :
    GradedCorrespondencePointNaturality
      K.toBiFiniteClosedCorrespondence.toFiniteClosedCorrespondence H n n where
  cohomologyOperator := T.pushPull
  point_natural := C.point_natural

/-- Point compatibility globalizes to the complete native cycle space. -/
theorem cycleClass_natural
    {H : HodgeBigradedBettiData V}
    {K : SchemeBiFiniteClosedCorrespondence V}
    {T : RightFiniteBettiTrace H.analytification K (2 * n)}
    (C : PointCycleCompatibility (n := n) K T)
    (Z : codimensionCycles V.X n) :
    H.cycleClass n
        (K.toBiFiniteClosedCorrespondence.toFiniteClosedCorrespondence
          |>.gradedNativeCycleOperator n n Z) =
      T.pushPull (H.cycleClass n Z) := by
  exact C.toGradedCorrespondencePointNaturality.cycleClass_natural Z

end PointCycleCompatibility

#check RightFiniteBettiTrace
#check RightFiniteBettiTrace.normalizedTrace_rightPullback
#check RightFiniteBettiTrace.rightPullback_injective
#check RightFiniteBettiTrace.pushPull
#check BiFiniteBettiTrace
#check PointCycleCompatibility.cycleClass_natural

#print axioms RightFiniteBettiTrace.normalizedTrace_rightPullback
#print axioms RightFiniteBettiTrace.rightPullback_injective
#print axioms PointCycleCompatibility.cycleClass_natural

end GSTClassicalHodgeStrictCorrespondenceBettiTracePushPull
