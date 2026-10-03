import GSTClassicalHodgeStrictCorrespondenceMaximalBettiTransfer
import GSTClassicalHodgeStrictCorrespondenceChainTranspose
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
open GSTClassicalHodgeStrictCorrespondenceBettiObstruction
open GSTClassicalHodgeStrictCorrespondenceMaximalBettiTransfer
open GSTClassicalHodgeFiniteClosedCorrespondence
open GSTClassicalHodgeGradedFiniteClosedCorrespondence

variable {V : SmoothProjectiveComplexScheme}
variable (A : AnalytificationData V)
variable (K : SchemeBiFiniteClosedCorrespondence V)
variable (n : Nat)

abbrev XCoh := RationalSingularCohomology A n
abbrev CCoh := CarrierCohomology A K n

/-- Finite-map Betti trace for the right projection.  This is the geometric
covariant leg missing from the intrinsic pullback span. -/
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

/-- The normalized trace is an exact left inverse of the right pullback. -/
theorem normalizedTrace_rightPullback
    (T : RightFiniteBettiTrace A K n) :
    T.normalizedTrace.comp (rightCohomologyPullback A K n) = LinearMap.id := by
  ext alpha
  have h := LinearMap.congr_fun T.trace_rightPullback alpha
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply] at h ⊢
  rw [h]
  field_simp [T.degree_ne_zero]

/-- Nonzero finite degree forces injectivity of right pullback. -/
theorem rightPullback_injective
    (T : RightFiniteBettiTrace A K n) :
    Function.Injective (rightCohomologyPullback A K n) := by
  intro alpha beta h
  have h' := congrArg T.normalizedTrace h
  simpa [LinearMap.comp_apply, T.normalizedTrace_rightPullback] using h'

/-- **TOTAL WHOLE-BETTI PUSH-PULL.** `Tr_r ∘ l^*`, defined on every rational
singular cohomology class, including nonalgebraic Hodge classes. -/
noncomputable def pushPull : XCoh A n →ₗ[ℚ] XCoh A n :=
  T.normalizedTrace.comp (leftCohomologyPullback A K n)

@[simp]
theorem pushPull_apply
    (T : RightFiniteBettiTrace A K n)
    (alpha : XCoh A n) :
    T.pushPull alpha =
      T.normalizedTrace (leftCohomologyPullback A K n alpha) := rfl

/-- Finite trace removes the target ambiguity in GLM's maximal transfer. -/
theorem targetAmbiguity_eq_bot
    (T : RightFiniteBettiTrace A K n) :
    GSTClassicalHodgeStrictCorrespondenceMaximalBettiTransfer.targetAmbiguity A K n = ⊥ := by
  exact GSTClassicalHodgeStrictCorrespondenceMaximalBettiTransfer.targetAmbiguity_eq_bot
    A K n T.rightPullback_injective

/-- On every class on which the relation transfer is defined, trace push-pull
satisfies exactly the original strict Betti relation. -/
theorem pushPull_related_of_transferable
    (T : RightFiniteBettiTrace A K n)
    (alpha : GSTClassicalHodgeStrictCorrespondenceMaximalBettiTransfer.transferableSubspace A K n) :
    BettiRelated A K n alpha.1 (T.pushPull alpha.1) := by
  have hmem := GSTClassicalHodgeStrictCorrespondenceMaximalBettiTransfer.transferable_left_mem_rightRange
    A K n alpha
  rcases hmem with ⟨beta, hbeta⟩
  have hrel : leftCohomologyPullback A K n alpha.1 =
      rightCohomologyPullback A K n beta := hbeta.symm
  have hpush : T.pushPull alpha.1 = beta := by
    rw [pushPull_apply, hrel]
    have hs := LinearMap.congr_fun T.normalizedTrace_rightPullback beta
    simpa [LinearMap.comp_apply] using hs
  rw [hpush]
  exact hrel

/-- **MAXIMAL-TRANSFER FUSION.** GLM's canonical partial quotient transfer is
exactly the quotient class of the independently constructed total trace
push-pull. -/
theorem maximalBettiTransfer_eq_pushPull_mod_ambiguity
    (T : RightFiniteBettiTrace A K n)
    (alpha : GSTClassicalHodgeStrictCorrespondenceMaximalBettiTransfer.transferableSubspace A K n) :
    GSTClassicalHodgeStrictCorrespondenceMaximalBettiTransfer.maximalBettiTransfer A K n alpha =
      Submodule.Quotient.mk (T.pushPull alpha.1) := by
  symm
  exact (GSTClassicalHodgeStrictCorrespondenceMaximalBettiTransfer.quotient_eq_maximalTransfer_iff_related
    A K n alpha (T.pushPull alpha.1)).2
      (T.pushPull_related_of_transferable alpha)

end RightFiniteBettiTrace

/-- Forward and actual algebraic-transpose traces. -/
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

/-- Compare the independently constructed push-pull with the native finite
incidence action only on point cycles; compact point normal form then globalizes
this to every native cycle. -/
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

/-- **PROJECTIVE-INCIDENCE NATURALITY CROWN.** -/
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
#check RightFiniteBettiTrace.maximalBettiTransfer_eq_pushPull_mod_ambiguity
#check BiFiniteBettiTrace
#check PointCycleCompatibility.cycleClass_natural

#print axioms RightFiniteBettiTrace.normalizedTrace_rightPullback
#print axioms RightFiniteBettiTrace.maximalBettiTransfer_eq_pushPull_mod_ambiguity
#print axioms PointCycleCompatibility.cycleClass_natural

end GSTClassicalHodgeStrictCorrespondenceBettiTracePushPull
