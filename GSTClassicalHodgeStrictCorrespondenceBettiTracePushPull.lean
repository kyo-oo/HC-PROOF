import GSTClassicalHodgeStrictCorrespondenceBettiObstruction
import GSTClassicalHodgeStrictCorrespondenceAnalyticTranspose
import GSTClassicalHodgeGradedFiniteClosedCorrespondence

/-!
# GST CLASSICAL HODGE — STRICT BETTI TRACE PUSH-PULL

The intrinsic analytic span gives canonical pullbacks along both projections
of a strict scheme-bi-finite correspondence.  The missing covariant leg is not
an inverse to the right pullback.  For a finite map the correct object is its
Betti trace / transfer.

This file isolates that stronger construction and proves the complete linear
consequences.  A finite-map trace `Tr_r` with nonzero degree `d` satisfies

  Tr_r (r^* alpha) = d * alpha.

After normalization it is a left inverse of `r^*`.  The correspondence action
on the COMPLETE rational singular cohomology carrier is then canonically

  K_* = Tr_r o l^*.

No Hodge algebraicity, cycle-class surjectivity, basis representative, or
arbitrary extension off the algebraic range enters this construction.
-/

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

/-- Genuine finite-map Betti trace data for the right projection of the
intrinsic analytic correspondence span.  The decisive law is the standard
finite-degree trace identity `Tr_r o r^* = d id`. -/
structure RightFiniteBettiTrace where
  trace : CCoh A K n →ₗ[ℚ] XCoh A n
  degree : ℚ
  degree_ne_zero : degree ≠ 0
  trace_rightPullback :
    trace.comp (rightCohomologyPullback A K n) =
      degree • LinearMap.id

namespace RightFiniteBettiTrace

/-- Normalize the finite trace by its nonzero degree. -/
noncomputable def normalizedTrace
    (T : RightFiniteBettiTrace A K n) :
    CCoh A K n →ₗ[ℚ] XCoh A n :=
  T.degree⁻¹ • T.trace

/-- The normalized trace is an exact left inverse of the genuine right
cohomology pullback on the entire Betti carrier. -/
theorem normalizedTrace_rightPullback
    (T : RightFiniteBettiTrace A K n) :
    T.normalizedTrace.comp (rightCohomologyPullback A K n) = LinearMap.id := by
  ext alpha
  have h := LinearMap.congr_fun T.trace_rightPullback alpha
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply] at h ⊢
  rw [h]
  field_simp [T.degree_ne_zero]

/-- Finite trace forces injectivity of pullback; no separate injectivity axiom
is needed. -/
theorem rightPullback_injective
    (T : RightFiniteBettiTrace A K n) :
    Function.Injective (rightCohomologyPullback A K n) := by
  intro alpha beta h
  have h' := congrArg T.normalizedTrace h
  simpa [LinearMap.comp_apply, T.normalizedTrace_rightPullback] using h'

/-- **CANONICAL WHOLE-BETTI CORRESPONDENCE ACTION.**
Pull back through the left projection and transfer through the finite right
projection.  This is defined on every rational singular cohomology class,
including nonalgebraic Hodge classes. -/
noncomputable def pushPull :
    XCoh A n →ₗ[ℚ] XCoh A n :=
  T.normalizedTrace.comp (leftCohomologyPullback A K n)

@[simp]
theorem pushPull_apply
    (T : RightFiniteBettiTrace A K n)
    (alpha : XCoh A n) :
    T.pushPull alpha =
      T.normalizedTrace (leftCohomologyPullback A K n alpha) := rfl

/-- The trace construction is independent of the earlier range-inversion
obstruction: it produces a target even when the left pullback is not itself in
the image of the right pullback. -/
theorem pushPull_is_total
    (T : RightFiniteBettiTrace A K n) :
    ∀ alpha : XCoh A n, ∃ beta : XCoh A n, beta = T.pushPull alpha := by
  intro alpha
  exact ⟨T.pushPull alpha, rfl⟩

end RightFiniteBettiTrace

/-- Forward and genuine-transpose finite traces.  This is the bivariant packet
needed to obtain canonical actions for both an algebraic correspondence and
its actual factor-swap transpose. -/
structure BiFiniteBettiTrace where
  forward : RightFiniteBettiTrace A K n
  transpose : RightFiniteBettiTrace A K.transpose n

namespace BiFiniteBettiTrace

/-- Whole-Betti action of the actual correspondence. -/
noncomputable def forwardAction
    (T : BiFiniteBettiTrace A K n) :
    XCoh A n →ₗ[ℚ] XCoh A n :=
  T.forward.pushPull

/-- Whole-Betti action of the genuine algebraic factor-swap transpose. -/
noncomputable def transposeAction
    (T : BiFiniteBettiTrace A K n) :
    XCoh A n →ₗ[ℚ] XCoh A n :=
  T.transpose.pushPull

end BiFiniteBettiTrace

/-- The independently constructed trace push-pull can now be compared to the
existing native point-incidence action.  Notice that the cohomology operator
is NOT supplied here: it has already been constructed as `T.pushPull`. -/
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

/-- Point compatibility extends to every native codimension-n cycle by the
existing compact point normal form. -/
noncomputable def toGradedCorrespondencePointNaturality
    {H : HodgeBigradedBettiData V}
    {K : SchemeBiFiniteClosedCorrespondence V}
    {T : RightFiniteBettiTrace H.analytification K (2 * n)}
    (C : PointCycleCompatibility (n := n) K T) :
    GradedCorrespondencePointNaturality
      K.toBiFiniteClosedCorrespondence.toFiniteClosedCorrespondence H n n where
  cohomologyOperator := T.pushPull
  point_natural := C.point_natural

/-- Hence strict scheme correspondence + genuine finite Betti trace + the
pointwise incidence comparison yields an exact global cycle-class commuting
square without any off-range extension choice. -/
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
#check RightFiniteBettiTrace.normalizedTrace
#check RightFiniteBettiTrace.normalizedTrace_rightPullback
#check RightFiniteBettiTrace.rightPullback_injective
#check RightFiniteBettiTrace.pushPull
#check BiFiniteBettiTrace
#check BiFiniteBettiTrace.forwardAction
#check BiFiniteBettiTrace.transposeAction
#check PointCycleCompatibility
#check PointCycleCompatibility.cycleClass_natural

#print axioms RightFiniteBettiTrace.normalizedTrace_rightPullback
#print axioms RightFiniteBettiTrace.rightPullback_injective
#print axioms PointCycleCompatibility.cycleClass_natural

end GSTClassicalHodgeStrictCorrespondenceBettiTracePushPull
