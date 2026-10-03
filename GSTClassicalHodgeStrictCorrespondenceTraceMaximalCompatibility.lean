import GSTClassicalHodgeStrictCorrespondenceMaximalBettiTransfer
import GSTClassicalHodgeStrictCorrespondenceBettiTracePushPull

/-!
# GST CLASSICAL HODGE — TRACE / MAXIMAL-TRANSFER COMPATIBILITY

The intrinsic analytic relation and the finite-trace push-pull are different
constructions globally.  The relation only determines a target when
`l^* alpha` lies in the range of `r^*`; a finite trace gives a pushforward for
every class.

On the maximal transferable domain, however, the two constructions cannot
disagree.  If `l^* alpha = r^* beta`, applying the normalized trace gives

    Tr_r(l^* alpha) = beta,

because normalized trace is a left inverse of `r^*`.  Thus the whole-Betti
trace action is the unique extension of the canonical relation transfer on the
part of cohomology where the relation itself already determines an answer.

This is an important non-circularity theorem: the trace enhancement does not
alter any target already fixed by the strict correspondence geometry.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicGeometry

namespace GSTClassicalHodgeStrictCorrespondenceTraceMaximalCompatibility

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTClassicalHodgeSchemeFiniteCorrespondenceFirewall
open GSTClassicalHodgeStrictCorrespondenceAnalyticSpan
open GSTClassicalHodgeStrictCorrespondenceBettiObstruction
open GSTClassicalHodgeStrictCorrespondenceMaximalBettiTransfer
open GSTClassicalHodgeStrictCorrespondenceBettiTracePushPull

variable {V : SmoothProjectiveComplexScheme}
variable (A : AnalytificationData V)
variable (K : SchemeBiFiniteClosedCorrespondence V)
variable (n : Nat)

abbrev XCoh := RationalSingularCohomology A n

/-- On a genuinely related pair, finite trace push-pull recovers exactly the
related target. -/
theorem RightFiniteBettiTrace.pushPull_eq_of_related
    (T : RightFiniteBettiTrace A K n)
    {alpha beta : XCoh A n}
    (hrel : BettiRelated A K n alpha beta) :
    T.pushPull alpha = beta := by
  change T.normalizedTrace (leftCohomologyPullback A K n alpha) = beta
  rw [hrel]
  have h := LinearMap.congr_fun T.normalizedTrace_rightPullback beta
  simpa [LinearMap.comp_apply] using h

/-- Every transferable class is related to the trace push-pull target. -/
theorem RightFiniteBettiTrace.pushPull_related
    (T : RightFiniteBettiTrace A K n)
    (alpha : transferableSubspace A K n) :
    BettiRelated A K n alpha.1 (T.pushPull alpha.1) := by
  rcases (transferObstruction_apply_eq_zero_iff_exists_related
      A K n alpha.1).1 alpha.2 with ⟨beta, hbeta⟩
  rw [T.pushPull_eq_of_related A K hbeta]
  exact hbeta

/-- **TRACE EXTENDS THE MAXIMAL CANONICAL TRANSFER.**
The quotient class of finite-trace push-pull is exactly the choice-free
maximal transfer value on every transferable source. -/
theorem RightFiniteBettiTrace.quotient_pushPull_eq_maximalBettiTransfer
    (T : RightFiniteBettiTrace A K n)
    (alpha : transferableSubspace A K n) :
    Submodule.Quotient.mk (T.pushPull alpha.1) =
      maximalBettiTransfer A K n alpha := by
  exact (quotient_eq_maximalTransfer_iff_related A K n alpha
    (T.pushPull alpha.1)).2 (T.pushPull_related A K alpha)

/-- Because the finite trace makes `r^*` injective, target ambiguity vanishes. -/
theorem RightFiniteBettiTrace.targetAmbiguity_eq_bot
    (T : RightFiniteBettiTrace A K n) :
    targetAmbiguity A K n = ⊥ :=
  GSTClassicalHodgeStrictCorrespondenceMaximalBettiTransfer.targetAmbiguity_eq_bot
    A K n T.rightPullback_injective

/-- Elementwise uniqueness: the trace action is the unique actual target whose
strict right pullback equals the strict left pullback whenever such a target
exists. -/
theorem RightFiniteBettiTrace.pushPull_unique_related
    (T : RightFiniteBettiTrace A K n)
    {alpha beta : XCoh A n}
    (hrel : BettiRelated A K n alpha beta) :
    beta = T.pushPull alpha := by
  exact (T.pushPull_eq_of_related A K hrel).symm

/-- Any full linear operator satisfying the strict analytic relation everywhere
must coincide with trace push-pull.  This applies when the relation is total;
it is stronger than uniqueness on the algebraic cycle-class range. -/
theorem RightFiniteBettiTrace.unique_total_related_operator
    (T : RightFiniteBettiTrace A K n)
    (U : XCoh A n →ₗ[ℚ] XCoh A n)
    (hU : ∀ alpha : XCoh A n,
      BettiRelated A K n alpha (U alpha)) :
    U = T.pushPull := by
  apply LinearMap.ext
  intro alpha
  exact T.pushPull_unique_related A K (hU alpha)

#check RightFiniteBettiTrace.pushPull_eq_of_related
#check RightFiniteBettiTrace.pushPull_related
#check RightFiniteBettiTrace.quotient_pushPull_eq_maximalBettiTransfer
#check RightFiniteBettiTrace.targetAmbiguity_eq_bot
#check RightFiniteBettiTrace.unique_total_related_operator

end GSTClassicalHodgeStrictCorrespondenceTraceMaximalCompatibility
