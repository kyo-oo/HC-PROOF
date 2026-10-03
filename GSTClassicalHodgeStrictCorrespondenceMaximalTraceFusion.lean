import GSTClassicalHodgeStrictCorrespondenceMaximalBettiTransfer
import GSTClassicalHodgeStrictCorrespondenceBettiTracePushPull

/-!
# GST CLASSICAL HODGE — MAXIMAL TRANSFER / FINITE TRACE FUSION

There are two genuinely canonical constructions attached to a strict
scheme-bi-finite correspondence:

* the relation-only maximal transfer, defined on `ker Omega_K` and valued in
  `H / ker(r^*)`;
* the finite-trace push-pull `Tr_r o l^*`, defined on the whole Betti carrier.

A nonzero finite-degree trace makes `r^*` injective and is a normalized left
inverse of it.  Therefore, on every class where the relation-only transfer has
a target, the total trace push-pull is EXACTLY that target.  This theorem fuses
the two lanes and proves they are not competing semantics.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicGeometry

namespace GSTClassicalHodgeStrictCorrespondenceMaximalTraceFusion

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

/-- Finite trace removes the target ambiguity of the maximal relation transfer. -/
theorem targetAmbiguity_eq_bot_of_finiteTrace
    (T : RightFiniteBettiTrace A K n) :
    targetAmbiguity A K n = ⊥ := by
  exact targetAmbiguity_eq_bot A K n T.rightPullback_injective

/-- On every transferable class, normalized finite-trace push-pull satisfies
exactly the original strict correspondence relation. -/
theorem pushPull_related_of_transferable
    (T : RightFiniteBettiTrace A K n)
    (alpha : transferableSubspace A K n) :
    BettiRelated A K n alpha.1 (T.pushPull alpha.1) := by
  have hmem := transferable_left_mem_rightRange A K n alpha
  rcases hmem with ⟨beta, hbeta⟩
  have hrel :
      leftCohomologyPullback A K n alpha.1 =
        rightCohomologyPullback A K n beta := hbeta.symm
  have hpush : T.pushPull alpha.1 = beta := by
    rw [RightFiniteBettiTrace.pushPull_apply]
    rw [hrel]
    have hs := LinearMap.congr_fun T.normalizedTrace_rightPullback beta
    simpa [LinearMap.comp_apply] using hs
  rw [hpush]
  exact hrel

/-- **HIDDEN FUSION THEOREM.**
The quotient class produced by GLM's maximal canonical transfer is literally
the quotient class of the independently constructed finite-trace push-pull. -/
theorem maximalBettiTransfer_eq_pushPull_mod_ambiguity
    (T : RightFiniteBettiTrace A K n)
    (alpha : transferableSubspace A K n) :
    maximalBettiTransfer A K n alpha =
      Submodule.Quotient.mk (T.pushPull alpha.1) := by
  symm
  exact (quotient_eq_maximalTransfer_iff_related A K n alpha
    (T.pushPull alpha.1)).2
      (pushPull_related_of_transferable A K n T alpha)

/-- Because finite trace kills the ambiguity kernel, two relation targets are
already equal as honest Betti classes, not merely equal modulo a quotient. -/
theorem related_target_unique_of_finiteTrace
    (T : RightFiniteBettiTrace A K n)
    {alpha beta gamma : RationalSingularCohomology A n}
    (hbeta : BettiRelated A K n alpha beta)
    (hgamma : BettiRelated A K n alpha gamma) :
    beta = gamma := by
  exact related_target_unique A K n T.rightPullback_injective hbeta hgamma

/-- On a transferable class, finite-trace push-pull is the unique honest Betti
target satisfying the strict analytic correspondence equation. -/
theorem pushPull_unique_related_target
    (T : RightFiniteBettiTrace A K n)
    (alpha : transferableSubspace A K n)
    (beta : RationalSingularCohomology A n)
    (hbeta : BettiRelated A K n alpha.1 beta) :
    beta = T.pushPull alpha.1 := by
  exact related_target_unique_of_finiteTrace A K n T hbeta
    (pushPull_related_of_transferable A K n T alpha)

#check targetAmbiguity_eq_bot_of_finiteTrace
#check pushPull_related_of_transferable
#check maximalBettiTransfer_eq_pushPull_mod_ambiguity
#check related_target_unique_of_finiteTrace
#check pushPull_unique_related_target

#print axioms pushPull_related_of_transferable
#print axioms maximalBettiTransfer_eq_pushPull_mod_ambiguity
#print axioms pushPull_unique_related_target

end GSTClassicalHodgeStrictCorrespondenceMaximalTraceFusion
