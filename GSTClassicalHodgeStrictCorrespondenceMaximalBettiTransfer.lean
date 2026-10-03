import GSTClassicalHodgeStrictCorrespondenceBettiObstruction

/-!
# GST CLASSICAL HODGE — MAXIMAL CANONICAL BETTI TRANSFER

For a strict scheme-bi-finite correspondence the intrinsic analytic span gives
`l^*, r^* : H^n(X,Q) -> H^n(C_an,Q)` and the obstruction
`Omega_K(alpha) = [l^* alpha] mod range(r^*)`.

Before any trace/Gysin theorem is available there is already a completely
canonical, choice-free maximal action

  ker(Omega_K) -> H^n(X,Q) / ker(r^*).

This is the exact operator determined by the analytic relation itself.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicGeometry

namespace GSTClassicalHodgeStrictCorrespondenceMaximalBettiTransfer

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTClassicalHodgeSchemeFiniteCorrespondenceFirewall
open GSTClassicalHodgeStrictCorrespondenceAnalyticSpan
open GSTClassicalHodgeStrictCorrespondenceBettiObstruction

variable {V : SmoothProjectiveComplexScheme}
variable (A : AnalytificationData V)
variable (K : SchemeBiFiniteClosedCorrespondence V)
variable (n : Nat)

abbrev XCoh := RationalSingularCohomology A n
abbrev CCoh := CarrierCohomology A K n

def transferableSubspace : Submodule ℚ (XCoh A n) :=
  LinearMap.ker (transferObstruction A K n)

def targetAmbiguity : Submodule ℚ (XCoh A n) :=
  LinearMap.ker (rightCohomologyPullback A K n)

theorem transferable_left_mem_rightRange
    (alpha : transferableSubspace A K n) :
    leftCohomologyPullback A K n alpha.1 ∈ rightPullbackRange A K n := by
  exact (transferObstruction_apply_eq_zero_iff A K n alpha.1).1 alpha.2

noncomputable def transferableRangeMap :
    transferableSubspace A K n →ₗ[ℚ]
      LinearMap.range (rightCohomologyPullback A K n) where
  toFun := fun alpha =>
    ⟨leftCohomologyPullback A K n alpha.1,
      transferable_left_mem_rightRange A K n alpha⟩
  map_add' := by intro a b; apply Subtype.ext; simp
  map_smul' := by intro q a; apply Subtype.ext; simp

/-- **MAXIMAL CANONICAL STRICT-CORRESPONDENCE TRANSFER.** -/
noncomputable def maximalBettiTransfer :
    transferableSubspace A K n →ₗ[ℚ]
      (XCoh A n ⧸ targetAmbiguity A K n) :=
  (rightCohomologyPullback A K n).quotKerEquivRange.symm.toLinearMap.comp
    (transferableRangeMap A K n)

theorem maximalBettiTransfer_spec
    (alpha : transferableSubspace A K n) :
    (rightCohomologyPullback A K n).quotKerEquivRange
      (maximalBettiTransfer A K n alpha) =
        transferableRangeMap A K n alpha := by
  simp [maximalBettiTransfer]

theorem quotient_eq_maximalTransfer_iff_related
    (alpha : transferableSubspace A K n)
    (beta : XCoh A n) :
    Submodule.Quotient.mk beta = maximalBettiTransfer A K n alpha ↔
      BettiRelated A K n alpha.1 beta := by
  constructor
  · intro hq
    have hrange := congrArg
      (rightCohomologyPullback A K n).quotKerEquivRange hq
    rw [maximalBettiTransfer_spec] at hrange
    change rightCohomologyPullback A K n beta =
      leftCohomologyPullback A K n alpha.1 at hrange
    exact hrange.symm
  · intro hrel
    apply (rightCohomologyPullback A K n).quotKerEquivRange.injective
    rw [maximalBettiTransfer_spec]
    apply Subtype.ext
    exact hrel.symm

theorem maximalBettiTransfer_unique
    (T : transferableSubspace A K n →ₗ[ℚ]
      (XCoh A n ⧸ targetAmbiguity A K n))
    (hT : ∀ alpha : transferableSubspace A K n,
      (rightCohomologyPullback A K n).quotKerEquivRange (T alpha) =
        transferableRangeMap A K n alpha) :
    T = maximalBettiTransfer A K n := by
  apply LinearMap.ext
  intro alpha
  apply (rightCohomologyPullback A K n).quotKerEquivRange.injective
  rw [hT, maximalBettiTransfer_spec]

theorem transferableSubspace_eq_top
    (htotal : transferObstruction A K n = 0) :
    transferableSubspace A K n = ⊤ := by
  rw [transferableSubspace, htotal]
  exact LinearMap.ker_zero

theorem targetAmbiguity_eq_bot
    (hright : Function.Injective (rightCohomologyPullback A K n)) :
    targetAmbiguity A K n = ⊥ := by
  exact LinearMap.ker_eq_bot.mpr hright

#check maximalBettiTransfer
#check maximalBettiTransfer_spec
#check quotient_eq_maximalTransfer_iff_related
#check maximalBettiTransfer_unique

end GSTClassicalHodgeStrictCorrespondenceMaximalBettiTransfer
