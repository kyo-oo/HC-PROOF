import GSTClassicalHodgeStrictCorrespondenceBiTransferGeometry
import GSTClassicalHodgeStrictCorrespondenceTransferRigidity

/-!
# GST CLASSICAL HODGE — BI-TRANSFER RIGIDITY

A genuine right finite-chain transfer for `K` makes the right projection
Betti-faithful.  The actual factor-swap transpose converts its right transfer
into the original left transfer.  Therefore a bivariant transfer packet forces
BOTH projections to be split at chain level and injective after rational Betti
pullback.

This is the exact full-degree geometric regime in which same-degree
correspondence push-pull behaves like a finite multisection in both directions.
It is strictly stronger than scheme-theoretic bi-finiteness alone.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicTopology

namespace GSTClassicalHodgeStrictCorrespondenceBiTransferRigidity

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTClassicalHodgeSchemeFiniteCorrespondenceFirewall
open GSTClassicalHodgeStrictCorrespondenceAnalyticSpan
open GSTClassicalHodgeStrictCorrespondenceChainTransfer
open GSTClassicalHodgeStrictCorrespondenceChainTranspose
open GSTClassicalHodgeStrictCorrespondenceBiTransferGeometry
open GSTClassicalHodgeStrictCorrespondenceTransferRigidity

variable {V : SmoothProjectiveComplexScheme}
variable (A : AnalytificationData V)
variable (K : SchemeBiFiniteClosedCorrespondence V)

/-- Normalize a left finite-chain transfer. -/
noncomputable def normalizedLeftChainTransfer
    (T : LeftFiniteChainTransfer A K) :
    rationalSingularChains A ⟶ carrierSingularChains A K :=
  T.degree⁻¹ • T.transfer

/-- A left finite transfer makes the left projection a split epimorphism on
singular chains. -/
theorem normalizedLeftChainTransfer_left
    (T : LeftFiniteChainTransfer A K) :
    normalizedLeftChainTransfer A K T ≫ leftChainMap A K =
      𝟙 (rationalSingularChains A) := by
  rw [normalizedLeftChainTransfer]
  simp only [Preadditive.smul_comp]
  rw [T.transfer_left]
  ext m x
  simp [T.degree_ne_zero]

/-- Instead of re-dualizing the left transfer from scratch, use its geometric
origin from the transpose.  The transpose right pullback is Betti-injective in
all degrees, and the genuine carrier swap identifies it with original left
pullback.  This theorem records the resulting original-left faithfulness. -/
theorem BiFiniteChainTransfer.leftPullback_injective_all
    (T : BiFiniteChainTransfer A K) :
    ∀ n : Nat, Function.Injective (leftCohomologyPullback A K n) := by
  intro n alpha beta hab
  -- Transport the equality through the genuine transpose carrier.  The
  -- transpose packet has a right finite transfer and hence injective right
  -- pullback.  The chain-level swap identifies transpose-right with
  -- original-left; GLM may normalize the induced cohomology transport.
  have htr :
      Function.Injective (rightCohomologyPullback A K.transpose n) :=
    T.transpose.rightCohomologyPullback_injective_all A K.transpose n
  -- The exact equality of pullbacks after the carrier swap is a consequence
  -- of `transposeChain_right`; expose it as a local map identity through the
  -- cochain/homology functor.
  let F :=
    ((CategoryTheory.linearYoneda ℚ (ModuleCat ℚ)).obj rationalCoefficient).rightOp
      |>.mapHomologicalComplex (ComplexShape.down ℕ)
  let swapCochain :
      carrierSingularCochains A K.transpose ⟶ carrierSingularCochains A K :=
    (F.map (transposeChainIso A K).hom).unop
  let swapCoh :
      CarrierCohomology A K.transpose n →ₗ[ℚ] CarrierCohomology A K n :=
    (HomologicalComplex.homologyMap swapCochain n).hom
  have hswap :
      swapCoh.comp (rightCohomologyPullback A K.transpose n) =
        leftCohomologyPullback A K n := by
    ext a
    simp [swapCoh, swapCochain, rightCohomologyPullback,
      rightCohomologyPullbackObj, rightCochainPullback,
      leftCohomologyPullback, leftCohomologyPullbackObj,
      leftCochainPullback, transposeChain_right]
  have hsalpha := LinearMap.congr_fun hswap alpha
  have hsbeta := LinearMap.congr_fun hswap beta
  -- `swapCoh` comes from an isomorphism, hence is injective.  It is enough to
  -- compare before transport; the transpose right-pullback injectivity then
  -- returns alpha = beta.
  have hswapIso : Function.Injective swapCoh := by
    let swapInvCochain :
        carrierSingularCochains A K ⟶ carrierSingularCochains A K.transpose :=
      (F.map (transposeChainIso A K).inv).unop
    let swapInvCoh :
        CarrierCohomology A K n →ₗ[ℚ] CarrierCohomology A K.transpose n :=
      (HomologicalComplex.homologyMap swapInvCochain n).hom
    intro u v huv
    have := congrArg swapInvCoh huv
    simpa [swapCoh, swapInvCoh, swapCochain, swapInvCochain] using this
  apply htr
  apply hswapIso
  rw [hsalpha, hsbeta]
  exact hab

/-- A genuine bi-transfer is Betti-faithful on both actual projection maps. -/
theorem BiFiniteChainTransfer.bettiFaithful_both
    (T : BiFiniteChainTransfer A K) :
    (∀ n : Nat, Function.Injective (rightCohomologyPullback A K n)) ∧
    (∀ n : Nat, Function.Injective (leftCohomologyPullback A K n)) := by
  constructor
  · exact T.forward.rightCohomologyPullback_injective_all A K
  · exact T.leftPullback_injective_all A K

/-- **FULL-DEGREE STRICT CORRESPONDENCE.**
A strict scheme-bi-finite carrier together with genuine finite chain transfer
geometry in both orientations.  This is the correct same-degree push-pull
carrier; arbitrary lower-dimensional finite closed correspondences belong to
the graded-kernel theory instead. -/
structure FullDegreeStrictCorrespondence
    (V : SmoothProjectiveComplexScheme)
    (A : AnalytificationData V) where
  correspondence : SchemeBiFiniteClosedCorrespondence V
  transfer : BiFiniteChainTransfer A correspondence

namespace FullDegreeStrictCorrespondence

/-- Both projection pullbacks of a full-degree strict correspondence are
faithful on every rational Betti degree. -/
theorem bettiFaithful_both
    (R : FullDegreeStrictCorrespondence V A) :
    (∀ n : Nat,
      Function.Injective
        (rightCohomologyPullback A R.correspondence n)) ∧
    (∀ n : Nat,
      Function.Injective
        (leftCohomologyPullback A R.correspondence n)) :=
  R.transfer.bettiFaithful_both A R.correspondence

end FullDegreeStrictCorrespondence

#check normalizedLeftChainTransfer
#check normalizedLeftChainTransfer_left
#check BiFiniteChainTransfer.leftPullback_injective_all
#check BiFiniteChainTransfer.bettiFaithful_both
#check FullDegreeStrictCorrespondence
#check FullDegreeStrictCorrespondence.bettiFaithful_both

end GSTClassicalHodgeStrictCorrespondenceBiTransferRigidity
