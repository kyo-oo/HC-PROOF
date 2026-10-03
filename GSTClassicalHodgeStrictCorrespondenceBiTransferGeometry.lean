import GSTClassicalHodgeStrictCorrespondenceChainTransfer
import GSTClassicalHodgeStrictCorrespondenceChainTranspose

/-!
# GST CLASSICAL HODGE — BIVARIANT TRANSFER GEOMETRY

A factor-swap transpose is not a second unrelated correspondence.  Once the
actual analytic carrier swap has been lifted to singular chains, a right
finite-chain transfer for `K^t` canonically becomes a left finite-chain
transfer for `K`.

This removes one independent orientation choice from the transfer packet and
makes the forward/transpose relationship genuinely geometric.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicTopology

namespace GSTClassicalHodgeStrictCorrespondenceBiTransferGeometry

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTClassicalHodgeSchemeFiniteCorrespondenceFirewall
open GSTClassicalHodgeStrictCorrespondenceAnalyticSpan
open GSTClassicalHodgeStrictCorrespondenceChainTransfer
open GSTClassicalHodgeStrictCorrespondenceChainTranspose

variable {V : SmoothProjectiveComplexScheme}
variable (A : AnalytificationData V)
variable (K : SchemeBiFiniteClosedCorrespondence V)

/-- Finite chain transfer normalized against the LEFT projection. -/
structure LeftFiniteChainTransfer where
  transfer : rationalSingularChains A ⟶ carrierSingularChains A K
  degree : ℚ
  degree_ne_zero : degree ≠ 0
  transfer_left :
    transfer ≫ leftChainMap A K = degree • 𝟙 (rationalSingularChains A)

/-- The inverse carrier swap followed by the original left projection is the
right projection of the genuine transpose. -/
theorem transposeChainIso_inv_left
    (K : SchemeBiFiniteClosedCorrespondence V) :
    (transposeChainIso A K).inv ≫ leftChainMap A K =
      rightChainMap A K.transpose := by
  have h := congrArg
    (fun f => (transposeChainIso A K).inv ≫ f)
    (transposeChain_right A K)
  simpa [Category.assoc] using h.symm

/-- Dually, inverse swap followed by the original right projection is the left
projection of the transpose. -/
theorem transposeChainIso_inv_right
    (K : SchemeBiFiniteClosedCorrespondence V) :
    (transposeChainIso A K).inv ≫ rightChainMap A K =
      leftChainMap A K.transpose := by
  have h := congrArg
    (fun f => (transposeChainIso A K).inv ≫ f)
    (transposeChain_left A K)
  simpa [Category.assoc] using h.symm

/-- **TRANSPOSE RIGHT TRANSFER -> ORIGINAL LEFT TRANSFER.** -/
noncomputable def leftTransferOfTransposeRight
    (T : RightFiniteChainTransfer A K.transpose) :
    LeftFiniteChainTransfer A K where
  transfer := T.transfer ≫ (transposeChainIso A K).inv
  degree := T.degree
  degree_ne_zero := T.degree_ne_zero
  transfer_left := by
    rw [Category.assoc, transposeChainIso_inv_left A K]
    exact T.transfer_right

/-- The construction uses literally the same finite degree. -/
@[simp]
theorem leftTransferOfTransposeRight_degree
    (T : RightFiniteChainTransfer A K.transpose) :
    (leftTransferOfTransposeRight A K T).degree = T.degree := rfl

/-- A geometric bi-transfer packet can therefore be read as right and left
transfer data on the SAME strict correspondence. -/
noncomputable def BiFiniteChainTransfer.leftTransfer
    (T : BiFiniteChainTransfer A K) : LeftFiniteChainTransfer A K :=
  leftTransferOfTransposeRight A K T.transpose

/-- Exact left transfer law extracted from the genuine transpose packet. -/
theorem BiFiniteChainTransfer.leftTransfer_left
    (T : BiFiniteChainTransfer A K) :
    T.leftTransfer.transfer ≫ leftChainMap A K =
      T.leftTransfer.degree • 𝟙 (rationalSingularChains A) :=
  T.leftTransfer.transfer_left

/-- Thus a bi-transfer packet supplies finite-degree splittings of BOTH actual
projection chain maps. -/
theorem biTransfer_projection_splittings
    (T : BiFiniteChainTransfer A K) :
    (T.forward.transfer ≫ rightChainMap A K =
      T.forward.degree • 𝟙 (rationalSingularChains A)) ∧
    (T.leftTransfer.transfer ≫ leftChainMap A K =
      T.leftTransfer.degree • 𝟙 (rationalSingularChains A)) :=
  ⟨T.forward.transfer_right, T.leftTransfer.transfer_left⟩

#check LeftFiniteChainTransfer
#check transposeChainIso_inv_left
#check leftTransferOfTransposeRight
#check BiFiniteChainTransfer.leftTransfer
#check biTransfer_projection_splittings

end GSTClassicalHodgeStrictCorrespondenceBiTransferGeometry
