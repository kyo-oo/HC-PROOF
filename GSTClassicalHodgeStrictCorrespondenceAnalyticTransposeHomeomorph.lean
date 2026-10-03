import GSTClassicalHodgeStrictCorrespondenceAnalyticTranspose

/-!
# GST CLASSICAL HODGE — ANALYTIC TRANSPOSE HOMEOMORPHISM

The set-level transpose law upgrades canonically to a homeomorphism of the
intrinsic analytic carriers.  It is literally coordinate swap on the subspace
of `X^an × X^an` cut out by the strict algebraic correspondence.

This is the missing topological bridge needed to transport singular-chain and
cochain constructions through the genuine algebraic factor-swap transpose.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicGeometry

namespace GSTClassicalHodgeStrictCorrespondenceAnalyticTransposeHomeomorph

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTClassicalHodgeSchemeFiniteCorrespondenceFirewall
open GSTClassicalHodgeStrictCorrespondenceAnalyticSpan
open GSTClassicalHodgeStrictCorrespondenceAnalyticTranspose

variable {V : SmoothProjectiveComplexScheme}
variable (A : AnalytificationData V)

/-- Coordinate swap sends every point of the transpose analytic carrier to the
corresponding point of the original analytic carrier. -/
noncomputable def transposeCarrierSwap
    (K : SchemeBiFiniteClosedCorrespondence V) :
    analyticCarrier A K.transpose → analyticCarrier A K :=
  fun q =>
    ⟨(q.1.2, q.1.1),
      (mem_analyticLocus_transpose_iff A K q.1).1 q.2⟩

/-- The same coordinate swap runs backwards. -/
noncomputable def transposeCarrierUnswap
    (K : SchemeBiFiniteClosedCorrespondence V) :
    analyticCarrier A K → analyticCarrier A K.transpose :=
  fun q =>
    ⟨(q.1.2, q.1.1),
      (mem_analyticLocus_transpose_iff A K (q.1.2, q.1.1)).2
        (by simpa using q.2)⟩

/-- The genuine transpose carriers are homeomorphic by coordinate swap. -/
noncomputable def transposeCarrierHomeomorph
    (K : SchemeBiFiniteClosedCorrespondence V) :
    analyticCarrier A K.transpose ≃ₜ analyticCarrier A K where
  toFun := transposeCarrierSwap A K
  invFun := transposeCarrierUnswap A K
  left_inv := by
    intro q
    apply Subtype.ext
    rfl
  right_inv := by
    intro q
    apply Subtype.ext
    rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_snd.comp continuous_subtype_val).prod_mk
      (continuous_fst.comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (continuous_snd.comp continuous_subtype_val).prod_mk
      (continuous_fst.comp continuous_subtype_val)

@[simp]
theorem transposeCarrierHomeomorph_apply_val
    (K : SchemeBiFiniteClosedCorrespondence V)
    (q : analyticCarrier A K.transpose) :
    (transposeCarrierHomeomorph A K q).1 = (q.1.2, q.1.1) := rfl

/-- After the carrier homeomorphism, the left projection of the transpose is
literally the original right projection. -/
theorem transposeCarrier_left_eq_right
    (K : SchemeBiFiniteClosedCorrespondence V)
    (q : analyticCarrier A K.transpose) :
    analyticLeft A K.transpose q =
      analyticRight A K (transposeCarrierHomeomorph A K q) := rfl

/-- Likewise the right projection of the transpose becomes the original left
projection. -/
theorem transposeCarrier_right_eq_left
    (K : SchemeBiFiniteClosedCorrespondence V)
    (q : analyticCarrier A K.transpose) :
    analyticRight A K.transpose q =
      analyticLeft A K (transposeCarrierHomeomorph A K q) := rfl

#check transposeCarrierSwap
#check transposeCarrierUnswap
#check transposeCarrierHomeomorph
#check transposeCarrier_left_eq_right
#check transposeCarrier_right_eq_left

#print axioms transposeCarrierHomeomorph
#print axioms transposeCarrier_left_eq_right
#print axioms transposeCarrier_right_eq_left

end GSTClassicalHodgeStrictCorrespondenceAnalyticTransposeHomeomorph
