import GSTClassicalHodgeStrictCorrespondenceAnalyticTranspose

/-!
# GST CLASSICAL HODGE — STRICT CORRESPONDENCE CHAIN TRANSPOSE

The genuine algebraic factor swap is lifted to an isomorphism of the intrinsic
analytic carriers and then through Mathlib's singular-chain functor.  This
fixes the transpose orientation before any trace/Gysin datum is introduced.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicTopology

namespace GSTClassicalHodgeStrictCorrespondenceChainTranspose

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTClassicalHodgeSchemeFiniteCorrespondenceFirewall
open GSTClassicalHodgeStrictCorrespondenceAnalyticSpan
open GSTClassicalHodgeStrictCorrespondenceAnalyticTranspose

variable {V : SmoothProjectiveComplexScheme}
variable (A : AnalytificationData V)

noncomputable def analyticCarrierSwapHom
    (K : SchemeBiFiniteClosedCorrespondence V) :
    analyticCarrier A K ⟶ analyticCarrier A K.transpose :=
  ConcreteCategory.ofHom (C := TopCat) ⟨
    (fun q => ⟨(q.1.2, q.1.1),
      (mem_analyticLocus_transpose_iff A K (q.1.2, q.1.1)).2 q.2⟩),
    by
      exact Continuous.subtype_mk
        ((continuous_snd.comp continuous_subtype_val).prod_mk
          (continuous_fst.comp continuous_subtype_val)) _⟩

noncomputable def analyticCarrierSwapInv
    (K : SchemeBiFiniteClosedCorrespondence V) :
    analyticCarrier A K.transpose ⟶ analyticCarrier A K :=
  ConcreteCategory.ofHom (C := TopCat) ⟨
    (fun q => ⟨(q.1.2, q.1.1),
      (mem_analyticLocus_transpose_iff A K q.1).1 q.2⟩),
    by
      exact Continuous.subtype_mk
        ((continuous_snd.comp continuous_subtype_val).prod_mk
          (continuous_fst.comp continuous_subtype_val)) _⟩

noncomputable def analyticCarrierTransposeIso
    (K : SchemeBiFiniteClosedCorrespondence V) :
    analyticCarrier A K ≅ analyticCarrier A K.transpose where
  hom := analyticCarrierSwapHom A K
  inv := analyticCarrierSwapInv A K
  hom_inv_id := by ext q; apply Subtype.ext; rfl
  inv_hom_id := by ext q; apply Subtype.ext; rfl

@[simp]
theorem swapHom_left
    (K : SchemeBiFiniteClosedCorrespondence V) :
    analyticCarrierSwapHom A K ≫ analyticLeft A K.transpose =
      analyticRight A K := by
  ext q
  rfl

@[simp]
theorem swapHom_right
    (K : SchemeBiFiniteClosedCorrespondence V) :
    analyticCarrierSwapHom A K ≫ analyticRight A K.transpose =
      analyticLeft A K := by
  ext q
  rfl

noncomputable def transposeChainIso
    (K : SchemeBiFiniteClosedCorrespondence V) :
    carrierSingularChains A K ≅ carrierSingularChains A K.transpose :=
  ((singularChainComplexFunctor (ModuleCat ℚ)).obj rationalCoefficient).mapIso
    (analyticCarrierTransposeIso A K)

/-- **CHAIN-LEVEL LEFT/RIGHT TRANSPOSE LAW.** -/
theorem transposeChain_left
    (K : SchemeBiFiniteClosedCorrespondence V) :
    (transposeChainIso A K).hom ≫ leftChainMap A K.transpose =
      rightChainMap A K := by
  let F := (singularChainComplexFunctor (ModuleCat ℚ)).obj rationalCoefficient
  change F.map (analyticCarrierSwapHom A K) ≫ F.map (analyticLeft A K.transpose) =
    F.map (analyticRight A K)
  rw [← F.map_comp, swapHom_left A K]

theorem transposeChain_right
    (K : SchemeBiFiniteClosedCorrespondence V) :
    (transposeChainIso A K).hom ≫ rightChainMap A K.transpose =
      leftChainMap A K := by
  let F := (singularChainComplexFunctor (ModuleCat ℚ)).obj rationalCoefficient
  change F.map (analyticCarrierSwapHom A K) ≫ F.map (analyticRight A K.transpose) =
    F.map (analyticLeft A K)
  rw [← F.map_comp, swapHom_right A K]

#check analyticCarrierTransposeIso
#check transposeChainIso
#check transposeChain_left
#check transposeChain_right

end GSTClassicalHodgeStrictCorrespondenceChainTranspose
