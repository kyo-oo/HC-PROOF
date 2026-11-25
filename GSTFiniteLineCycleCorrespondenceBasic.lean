import Mathlib
import GSTFiniteLineHonestHodgeData
import GSTFiniteLineGeneralMLaw
import GSTFiniteLineAnalytification
/- SPLIT PIECE of GSTFiniteLineCycleCorrespondence.lean (the wave-9-G module-split law: the runner-kill window demands small pieces) -/

/-
Copyright (c) 2026. The HC-PROOF campaign. All rights reserved.

# GATE-L — THE TWO M-CYCLE LETTERS (wave 4-C)

The M-cycle automorphism's graphs as genuine realized closed
correspondences on the honest Hodge data:

* the residue-degree receipt — the M-cycle is an isomorphism, so its
  residue field maps are bijective (the composition roundtrips through
  `residueFieldMap_id`/`residueFieldMap_comp`), and the residue weight is
  one (the green finrank pattern of the finite-point lane);
* the point-action receipt — the M-cycle acts on the generic points by
  `cyclicPred` (the comap of the graded rotation permutes the block
  ideals);
* the two letters `finiteLineCycleLetterOne` (weight one) and
  `finiteLineCycleLetterZero` (weight zero): the graph correspondence of the
  M-cycle endomorphism with the transported sphere-cycle pullback (letter one)/the
  component-iso conjugate of the index shift (letter zero) as the
  cohomological operator, rotating the honest point/component families.

Honesty ledger: every statement is proved unconditionally.  No `sorry`,
no new axioms, no `native_decide`.  The GitHub CI lane
`gst-finite-line-cycle-correspondence.yml` owns the kernel check.
-/

set_option maxHeartbeats 200000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicTopology
open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra
open GSTClassicalHodgeRealizedCorrespondenceKrylovFinale
open GSTClassicalHodgeAnalytificationFunctoriality
open GSTClassicalHodgeFiniteClosedCorrespondence
open GSTClassicalHodgeFiniteClosedCorrespondenceOperator
open GSTClassicalHodgeProjectivePointTransport
open GSTNativeCodimensionCyclePresentation
open GSTSphereUnionComponents
open GSTSphereUnionPointClassGate
open GSTSingularCohomologyMaps
open GSTSphereCycleLegs
open GSTPositiveDimensionalLawLanding
open GSTFiniteLineRing
open GSTFiniteLineWorldCarrier
open GSTFiniteLineOverBase
open GSTFiniteLineGeneralMLaw
open GSTFiniteLinePointAlgebra
open GSTFiniteLineHonestHodgeData
open GSTComponentCohomologyZero
open GSTFiniteLineAnalytification

namespace GSTFiniteLineCycleCorrespondence

/-! ## §0 The M-cycle endomorphism -/

/-- **THE M-CYCLE ENDOMORPHISM** — the M-cycle automorphism as a complex
scheme endomorphism (the over-base square is green). -/
noncomputable def finiteLineCycleEndo (M : ℕ) [NeZero M] :
    ComplexSchemeEndomorphism (finiteLineWorld M) where
  hom := finiteLineCycle M
  over_base := finiteLineCycle_over_base M

/-! ## §1 The residue-degree receipt -/

/-- The map_id transport (the wave-65 carrier's private helper, localized
for this module — private declarations do not export across files). -/
private theorem map_id_of_eq {A σ : Type u} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] {𝒜 : ℕ → σ} [GradedRing 𝒜] {f : 𝒜 →+*ᵍ 𝒜}
    (h : f = GradedRingHom.id 𝒜)
    (hf : HomogeneousIdeal.irrelevant 𝒜 ≤
      HomogeneousIdeal.map f (HomogeneousIdeal.irrelevant 𝒜)) :
    Proj.map f hf = 𝟙 (Proj 𝒜) := by
  subst h
  exact Proj.map_id

/-- The point-level roundtrips of the M-cycle. -/
theorem finiteLineCycleInv_apply (M : ℕ) [NeZero M] (x : finiteLineScheme M) :
    finiteLineCycleInv M (finiteLineCycle M x) = x := by
  have hinv' : finiteLineCycle M ≫ finiteLineCycleInv M = 𝟙 (finiteLineScheme M) := by
    rw [finiteLineCycle, finiteLineCycleInv, ← Proj.map_comp]
    exact map_id_of_eq (lineRotateGraded_comp_inv M) _
  have h := congrArg (fun f => f x) hinv'
  rw [Scheme.Hom.comp_apply] at h
  simpa using h

theorem finiteLineCycle_apply_inv (M : ℕ) [NeZero M] (x : finiteLineScheme M) :
    finiteLineCycle M (finiteLineCycleInv M x) = x := by
  have hinv : finiteLineCycleInv M ≫ finiteLineCycle M = 𝟙 (finiteLineScheme M) := by
    rw [finiteLineCycle, finiteLineCycleInv, ← Proj.map_comp]
    exact map_id_of_eq (lineRotateInvGraded_comp M) _
  have h := congrArg (fun f => f x) hinv
  rw [Scheme.Hom.comp_apply] at h
  simpa using h

/-- The residue field maps of the M-cycle are bijective — the roundtrips
through the Inv-cycle in the pinned residue-field API's CONTRAVariant
direction (`ResidueField.lean`:
`Hom.residueFieldMap f x : κ (f x) ⟶ κ x`): the inverse rides the
point-equality transport `residueFieldCongr` (`residueFieldMap_congr'`
moves the point of the cycle's own map; `residueFieldMap_congr` rewrites
the roundtripped composite through the identity), and the two composite
roundtrips close by `Iso.inv_hom_id`/`Iso.hom_inv_id` at the transported
congruences. -/
theorem finiteLineCycle_residueFieldMap_bijective (M : ℕ) [NeZero M]
    (x : finiteLineScheme M) :
    Function.Bijective
      (Scheme.Hom.residueFieldMap (finiteLineCycle M) x) := by
  have hinv : finiteLineCycleInv M ≫ finiteLineCycle M = 𝟙 (finiteLineScheme M) := by
    rw [finiteLineCycle, finiteLineCycleInv, ← Proj.map_comp]
    exact map_id_of_eq (lineRotateInvGraded_comp M) _
  have hinv' : finiteLineCycle M ≫ finiteLineCycleInv M = 𝟙 (finiteLineScheme M) := by
    rw [finiteLineCycle, finiteLineCycleInv, ← Proj.map_comp]
    exact map_id_of_eq (lineRotateGraded_comp_inv M) _
  have eInv : finiteLineCycleInv M (finiteLineCycle M x) = x :=
    finiteLineCycleInv_apply M x
  -- THE RIGHT-INVERSE EQUATION (surjectivity side): the transported
  -- composite L ≫ φ, where L := (congr eInv).symm.hom ≫ inv.rFM (cyc x).
  have hLφ : ((finiteLineScheme M).residueFieldCongr eInv).symm.hom ≫
      (Scheme.Hom.residueFieldMap (finiteLineCycleInv M) (finiteLineCycle M x) ≫
        Scheme.Hom.residueFieldMap (finiteLineCycle M) x) =
      𝟙 ((finiteLineScheme M).residueField x) := by
    rw [← Scheme.residueFieldMap_comp,
      Scheme.Hom.residueFieldMap_congr hinv' x, Scheme.residueFieldMap_id,
      Category.id_comp]
    exact Iso.inv_hom_id ((finiteLineScheme M).residueFieldCongr eInv)
  -- THE LEFT-INVERSE EQUATION (injectivity side): φ ≫ L.
  have hφL : (Scheme.Hom.residueFieldMap (finiteLineCycle M) x ≫
      ((finiteLineScheme M).residueFieldCongr eInv).symm.hom) ≫
      Scheme.Hom.residueFieldMap (finiteLineCycleInv M) (finiteLineCycle M x) =
      𝟙 ((finiteLineScheme M).residueField (finiteLineCycle M x)) := by
    rw [Scheme.residueFieldCongr_symm,
      Scheme.Hom.residueFieldMap_congr' eInv.symm, Category.assoc,
      ← Scheme.residueFieldMap_comp,
      Scheme.Hom.residueFieldMap_congr hinv (finiteLineCycle M x),
      Scheme.residueFieldMap_id, Category.id_comp]
    exact Iso.hom_inv_id
      ((finiteLineScheme M).residueFieldCongr
        (congrArg (finiteLineCycle M) eInv.symm))
  constructor
  · intro a b hab
    have ha : Scheme.Hom.residueFieldMap (finiteLineCycleInv M)
        (finiteLineCycle M x) (((finiteLineScheme M).residueFieldCongr eInv).symm.hom
          (Scheme.Hom.residueFieldMap (finiteLineCycle M) x a)) = a := by
      simpa using DFunLike.congr_fun hφL a
    have hb : Scheme.Hom.residueFieldMap (finiteLineCycleInv M)
        (finiteLineCycle M x) (((finiteLineScheme M).residueFieldCongr eInv).symm.hom
          (Scheme.Hom.residueFieldMap (finiteLineCycle M) x b)) = b := by
      simpa using DFunLike.congr_fun hφL b
    calc a = Scheme.Hom.residueFieldMap (finiteLineCycleInv M)
          (finiteLineCycle M x) (((finiteLineScheme M).residueFieldCongr eInv).symm.hom
            (Scheme.Hom.residueFieldMap (finiteLineCycle M) x a)) := ha.symm
      _ = Scheme.Hom.residueFieldMap (finiteLineCycleInv M)
          (finiteLineCycle M x) (((finiteLineScheme M).residueFieldCongr eInv).symm.hom
            (Scheme.Hom.residueFieldMap (finiteLineCycle M) x b)) := by
          rw [hab]
      _ = b := hb
  · intro w
    refine ⟨Scheme.Hom.residueFieldMap (finiteLineCycleInv M)
        (finiteLineCycle M x) (((finiteLineScheme M).residueFieldCongr eInv).symm.hom w),
      ?_⟩
    simpa using DFunLike.congr_fun hLφ w

/-- **THE M-CYCLE'S RESIDUE WEIGHT IS ONE** — the isomorphism's residue
field maps are bijective, so the induced residue extension has rank one
(the green finrank pattern of the finite-point lane). -/
theorem finiteLineCycle_pointResidueWeight (M : ℕ) [NeZero M]
    (x : finiteLineScheme M) :
    pointResidueWeight (finiteLineCycle M) x = 1 := by
  have hsurj : Function.Surjective (Scheme.Hom.residueFieldMap
      (finiteLineCycle M) x) :=
    (finiteLineCycle_residueFieldMap_bijective M x).2
  letI : Algebra
      ((finiteLineScheme M).residueField (finiteLineCycle M x))
      ((finiteLineScheme M).residueField x) :=
    (Scheme.Hom.residueFieldMap (finiteLineCycle M) x).hom.toAlgebra
  show (Scheme.Hom.residueDegree (finiteLineCycle M) x : ℚ) = 1
  rw [Scheme.Hom.residueDegree]
  have : (Module.finrank ((finiteLineScheme M).residueField (finiteLineCycle M x))
      ((finiteLineScheme M).residueField x)) = 1 := by
    refine (finrank_eq_one_iff_of_nonzero'
      (1 : (finiteLineScheme M).residueField x) one_ne_zero).mpr ?_
    intro w
    obtain ⟨a, ha⟩ := hsurj w
    refine ⟨a, ?_⟩
    calc a • (1 : (finiteLineScheme M).residueField x)
        = Scheme.Hom.residueFieldMap (finiteLineCycle M) x a := by
          rw [Algebra.smul_def, mul_one]
          rfl
      _ = w := ha
  rw [this]
  rfl



end GSTFiniteLineCycleCorrespondence

end -- noncomputable section
