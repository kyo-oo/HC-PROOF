import Mathlib
import GSTFiniteLineHonestHodgeData
import GSTFiniteLineGeneralMLaw
import GSTFiniteLineAnalytification

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
* the two letters `finiteLineCycleRot₁` (weight one) and
  `finiteLineCycleRot₀` (weight zero): the graph correspondence of the
  M-cycle endomorphism with the transported sphere-cycle pullback as the
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
    have := finiteLineCycle_isIso M
    rw [finiteLineCycle, finiteLineCycleInv, ← Proj.map_comp]
    exact map_id_of_eq (lineRotateGraded_comp_inv M) _
  have h := congrArg (fun f => f x) hinv'
  rw [Scheme.Hom.comp_apply] at h
  simpa using h

theorem finiteLineCycle_apply_inv (M : ℕ) [NeZero M] (x : finiteLineScheme M) :
    finiteLineCycle M (finiteLineCycleInv M x) = x := by
  have hinv : finiteLineCycleInv M ≫ finiteLineCycle M = 𝟙 (finiteLineScheme M) := by
    have := finiteLineCycle_isIso M
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
    have := finiteLineCycle_isIso M
    rw [finiteLineCycle, finiteLineCycleInv, ← Proj.map_comp]
    exact map_id_of_eq (lineRotateInvGraded_comp M) _
  have hinv' : finiteLineCycle M ≫ finiteLineCycleInv M = 𝟙 (finiteLineScheme M) := by
    have := finiteLineCycle_isIso M
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


/-! ## §2 The point-action receipts (GATE-L waves 6-C: the ideal-level §2a + the order-level §2b, spliced from repairs/wave6_sec2a.lean and repairs/wave6_sec2b.lean) -/

/-! ## §2a The point-action lemmas (the ideal-level battle) -/

/-- **THE ONE-POINT BLOCK ARITHMETIC** — rotating the even variable index of
block `i` lands in block `cyclicSucc i`: `(blockRot M (blockVarLeft M i)).val / 2
= (cyclicSucc M i).val`.  This is the only new arithmetic in §2a: the
no-wrap/wrap case split (`2*i+2 < 2*M` vs `2*M ≤ 2*i+2`; in the wrap case
`2*i+2 = 2*M` exactly since `i.val < M`, so both sides are `0`), everything
else rides the green `blockRot`/`blockVarLeft` corpus lemmas. -/
private theorem blockRot_blockVarLeft (M : ℕ) [NeZero M] (i : Fin M) :
    (blockRot M (blockVarLeft M i)).val / 2 = (cyclicSucc M i).val := by
  have hi : i.val < M := i.isLt
  show (2 * i.val + 2) % (2 * M) / 2 = (i.val + 1) % M
  rcases Nat.lt_or_ge (2 * i.val + 2) (2 * M) with h | h
  · have hlt : i.val + 1 < M := by omega
    rw [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt hlt]
    omega
  · have heq : 2 * i.val + 2 = 2 * M := by omega
    have hiM : i.val + 1 = M := by omega
    rw [heq, hiM, Nat.mod_self, Nat.mod_self]

/-- **THE SPAN RECEIPT (+2 SHIFT)** — every generator of the i-th generic
ideal maps, under the graded rotation, into the `cyclicSucc i`-th one: the
variable `X_b` (block `b/2 ≠ i`) rotates to `X_{blockRot b}` whose block is
`(b/2 + 1) mod M ≠ cyclicSucc i`.  This is the ≥-direction of the block-ideal
permutation, stated so that it can be re-indexed by either `cyclicPred` (for
L2) or used directly (for the Inv-mirror's ≤-direction). -/
private theorem lineGenericIdeal_le_comap_rotate (M : ℕ) [NeZero M] (i : Fin M) :
    lineGenericIdeal M i ≤ (lineGenericIdeal M (cyclicSucc M i)).comap
      (lineRotateGraded M) := by
  rw [lineGenericIdeal, Ideal.span_le]
  rintro _ ⟨b, rfl⟩
  show lineQuotientMap M (MvPolynomial.X (b : Fin (2 * M))) ∈
      Ideal.comap (lineRotateGraded M) (lineGenericIdeal M (cyclicSucc M i))
  rw [Ideal.mem_comap]
  show lineRotateHom M (lineQuotientMap M (MvPolynomial.X (b : Fin (2 * M)))) ∈
      lineGenericIdeal M (cyclicSucc M i)
  rw [lineRotateHom_mk, lineRename_X]
  refine mem_lineGenericIdeal M (cyclicSucc M i) ?_
  intro hcon
  have h1 : (blockRot M (b : Fin (2 * M))).val / 2
      = (blockRot M (blockVarLeft M i)).val / 2 := by
    rw [blockRot_blockVarLeft M i]
    exact hcon
  exact b.2 ((blockRot_sameBlock M (b : Fin (2 * M)) (blockVarLeft M i)).mp h1).trans
    (blockVarLeft_block M i)

/-- **THE SPAN RECEIPT (−2 SHIFT)** — the Inv-mirror: every generator of the
i-th generic ideal maps, under the inverse graded rotation, into the
`cyclicPred i`-th one (the `blockRot.symm` index shift is `−1` at the block
level, so the outside-block span pulls back to the predecessor's).  Route
mirrors `lineGenericIdeal_le_comap_rotate` through the carrier's Inv descent
(`lineRotateInvHom_mk` + the `renameEquiv`/`rename_X` pair) and folds the
symmetric pair by `Equiv.symm_apply_apply` before the block comparison. -/
private theorem lineGenericIdeal_le_comap_rotateInv (M : ℕ) [NeZero M] (i : Fin M) :
    lineGenericIdeal M i ≤ (lineGenericIdeal M (cyclicPred M i)).comap
      (lineRotateInvGraded M) := by
  rw [lineGenericIdeal, Ideal.span_le]
  rintro _ ⟨b, rfl⟩
  show lineQuotientMap M (MvPolynomial.X (b : Fin (2 * M))) ∈
      Ideal.comap (lineRotateInvGraded M) (lineGenericIdeal M (cyclicPred M i))
  rw [Ideal.mem_comap]
  show lineRotateInvHom M (lineQuotientMap M (MvPolynomial.X (b : Fin (2 * M)))) ∈
      lineGenericIdeal M (cyclicPred M i)
  rw [lineRotateInvHom_mk, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X]
  refine mem_lineGenericIdeal M (cyclicPred M i) ?_
  intro hcon
  have hF : (blockRot M (blockVarLeft M (cyclicPred M i))).val / 2 = i.val := by
    have h := blockRot_blockVarLeft M (cyclicPred M i)
    rw [cyclicSucc_cyclicPred M i] at h
    exact h
  have hQ : ((blockRot M).symm (b : Fin (2 * M))).val / 2
      = (blockVarLeft M (cyclicPred M i)).val / 2 :=
    hcon.trans (blockVarLeft_block M (cyclicPred M i)).symm
  have hP := (blockRot_sameBlock M ((blockRot M).symm (b : Fin (2 * M)))
    (blockVarLeft M (cyclicPred M i))).mpr hQ
  rw [Equiv.apply_symm_apply (blockRot M) (b : Fin (2 * M))] at hP
  exact b.2 (hP.trans hF)

/-- **L1 — THE CYCLE'S POINT ACTION AT THE IDEAL LEVEL.**  Applying the
M-cycle automorphism to a point takes the point's homogeneous ideal to its
comap under the graded rotation: `finiteLineCycle M` is `Proj.map
(lineRotateGraded M)` (carrier §4), and `Proj.map`'s underlying point
function is the pin's `ProjectiveSpectrum.comapFun`
(Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Functor.lean:34-37), whose
first field is exactly `p.1.comap f`.  The whole equation is definitionally
the coercion chain `coe f := f.base` (Scheme.lean:108-109) →
`sheafedSpaceMap`'s `TopCat.ofHom (comap f hf)` base (Functor.lean:100-104) →
`comap`'s `toFun` (Functor.lean:40-44) → `comapFun` — the same chain the pin
closes by `rfl` at `map_preimage_basicOpen` (Functor.lean:160-161) — so the
proof is the show-bridge `rfl` at default transparency (the
`finiteLineCycle` δ-unfolding is pre-empted by restating the goal at
`Proj.map`, keeping the defeq burden inside the single `rfl` check). -/
theorem finiteLineCycle_apply_ideal (M : ℕ) [NeZero M] (x : finiteLineScheme M) :
    ((finiteLineCycle M) x).asHomogeneousIdeal = x.asHomogeneousIdeal.comap
      (lineRotateGraded M) :=
  show ((Proj.map (lineRotateGraded M) (lineRotate_irrelevant_le M)) x).asHomogeneousIdeal
      = x.asHomogeneousIdeal.comap (lineRotateGraded M) from rfl

/-- **L1's INV-MIRROR** — the same ideal-level receipt for the inverse cycle
(`finiteLineCycleInv` is `Proj.map` of the inverse graded rotation, carrier
§4 l. 520-522).  Consumed by `finiteLineCycle_genericPoint_inv` below. -/
private theorem finiteLineCycleInv_apply_ideal (M : ℕ) [NeZero M]
    (x : finiteLineScheme M) :
    ((finiteLineCycleInv M) x).asHomogeneousIdeal = x.asHomogeneousIdeal.comap
      (lineRotateInvGraded M) :=
  show ((Proj.map (lineRotateInvGraded M) (lineRotate_inv_irrelevant_le M)) x).asHomogeneousIdeal
      = x.asHomogeneousIdeal.comap (lineRotateInvGraded M) from rfl

/-- **L2 — THE BLOCK-IDEAL PERMUTATION.**  The comap of the j-th generic
homogeneous ideal under the graded rotation is the generic homogeneous ideal
of the predecessor block: the rotation's variable action `X_b ↦ X_{blockRot
b}` (the +2 index shift, one block up) pulls the outside-block-j span back
to the outside-block-(cyclicPred j) span.  Both inclusions: ≥ is the span
receipt `lineGenericIdeal_le_comap_rotate` re-indexed by `cyclicPred j`
(`cyclicSucc (cyclicPred j) = j`), ≤ is elementwise — a member `y` (with
`f y` in the j-th ideal) is `g (f y)` by the graded roundtrip, and the −2
span receipt maps `f y`'s membership into the predecessor ideal. -/
theorem lineRotate_comap_genericIdeal (M : ℕ) [NeZero M] (j : Fin M) :
    (lineGenericHomogeneousIdeal M j).comap (lineRotateGraded M) =
      lineGenericHomogeneousIdeal M (cyclicPred M j) := by
  refine HomogeneousIdeal.ext ?_
  rw [HomogeneousIdeal.toIdeal_comap, lineGenericHomogeneousIdeal_toIdeal,
    lineGenericHomogeneousIdeal_toIdeal]
  apply le_antisymm
  · intro y hy
    rw [Ideal.mem_comap] at hy
    have hround : lineRotateInvGraded M (lineRotateGraded M y) = y := by
      rw [← GradedRingHom.comp_apply, lineRotateInvGraded_comp,
        GradedRingHom.id_apply]
    rw [← hround]
    exact Ideal.mem_comap.mp (lineGenericIdeal_le_comap_rotateInv M j hy)
  · have h := lineGenericIdeal_le_comap_rotate M (cyclicPred M j)
    rw [cyclicSucc_cyclicPred M j] at h
    exact h

/-- **L2's INV-MIRROR** — the comap of the j-th generic homogeneous ideal
under the inverse graded rotation (the −2 index shift) is the generic
homogeneous ideal of the successor block.  The two inclusions are the
mirrors of L2's (the roundtrip now rides `lineRotateGraded_comp_inv`, and
the re-indexing rides `cyclicPred (cyclicSucc j) = j`).  Consumed by
`finiteLineCycle_genericPoint_inv` below. -/
private theorem lineRotateInv_comap_genericIdeal (M : ℕ) [NeZero M] (j : Fin M) :
    (lineGenericHomogeneousIdeal M j).comap (lineRotateInvGraded M) =
      lineGenericHomogeneousIdeal M (cyclicSucc M j) := by
  refine HomogeneousIdeal.ext ?_
  rw [HomogeneousIdeal.toIdeal_comap, lineGenericHomogeneousIdeal_toIdeal,
    lineGenericHomogeneousIdeal_toIdeal]
  apply le_antisymm
  · intro y hy
    rw [Ideal.mem_comap] at hy
    have hround : lineRotateGraded M (lineRotateInvGraded M y) = y := by
      rw [← GradedRingHom.comp_apply, lineRotateGraded_comp_inv,
        GradedRingHom.id_apply]
    rw [← hround]
    exact Ideal.mem_comap.mp (lineGenericIdeal_le_comap_rotate M j hy)
  · have h := lineGenericIdeal_le_comap_rotateInv M (cyclicSucc M j)
    rw [cyclicPred_cyclicSucc M j] at h
    exact h

/-- **L3 — THE CYCLE ACTS ON THE GENERIC POINTS BY THE CYCLIC
PREDECESSOR.**  The point-action receipt: the cycle carries the j-th generic
point to the `cyclicPred j`-th one.  Route: the ideal equality implies the
point equality (`projectiveSpectrum_ext`,
GSTFiniteLinePointAlgebra.lean:789-797), and the ideal equality is L1
instantiated at `lineGenericPoint M j` composed with L2 — the composition is
term-mode `Eq.trans` (the middle types close by the definitional field
`lineGenericPoint`'s `asHomogeneousIdeal := lineGenericHomogeneousIdeal M j`,
so no re-elaborated rw atom ever touches the `.X`-typed goal). -/
theorem finiteLineCycle_genericPoint (M : ℕ) [NeZero M] (j : Fin M) :
    finiteLineCycle M (lineGenericPoint M j) = lineGenericPoint M (cyclicPred M j) := by
  have h1 := finiteLineCycle_apply_ideal M (lineGenericPoint M j)
  have h2 := lineRotate_comap_genericIdeal M j
  refine projectiveSpectrum_ext ?_
  exact h1.trans h2

/-- **L3's INV-MIRROR** — the Inv-cycle carries the j-th generic point to the
`cyclicSucc j`-th one (the same route through `finiteLineCycleInv` /
`lineRotateInvGraded`, the carrier's inverse machinery at §4 l. 415-425,
520-522). -/
theorem finiteLineCycle_genericPoint_inv (M : ℕ) [NeZero M] (j : Fin M) :
    finiteLineCycleInv M (lineGenericPoint M j) = lineGenericPoint M (cyclicSucc M j) := by
  have h1 := finiteLineCycleInv_apply_ideal M (lineGenericPoint M j)
  have h2 := lineRotateInv_comap_genericIdeal M j
  refine projectiveSpectrum_ext ?_
  exact h1.trans h2

/-! ## §2b The order-level lemmas

The M-cycle is an order-automorphism of the honest prime lattice: monotone
(L4), reflecting (the comap-inverse), strictly monotone, and coheight-preserving
(L5); and it acts on the component index by the cyclic predecessor (L6). -/

attribute [local instance] specializationOrder

/-- **L4 — THE M-CYCLE IS MONOTONE.**  Specialization is reverse ideal
inclusion (`le_iff_ideal`), the cycle's point action is the comap of the graded
rotation (`finiteLineCycle_apply_ideal`), and comap is monotone. -/
theorem finiteLineCycle_mono (M : ℕ) [NeZero M] {x y : finiteLineScheme M}
    (h : x ≤ y) : finiteLineCycle M x ≤ finiteLineCycle M y :=
  (le_iff_ideal M (finiteLineCycle M x) (finiteLineCycle M y)).mpr
    (by
      rw [finiteLineCycle_apply_ideal M y, finiteLineCycle_apply_ideal M x]
      exact Ideal.comap_mono ((le_iff_ideal M x y).mp h))

/-- The cycle is injective on points (the Inv roundtrip). -/
theorem finiteLineCycle_inj (M : ℕ) [NeZero M] :
    Function.Injective (finiteLineCycle M) := by
  intro a b hab
  have h := congrArg (fun z => finiteLineCycleInv M z) hab
  rw [finiteLineCycleInv_apply M a, finiteLineCycleInv_apply M b] at h
  exact h

/-- **THE INV-MIRROR REFLECTION.**  The cycle reflects the specialization
order: undo the comap of the graded rotation by comapping with the inverse
rotation — `Ideal.comap_comap` (a `rfl` lemma) turns the double comap into the
comap of the composite, and the green quotient-level roundtrip
`lineRotateHom_comp_inv` closes the composite at the identity, so
`Ideal.comap_id` lands back on the original ideal. -/
theorem finiteLineCycle_reflect (M : ℕ) [NeZero M] {x y : finiteLineScheme M}
    (h : finiteLineCycle M x ≤ finiteLineCycle M y) : x ≤ y := by
  have hid : (finiteLineCycle M y).asHomogeneousIdeal.toIdeal ≤
      (finiteLineCycle M x).asHomogeneousIdeal.toIdeal :=
    (le_iff_ideal M (finiteLineCycle M x) (finiteLineCycle M y)).mp h
  rw [finiteLineCycle_apply_ideal M y, finiteLineCycle_apply_ideal M x] at hid
  -- canonicalization of §2a's comap spelling (defeq bridge at default
  -- transparency: `(lineRotateGraded M).toRingHom` unfolds to
  -- `(lineRotateHom M).toRingHom`)
  have hid' : Ideal.comap ((lineRotateHom M).toRingHom)
      y.asHomogeneousIdeal.toIdeal ≤
      Ideal.comap ((lineRotateHom M).toRingHom) x.asHomogeneousIdeal.toIdeal :=
    hid
  have hcomp : (lineRotateHom M).toRingHom.comp (lineRotateInvHom M).toRingHom =
      RingHom.id (lineQuotient M) := by
    apply RingHom.ext
    intro t
    show (lineRotateHom M) ((lineRotateInvHom M) t) = t
    have hrt := DFunLike.congr_fun (lineRotateHom_comp_inv M) t
    rw [AlgHom.comp_apply] at hrt
    exact hrt
  have hundo : ∀ J : Ideal (lineQuotient M),
      Ideal.comap ((lineRotateInvHom M).toRingHom)
        (Ideal.comap ((lineRotateHom M).toRingHom) J) = J := by
    intro J
    rw [Ideal.comap_comap, hcomp, Ideal.comap_id]
  have hkey : y.asHomogeneousIdeal.toIdeal ≤ x.asHomogeneousIdeal.toIdeal := by
    have hmono2 := Ideal.comap_mono (f := (lineRotateInvHom M).toRingHom) hid'
    rw [hundo, hundo] at hmono2
    exact hmono2
  exact (le_iff_ideal M x y).mpr hkey

/-- **THE INV-MIRROR MONO.**  The Inv-cycle is monotone (the reflection
transported through the roundtrip). -/
theorem finiteLineCycleInv_mono (M : ℕ) [NeZero M] {x y : finiteLineScheme M}
    (h : x ≤ y) : finiteLineCycleInv M x ≤ finiteLineCycleInv M y := by
  have h' : finiteLineCycle M (finiteLineCycleInv M x) ≤
      finiteLineCycle M (finiteLineCycleInv M y) := by
    rw [finiteLineCycle_apply_inv M x, finiteLineCycle_apply_inv M y]
    exact h
  exact finiteLineCycle_reflect M h'

/-- The cycle is strictly monotone (the mono plus the reflection). -/
theorem finiteLineCycle_strictMono (M : ℕ) [NeZero M] :
    StrictMono (finiteLineCycle M) := by
  intro a b hab
  refine ⟨finiteLineCycle_mono M hab.le, ?_⟩
  intro hcon
  exact absurd (finiteLineCycle_reflect M hcon) (not_le_of_lt hab)

/-- The cycle reflects the strict order (the reflection plus its own
strictness). -/
theorem finiteLineCycle_strictReflect (M : ℕ) [NeZero M]
    {x y : finiteLineScheme M}
    (h : finiteLineCycle M x < finiteLineCycle M y) : x < y := by
  refine ⟨finiteLineCycle_reflect M h.le, ?_⟩
  intro hle
  exact absurd (finiteLineCycle_mono M hle) (not_le_of_lt h)

/-- **L5 — THE M-CYCLE PRESERVES COHEIGHT.**  The cycle is a strictly
monotone order reflection whose strict-lift witness is the Inv-cycle
roundtrip, so the pin's `Order.coheight_eq_of_strictMono` transports the
coheight of every point. -/
theorem finiteLineCycle_coheight (M : ℕ) [NeZero M] (x : finiteLineScheme M) :
    Order.coheight (finiteLineCycle M x) = Order.coheight x := by
  refine (Order.coheight_eq_of_strictMono (finiteLineCycle M)
    (finiteLineCycle_strictMono M) ?_ x).symm
  intro a b hab
  refine ⟨finiteLineCycleInv M b, ?_, finiteLineCycle_apply_inv M b⟩
  have h1 : finiteLineCycle M a < finiteLineCycle M (finiteLineCycleInv M b) := by
    rw [finiteLineCycle_apply_inv M b]
    exact hab
  exact finiteLineCycle_strictReflect M h1

/-- **L6 — THE M-CYCLE ACTS ON THE COMPONENT INDEX BY THE CYCLIC
PREDECESSOR.**  The strict-below receipt: a coheight-one point lies strictly
below its component's generic point, the cycle (strictly monotone) carries
that below the cycled generic point `η_{cyclicPred j}` (the §2a generic
action), `lineComponentOf_unique` fixes the cycled point's component, and
`lineIndexOfGeneric_lineGenericPoint` reads off the index. -/
theorem finiteLineCycle_componentIndex (M : ℕ) [NeZero M]
    (x : CodimensionPoint (finiteLineWorld M).X 1) :
    lineIndexOfGeneric M (lineComponentOf M
      ⟨(finiteLineCycle M) x.1, (finiteLineCycle_coheight M x.1).trans x.2⟩) =
      cyclicPred M (lineIndexOfGeneric M (lineComponentOf M x)) := by
  have hspec : lineGenericPoint M (lineIndexOfGeneric M (lineComponentOf M x)) =
      (lineComponentOf M x).1 :=
    lineIndexOfGeneric_spec M (lineComponentOf M x)
  have hstep : x.1 < lineGenericPoint M (lineIndexOfGeneric M (lineComponentOf M x)) := by
    rw [hspec]
    exact lineComponentOf_above M x
  have hbelow : (finiteLineCycle M) x.1 <
      lineGenericPoint M (cyclicPred M (lineIndexOfGeneric M (lineComponentOf M x))) := by
    have hpush : (finiteLineCycle M) x.1 <
        (finiteLineCycle M)
        (lineGenericPoint M (lineIndexOfGeneric M (lineComponentOf M x))) :=
      finiteLineCycle_strictMono M hstep
    rw [finiteLineCycle_genericPoint M
      (lineIndexOfGeneric M (lineComponentOf M x))] at hpush
    exact hpush
  have hcomp := lineComponentOf_unique M
    ⟨(finiteLineCycle M) x.1, (finiteLineCycle_coheight M x.1).trans x.2⟩
    ⟨lineGenericPoint M (cyclicPred M (lineIndexOfGeneric M (lineComponentOf M x))),
      lineGenericPoint_coheight M
        (cyclicPred M (lineIndexOfGeneric M (lineComponentOf M x)))⟩
    hbelow
  exact (congrArg (lineIndexOfGeneric M) hcomp).symm.trans
    (lineIndexOfGeneric_lineGenericPoint M
      (cyclicPred M (lineIndexOfGeneric M (lineComponentOf M x))))

/-! ## §3 The two M-cycle letters (GATE-L, wave 7-A)

The two genuine realized closed correspondences of the M-cycle endomorphism,
stated at the GATE-FORM analytification (`finiteLineAnalytificationOfGate`,
whose space `finiteLineSpace M` is definitionally `TopCat.of (sphereUnionSpace
M)` — GSTFiniteLineAnalytification.lean:111-112, the space receipt :423-426
an `rfl`): at this analytification every type-level transport between the
world's `RationalSingularCohomology` and the raw sphere-union's
`singularCohomologyOf` is definitional (the delta chain
`finiteLineAnalytificationOfGate` → the record's `space` field →
`finiteLineSpace` → `TopCat.of`), so the letter operators ARE the green
corpus operators, definitionally:

* **the weight-one letter** `finiteLineCycleLetterOne` — its cohomology
  operator IS `cohomologyPullbackOf (sphereCycle M) 2` (the M-cycle
  pullback at the live degree, GSTSingularCohomologyMaps.lean:133-135),
  the rotation equation rides the green derived letter equation
  `spherePointClassWorld_rotate_of_pullback`
  (GSTPositiveDimensionalLawLanding.lean:148-161) through the definitional
  transport receipt, and the pointwise realization rides the graph
  machinery (`graphCorrespondence_nativePointImage_eq`,
  GSTClassicalHodgeFiniteClosedCorrespondenceOperator.lean:191-198) with
  §1's residue-weight-one and §2b's coheight preservation feeding
  `nativePointPushforward_eq` (GSTClassicalHodgeProjectivePointTransport
  .lean:141-151), the honest atom formula at weight one
  (GSTFiniteLineHonestHodgeData.lean:170-193), L6's component-index
  rotation (:508-536), and the honest world bridge
  `honest_pointClass_eq_world` (:255-265);

* **the weight-zero letter** `finiteLineCycleLetterZero` — its cohomology
  operator is the component-iso index shift (the component H⁰ machine
  `componentCohomologyZeroEquivFinM`,
  GSTComponentCohomologyZero.lean:500-506, precomposed with the cyclic
  successor — the degree-0 rotation is pure linear algebra, no cohomology
  machinery: the singleton-vector rotation `Pi.single j ↦ Pi.single
  (cyclicPred j)` closes by `cyclicSucc_cyclicPred`/
  `cyclicPred_cyclicSucc`), the pointwise realization rides the same
  graph-pushforward chain with the honest atom formula at weight zero
  (:120-140), L3's generic-point action (:378-383) read through
  `lineIndexOfGeneric_spec` (GSTFiniteLinePointAlgebra.lean:1321-1324),
  and the honest world bridge `honest_componentClass_eq_world` (:241-252).

The letters are gate-formed: `FiniteLinePointsGate M`
(GSTFiniteLineAnalytification.lean:403-404) stays a parameter — the frozen
architecture's own discipline (the unconditional
`finiteLineAnalytification` name stays reserved for the gate-discharge
wave; the letters need ONLY the gate-form's space, which is
definitionally the sphere-union regardless of the gate's content).

Honesty ledger: every statement is proved unconditionally given the gate
parameter.  No `sorry`, no new axioms, no `native_decide`.  The GitHub CI
lane `gst-finite-line-cycle-correspondence.yml` owns the kernel check.
-/

/-! ## §3a The weight-one operator and its rotation -/

/-- **THE DEFEQ RECEIPT** — at the gate form, the world's degree-two
rational singular cohomology IS the raw sphere-union's (the delta chain:
the record's `space` field is `finiteLineSpace M`, which is
`TopCat.of (sphereUnionSpace M)`; `RationalSingularCohomology` is
abbrev-transparent to `singularCohomologyOf A.space` — the `rfl` at
GSTSingularCohomologyMaps.lean:79-81).  THE designated CI repair point of
§3: if the elaborator stalls on any §3 unification, this receipt is the
contract every other proof rides. -/
theorem finiteLineGate_cohomology_two_defeq (M : ℕ) [NeZero M]
    (gate : FiniteLinePointsGate M) :
    RationalSingularCohomology (finiteLineAnalytificationOfGate M gate) 2 =
      singularCohomologyOf (TopCat.of (sphereUnionSpace M)) 2 := rfl

/-- **THE WEIGHT-ONE LETTER OPERATOR** — the M-cycle pullback at the live
degree, definitionally: at the gate-form analytification the operator's
declared type (the world's `RationalSingularCohomology`) unifies with the
pullback's own type (the sphere-union's `singularCohomologyOf`) by the
delta chain of `finiteLineGate_cohomology_two_defeq`. -/
noncomputable def finiteLineCycleLetterOpOne (M : ℕ) [NeZero M]
    (gate : FiniteLinePointsGate M) :
    RationalSingularCohomology (finiteLineAnalytificationOfGate M gate) 2 →ₗ[ℚ]
      RationalSingularCohomology (finiteLineAnalytificationOfGate M gate) 2 :=
  cohomologyPullbackOf (sphereCycle M) 2

/-- **THE TRANSPORT RECEIPT** — the operator applied at a
`sphereUnionCoe`-transported value is the transport of the pullback's
value: at the gate form the cast transports ride `rfl`-provable type
equalities (the space receipt :423-426 is `rfl`), so the equation is
definitional.  This is exactly the `hRop` hypothesis the green derived
letter equation consumes. -/
theorem finiteLineCycleLetterOpOne_transport (M : ℕ) [NeZero M]
    (gate : FiniteLinePointsGate M)
    (u : singularCohomologyOf (TopCat.of (sphereUnionSpace M)) 2) :
    finiteLineCycleLetterOpOne M gate
        (sphereUnionCoe M (finiteLineAnalytificationOfGate_space M gate) u) =
      sphereUnionCoe M (finiteLineAnalytificationOfGate_space M gate)
        ((cohomologyPullbackOf (sphereCycle M) 2) u) := rfl

/-- **THE WEIGHT-ONE ROTATION** — the operator rotates the honest world
point-class family by the cyclic predecessor: the green derived letter
equation (`spherePointClassWorld_rotate_of_pullback`, whose proof is
`cycle_pointClass` — GSTSphereUnionPointClassGate.lean:140-148 — consumed
through the transport receipt). -/
theorem finiteLineCycleLetterOpOne_rotate (M : ℕ) [NeZero M]
    (gate : FiniteLinePointsGate M)
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2) (j : Fin M) :
    finiteLineCycleLetterOpOne M gate
      (spherePointClassWorld (V := finiteLineWorld M)
        (H := finiteLineHodgeDataHonest M (finiteLineAnalytificationOfGate M gate)
          (finiteLineAnalytificationOfGate_space M gate) ω)
        M (finiteLineAnalytificationOfGate_space M gate) ω j) =
    spherePointClassWorld (V := finiteLineWorld M)
      (H := finiteLineHodgeDataHonest M (finiteLineAnalytificationOfGate M gate)
        (finiteLineAnalytificationOfGate_space M gate) ω)
      M (finiteLineAnalytificationOfGate_space M gate) ω (cyclicPred M j) := by
  show finiteLineCycleLetterOpOne M gate
      (sphereUnionCoe M (finiteLineAnalytificationOfGate_space M gate)
        (spherePointClass M ω j)) =
    sphereUnionCoe M (finiteLineAnalytificationOfGate_space M gate)
      (spherePointClass M ω (cyclicPred M j))
  rw [finiteLineCycleLetterOpOne_transport M gate (spherePointClass M ω j),
    cycle_pointClass M ω j]

/-! ## §3b The weight-zero operator and its rotation -/

/-- **THE INDEX-SHIFT OPERATOR** — the precomposition with the cyclic
successor on the free rank-M function space (the degree-0 rotation as
pure linear algebra). -/
noncomputable def finiteLineCyclePrecompSucc (M : ℕ) [NeZero M] :
    (Fin M → ℚ) →ₗ[ℚ] (Fin M → ℚ) where
  toFun := fun v k => v (cyclicSucc M k)
  map_add' := by
    intro v w
    funext k
    show (v + w) (cyclicSucc M k) =
      v (cyclicSucc M k) + w (cyclicSucc M k)
    rfl
  map_smul' := by
    intro q v
    funext k
    show (q • v) (cyclicSucc M k) = q • v (cyclicSucc M k)
    rfl

/-- **THE SINGLETON ROTATION** — the index-shift operator carries the
j-th indicator vector to the `cyclicPred j`-th one (the two if-conditions
are the same equation: `cyclicSucc k = j` iff `k = cyclicPred j`, by the
green successor/predecessor roundtrips). -/
theorem finiteLineCyclePrecompSucc_single (M : ℕ) [NeZero M] (j : Fin M) :
    finiteLineCyclePrecompSucc M (Pi.single j (1 : ℚ)) =
      Pi.single (cyclicPred M j) (1 : ℚ) := by
  funext k
  show (Pi.single j (1 : ℚ)) (cyclicSucc M k) =
      (Pi.single (cyclicPred M j) (1 : ℚ)) k
  rw [Pi.single_apply, Pi.single_apply]
  by_cases hk : cyclicSucc M k = j
  · rw [if_pos hk]
    have hk' : k = cyclicPred M j := by
      have h := congrArg (cyclicPred M) hk
      rwa [cyclicPred_cyclicSucc M k] at h
    rw [if_pos hk']
  · rw [if_neg hk, if_neg (fun hcon =>
      hk (by rw [hcon, cyclicSucc_cyclicPred M j]))]

/-- **THE WEIGHT-ZERO LETTER OPERATOR** — the component-iso conjugate of
the index shift: through the component H⁰ machine, conjugate by the
degree-zero iso, the operator is the precomposition with the cyclic
successor (the honest degree-0 action of the M-cycle). -/
noncomputable def finiteLineCycleLetterOpZero (M : ℕ) [NeZero M]
    (gate : FiniteLinePointsGate M) :
    RationalSingularCohomology (finiteLineAnalytificationOfGate M gate) 0 →ₗ[ℚ]
      RationalSingularCohomology (finiteLineAnalytificationOfGate M gate) 0 :=
  { toFun := fun u =>
      (componentCohomologyZeroEquivFinM (finiteLineAnalytificationOfGate M gate) M
        (sphereUnion_cohomology_zero (finiteLineAnalytificationOfGate_space M gate))).symm
        (finiteLineCyclePrecompSucc M
          ((componentCohomologyZeroEquivFinM (finiteLineAnalytificationOfGate M gate) M
            (sphereUnion_cohomology_zero (finiteLineAnalytificationOfGate_space M gate))) u))
    map_add' := by
      intro u v
      show (componentCohomologyZeroEquivFinM (finiteLineAnalytificationOfGate M gate) M
          (sphereUnion_cohomology_zero (finiteLineAnalytificationOfGate_space M gate))).symm
          (finiteLineCyclePrecompSucc M
            ((componentCohomologyZeroEquivFinM (finiteLineAnalytificationOfGate M gate) M
              (sphereUnion_cohomology_zero (finiteLineAnalytificationOfGate_space M gate)))
              (u + v))) = _ + _
      rw [LinearEquiv.map_add, LinearMap.map_add, LinearEquiv.map_add]
    map_smul' := by
      intro q u
      show (componentCohomologyZeroEquivFinM (finiteLineAnalytificationOfGate M gate) M
          (sphereUnion_cohomology_zero (finiteLineAnalytificationOfGate_space M gate))).symm
          (finiteLineCyclePrecompSucc M
            ((componentCohomologyZeroEquivFinM (finiteLineAnalytificationOfGate M gate) M
              (sphereUnion_cohomology_zero (finiteLineAnalytificationOfGate_space M gate)))
              (q • u))) = _
      rw [LinearEquiv.map_smul, LinearMap.map_smul, LinearEquiv.map_smul] }

/-- **THE WEIGHT-ZERO ROTATION** — the operator rotates the honest world
component-class family by the cyclic predecessor: the component-class
family IS the component iso's inverse of the indicator vectors
(definitionally — `sphereComponentClass`,
GSTPositiveDimensionalLawLanding.lean:168-173, whose `H`-dependence is
only through `H.analytification`, definitionally the gate form here),
the operator conjugates the indicator rotation, and the singleton
rotation is `finiteLineCyclePrecompSucc_single`. -/
theorem finiteLineCycleLetterOpZero_rotate (M : ℕ) [NeZero M]
    (gate : FiniteLinePointsGate M)
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2) (j : Fin M) :
    finiteLineCycleLetterOpZero M gate
      (sphereComponentClass (V := finiteLineWorld M)
        (H := finiteLineHodgeDataHonest M (finiteLineAnalytificationOfGate M gate)
          (finiteLineAnalytificationOfGate_space M gate) ω)
        M (Nat.pos_of_neZero ‹_›) (finiteLineAnalytificationOfGate_space M gate) j) =
    sphereComponentClass (V := finiteLineWorld M)
      (H := finiteLineHodgeDataHonest M (finiteLineAnalytificationOfGate M gate)
        (finiteLineAnalytificationOfGate_space M gate) ω)
      M (Nat.pos_of_neZero ‹_›) (finiteLineAnalytificationOfGate_space M gate)
        (cyclicPred M j) := by
  have hEq : sphereComponentClass (V := finiteLineWorld M)
      (H := finiteLineHodgeDataHonest M (finiteLineAnalytificationOfGate M gate)
        (finiteLineAnalytificationOfGate_space M gate) ω)
      M (Nat.pos_of_neZero ‹_›) (finiteLineAnalytificationOfGate_space M gate) j =
      (componentCohomologyZeroEquivFinM (finiteLineAnalytificationOfGate M gate) M
        (sphereUnion_cohomology_zero (finiteLineAnalytificationOfGate_space M gate))).symm
        (Pi.single j (1 : ℚ)) := rfl
  show (componentCohomologyZeroEquivFinM (finiteLineAnalytificationOfGate M gate) M
        (sphereUnion_cohomology_zero (finiteLineAnalytificationOfGate_space M gate))).symm
      (finiteLineCyclePrecompSucc M
        ((componentCohomologyZeroEquivFinM (finiteLineAnalytificationOfGate M gate) M
          (sphereUnion_cohomology_zero (finiteLineAnalytificationOfGate_space M gate)))
          (sphereComponentClass (V := finiteLineWorld M)
            (H := finiteLineHodgeDataHonest M (finiteLineAnalytificationOfGate M gate)
              (finiteLineAnalytificationOfGate_space M gate) ω)
            M (Nat.pos_of_neZero ‹_›) (finiteLineAnalytificationOfGate_space M gate) j))) = _
  rw [hEq, LinearEquiv.apply_symm_apply, finiteLineCyclePrecompSucc_single M j]
  rfl

/-! ## §3c The weight-one letter -/

/-- **THE WEIGHT-ONE M-CYCLE LETTER** — the graph correspondence of the
M-cycle endomorphism (the geometry: the graph, a closed immersion with
singleton left fibers — GSTClassicalHodgeFiniteClosedCorrespondence
.lean:231-244) with the M-cycle pullback as the cohomological operator,
realized on points: the class of the graph's native image of any closed
point is the pullback of the point's class.  The realization chain: the
graph's native image is the native point pushforward
(`graphCorrespondence_nativePointImage_eq`); the pushforward of a
codimension-one point under the cycle is its image atom (§1's residue
weight one + §2b's coheight preservation inside
`nativePointPushforward_eq`); the honest atom formula at weight one
evaluates the image atom's class as the point class of its line; L6
rotates the line index; the world bridge lands the honest family; on the
other side, the same atom formula and bridge evaluate the source point's
class, and the operator's rotation
(`finiteLineCycleLetterOpOne_rotate`) closes the equation. -/
noncomputable def finiteLineCycleLetterOne (M : ℕ) [NeZero M]
    (gate : FiniteLinePointsGate M)
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2) :
    RealizedFiniteClosedCorrespondence (finiteLineWorld M)
      (finiteLineHodgeDataHonest M (finiteLineAnalytificationOfGate M gate)
        (finiteLineAnalytificationOfGate_space M gate) ω) 1 where
  geometry := FiniteClosedCorrespondence.graphCorrespondence (finiteLineCycleEndo M)
  cohomologyOperator := finiteLineCycleLetterOpOne M gate
  realizes_on_points := by
    intro x
    -- the coheight of the image (L5 + the packaging's own proof)
    have hco : Order.coheight ((finiteLineCycle M) x.1) = 1 :=
      (finiteLineCycle_coheight M x.1).trans x.2
    -- the graph's native image is the pushforward, then the image atom
    have himg : (FiniteClosedCorrespondence.graphCorrespondence (finiteLineCycleEndo M)).nativePointImage 1 x =
        nativePointPushforward (finiteLineCycle M) 1 x :=
      FiniteClosedCorrespondence.graphCorrespondence_nativePointImage_eq
        (finiteLineCycleEndo M) 1 x
    have hpush : nativePointPushforward (finiteLineCycle M) 1 x =
        pointResidueWeight (finiteLineCycle M) x.1 •
          codimensionPointCycle (finiteLineWorld M).X 1 ⟨(finiteLineCycle M) x.1, hco⟩ :=
      nativePointPushforward_eq (finiteLineCycle M) 1 x hco
    have hw : pointResidueWeight (finiteLineCycle M) x.1 = 1 :=
      finiteLineCycle_pointResidueWeight M x.1
    -- the honest atom formulas at the image and at the source
    have hatomImg := honestCycleClassOne_atom M (finiteLineWorld M)
      (finiteLineAnalytificationOfGate M gate) (finiteLineAnalytificationOfGate_space M gate) ω
      ⟨(finiteLineCycle M) x.1, hco⟩
    have hatom := honestCycleClassOne_atom M (finiteLineWorld M)
      (finiteLineAnalytificationOfGate M gate) (finiteLineAnalytificationOfGate_space M gate) ω x
    -- L6: the image's line index is the predecessor of the source's
    have hidx := finiteLineCycle_componentIndex M x
    -- the honest world bridges at both indices
    have hbridgeImg := honest_pointClass_eq_world M
      (finiteLineAnalytificationOfGate M gate) (finiteLineAnalytificationOfGate_space M gate) ω
      (cyclicPred M (lineIndexOfGeneric M (lineComponentOf M x)))
    have hbridge := honest_pointClass_eq_world M
      (finiteLineAnalytificationOfGate M gate) (finiteLineAnalytificationOfGate_space M gate) ω
      (lineIndexOfGeneric M (lineComponentOf M x))
    -- the operator's rotation at the source's index
    have hrot := finiteLineCycleLetterOpOne_rotate M gate ω
      (lineIndexOfGeneric M (lineComponentOf M x))
    -- the goal, restated at the honest data's unfolded cycle-class maps
    show honestCycleClassOne M (finiteLineWorld M)
        (finiteLineAnalytificationOfGate M gate)
        (finiteLineAnalytificationOfGate_space M gate) ω
        ((FiniteClosedCorrespondence.graphCorrespondence (finiteLineCycleEndo M)).nativePointImage 1 x) =
      finiteLineCycleLetterOpOne M gate
        (honestCycleClassOne M (finiteLineWorld M)
          (finiteLineAnalytificationOfGate M gate)
          (finiteLineAnalytificationOfGate_space M gate) ω
          (codimensionPointCycle (finiteLineWorld M).X 1 x))
    rw [himg, hpush, hw, one_smul, hatomImg, hidx, hbridgeImg, hatom,
      hbridge, hrot]

/-! ## §3d The weight-zero letter -/

/-- **THE WEIGHT-ZERO M-CYCLE LETTER** — the graph correspondence of the
M-cycle endomorphism with the component-iso index shift as the
cohomological operator, realized on points: the class of the graph's
native image of any generic point is the operator's value at the point's
class.  The realization chain mirrors the weight-one letter's: the graph
pushforward and the residue weight reduce the image to the image atom;
the honest atom formula at weight zero evaluates it as the component
class of its line; L3's generic-point action (read through
`lineIndexOfGeneric_spec`) rotates the line index; the world bridge and
the operator's rotation (`finiteLineCycleLetterOpZero_rotate`) close the
equation on the other side. -/
noncomputable def finiteLineCycleLetterZero (M : ℕ) [NeZero M]
    (gate : FiniteLinePointsGate M)
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2) :
    RealizedFiniteClosedCorrespondence (finiteLineWorld M)
      (finiteLineHodgeDataHonest M (finiteLineAnalytificationOfGate M gate)
        (finiteLineAnalytificationOfGate_space M gate) ω) 0 where
  geometry := FiniteClosedCorrespondence.graphCorrespondence (finiteLineCycleEndo M)
  cohomologyOperator := finiteLineCycleLetterOpZero M gate
  realizes_on_points := by
    intro η
    -- the coheight of the image (L5 + the packaging's own proof)
    have hco : Order.coheight ((finiteLineCycle M) η.1) = 0 :=
      (finiteLineCycle_coheight M η.1).trans η.2
    -- the graph's native image is the pushforward, then the image atom
    have himg : (FiniteClosedCorrespondence.graphCorrespondence (finiteLineCycleEndo M)).nativePointImage 0 η =
        nativePointPushforward (finiteLineCycle M) 0 η :=
      FiniteClosedCorrespondence.graphCorrespondence_nativePointImage_eq
        (finiteLineCycleEndo M) 0 η
    have hpush : nativePointPushforward (finiteLineCycle M) 0 η =
        pointResidueWeight (finiteLineCycle M) η.1 •
          codimensionPointCycle (finiteLineWorld M).X 0 ⟨(finiteLineCycle M) η.1, hco⟩ :=
      nativePointPushforward_eq (finiteLineCycle M) 0 η hco
    have hw : pointResidueWeight (finiteLineCycle M) η.1 = 1 :=
      finiteLineCycle_pointResidueWeight M η.1
    -- the honest atom formulas at the image and at the source
    have hatomImg := honestCycleClassZero_atom M (finiteLineWorld M)
      (finiteLineAnalytificationOfGate M gate) (finiteLineAnalytificationOfGate_space M gate)
      ⟨(finiteLineCycle M) η.1, hco⟩
    have hatom := honestCycleClassZero_atom M (finiteLineWorld M)
      (finiteLineAnalytificationOfGate M gate) (finiteLineAnalytificationOfGate_space M gate) η
    -- L3 read through the spec: the image's line index is the
    -- predecessor of the source's
    have hspecImg := lineIndexOfGeneric_spec M
      ⟨(finiteLineCycle M) η.1, hco⟩
    have hspec := lineIndexOfGeneric_spec M η
    have hpt : (finiteLineCycle M) η.1 =
        lineGenericPoint M (cyclicPred M (lineIndexOfGeneric M η)) := by
      rw [← hspec]
      exact finiteLineCycle_genericPoint M (lineIndexOfGeneric M η)
    have hidx : lineIndexOfGeneric M
        ⟨(finiteLineCycle M) η.1, hco⟩ =
        cyclicPred M (lineIndexOfGeneric M η) :=
      lineGenericPoint_injective M (hspecImg.trans hpt)
    -- the honest world bridges at both indices
    have hbridgeImg := honest_componentClass_eq_world M
      (finiteLineAnalytificationOfGate M gate) (finiteLineAnalytificationOfGate_space M gate) ω
      (cyclicPred M (lineIndexOfGeneric M η))
    have hbridge := honest_componentClass_eq_world M
      (finiteLineAnalytificationOfGate M gate) (finiteLineAnalytificationOfGate_space M gate) ω
      (lineIndexOfGeneric M η)
    -- the operator's rotation at the source's index
    have hrot := finiteLineCycleLetterOpZero_rotate M gate ω
      (lineIndexOfGeneric M η)
    -- the goal, restated at the honest data's unfolded cycle-class maps
    show honestCycleClassZero M (finiteLineWorld M)
        (finiteLineAnalytificationOfGate M gate)
        (finiteLineAnalytificationOfGate_space M gate)
        ((FiniteClosedCorrespondence.graphCorrespondence (finiteLineCycleEndo M)).nativePointImage 0 η) =
      finiteLineCycleLetterOpZero M gate
        (honestCycleClassZero M (finiteLineWorld M)
          (finiteLineAnalytificationOfGate M gate)
          (finiteLineAnalytificationOfGate_space M gate)
          (codimensionPointCycle (finiteLineWorld M).X 0 η))
    rw [himg, hpush, hw, one_smul, hatomImg, hidx, hbridgeImg, hatom,
      hbridge, hrot]

/-! ## §3e The rotation equations in the engine's spelling -/

/-- **THE WEIGHT-ONE ROTATION, LETTER-SPELLED** — the letter's own
cohomology operator rotates the world point-class family by the cyclic
predecessor (the engine's `hR₁` form: the field projection is
definitionally the operator). -/
theorem finiteLineCycleLetterOne_rotate (M : ℕ) [NeZero M]
    (gate : FiniteLinePointsGate M)
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2) (j : Fin M) :
    (finiteLineCycleLetterOne M gate ω).cohomologyOperator
      (spherePointClassWorld (V := finiteLineWorld M)
        (H := finiteLineHodgeDataHonest M (finiteLineAnalytificationOfGate M gate)
          (finiteLineAnalytificationOfGate_space M gate) ω)
        M (finiteLineAnalytificationOfGate_space M gate) ω j) =
    spherePointClassWorld (V := finiteLineWorld M)
      (H := finiteLineHodgeDataHonest M (finiteLineAnalytificationOfGate M gate)
        (finiteLineAnalytificationOfGate_space M gate) ω)
      M (finiteLineAnalytificationOfGate_space M gate) ω (cyclicPred M j) :=
  finiteLineCycleLetterOpOne_rotate M gate ω j

/-- **THE WEIGHT-ZERO ROTATION, LETTER-SPELLED** — the letter's own
cohomology operator rotates the world component-class family by the
cyclic predecessor (the engine's `hR₀` form). -/
theorem finiteLineCycleLetterZero_rotate (M : ℕ) [NeZero M]
    (gate : FiniteLinePointsGate M)
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2) (j : Fin M) :
    (finiteLineCycleLetterZero M gate ω).cohomologyOperator
      (sphereComponentClass (V := finiteLineWorld M)
        (H := finiteLineHodgeDataHonest M (finiteLineAnalytificationOfGate M gate)
          (finiteLineAnalytificationOfGate_space M gate) ω)
        M (Nat.pos_of_neZero ‹_›) (finiteLineAnalytificationOfGate_space M gate) j) =
    sphereComponentClass (V := finiteLineWorld M)
      (H := finiteLineHodgeDataHonest M (finiteLineAnalytificationOfGate M gate)
        (finiteLineAnalytificationOfGate_space M gate) ω)
      M (Nat.pos_of_neZero ‹_›) (finiteLineAnalytificationOfGate_space M gate)
        (cyclicPred M j) :=
  finiteLineCycleLetterOpZero_rotate M gate ω j

/-! ## §3 Receipts -/

#check finiteLineGate_cohomology_two_defeq
#check finiteLineCycleLetterOpOne
#check finiteLineCycleLetterOpOne_transport
#check finiteLineCycleLetterOpOne_rotate
#check finiteLineCycleLetterOne
#check finiteLineCycleLetterOne_rotate
#check finiteLineCyclePrecompSucc
#check finiteLineCyclePrecompSucc_single
#check finiteLineCycleLetterOpZero
#check finiteLineCycleLetterOpZero_rotate
#check finiteLineCycleLetterZero
#check finiteLineCycleLetterZero_rotate

#print axioms finiteLineCycleLetterOpOne_rotate
#print axioms finiteLineCycleLetterOne
#print axioms finiteLineCycleLetterZero
#print axioms finiteLineCycleLetterOne_rotate
#print axioms finiteLineCycleLetterZero_rotate

end GSTFiniteLineCycleCorrespondence

end -- noncomputable section
