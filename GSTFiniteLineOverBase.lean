import Mathlib
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import GSTFiniteLineRing
import GSTProjectiveOverC
import GSTFiniteLineWorldCarrier
import GSTFiniteLineClosedImmersion
import GSTFiniteLineSmoothness

/-!
# THE OVER-BASE SQUARES AND THE ACTUAL FINITE-LINE WORLD

The unconditional round's R3+R1 battle: the two over-base compatibility
squares that the world gate demands, and the world bundle they complete.

## Contents

* `gradedZeroHom` — the degree-zero restriction of a graded ring hom
  (a ring hom `(𝒜 0) →+* (ℬ 0)` from any `𝒜 →+*ᵍ ℬ`);
* `fromZeroRingHom_comp_awayMap` — THE RING SQUARE: pushing a degree-zero
  element into the away-localization commutes with the away-map of a
  graded hom (the ring-level heart of the base-naturality);
* `Proj_map_comp_toSpecZero` — THE BASE-NATURALITY (the missing pin
  lemma): `Proj.map g ≫ Proj.toSpecZero 𝒜 = Proj.toSpecZero ℬ ≫
  Spec.map (gradedZeroHom g)` for every graded hom `g` — proved by the
  chart interchange (`awayι_comp_map`), the chart's structure-map square
  (`awayι_toSpecZero`), the ring square, and open-cover `hom_ext`
  (the `map_comp` doctrine of the pin, Functor.lean);
* `finiteLineEmbedding_over_base` — R3: the closed embedding commutes
  with the projective-space structure map (the `ProjectiveOverC` field);
* `finiteLineCycle_over_base` — R1: the M-cycle automorphism is a
  complex-scheme endomorphism (commutes with the structure map);
* `finiteLineWorld` — THE ACTUAL WORLD BUNDLE: the F1+F2+F3 carrier
  (scheme + structure map + smoothness + the projective witness), the
  `finitePointWorld` pattern at the finite-line world;
* the world-gate identification receipts (`rfl`).

Every external name is point-verified against the CI-green corpus or the
pinned Mathlib (research/pin/mathlib-51e6992).  No `sorry`, no new
axioms, no `native_decide`.  The GitHub CI lane
`gst-finite-line-world.yml` owns the kernel check.
-/

set_option maxHeartbeats 200000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry CategoryTheory
open GSTProjectiveOverC GSTFiniteLineRing GSTFiniteLineWorldCarrier
open GSTFiniteLineClosedImmersion GSTFiniteLineSmoothness
open MvPolynomial DirectSum
open HomogeneousLocalization

namespace GSTFiniteLineOverBase

/-! ## §0 The degree-zero restriction of a graded ring hom -/

section General

variable {A : Type*} [CommRing A] {σ : Type*} [SetLike σ A]
  [AddSubgroupClass σ A] {𝒜 : ℕ → σ} [GradedRing 𝒜]
variable {B : Type*} [CommRing B] {τ : Type*} [SetLike τ B]
  [AddSubgroupClass τ B] {ℬ : ℕ → τ} [GradedRing ℬ]

/-- **THE DEGREE-ZERO RESTRICTION.**  A graded ring hom restricts to a
genuine ring hom of the degree-zero pieces (the graded-mem field carries
the membership). -/
def gradedZeroHom (g : 𝒜 →+*ᵍ ℬ) : (𝒜 0) →+* (ℬ 0) where
  toFun x := ⟨g x, g.2 x.2⟩
  map_one' := by
    apply Subtype.ext
    exact map_one g
  map_zero' := by
    apply Subtype.ext
    exact map_zero g
  map_add' x y := by
    apply Subtype.ext
    show g (x + y) = g x + g y
    rw [map_add]
    rfl
  map_mul' x y := by
    apply Subtype.ext
    show g (x * y) = g x * g y
    rw [map_mul]
    rfl

theorem gradedZeroHom_apply (g : 𝒜 →+*ᵍ ℬ) (x : 𝒜 0) :
    gradedZeroHom g x = ⟨g x, g.2 x.2⟩ := rfl

/-- **THE RING SQUARE.**  Pushing a degree-zero element into the
away-localization commutes with the away-map of a graded hom: the two
roads from `(𝒜 0)` to `Away ℬ (g s)` — localize first then push the
localization, or restrict to degree zero first then localize — agree.
This is the ring-level heart of the base-naturality. -/
theorem fromZeroRingHom_comp_awayMap (g : 𝒜 →+*ᵍ ℬ) {i : ℕ} (hi : 0 < i)
    (s : A) (hs : s ∈ 𝒜 i) :
    (Away.map g s).comp (fromZeroRingHom 𝒜 (Submonoid.powers s)) =
      (fromZeroRingHom ℬ (Submonoid.powers (g s))).comp (gradedZeroHom g) := by
  ext a
  have hL : (Away.map g s) ((fromZeroRingHom 𝒜 (Submonoid.powers s)) a)
      = HomogeneousLocalization.mk ℬ ⟨0, g (a : A), 1, one_mem _⟩ := by
    have h1 : (fromZeroRingHom 𝒜 (Submonoid.powers s)) a
        = Away.mk 𝒜 hs 0 a a.2 := rfl
    rw [h1, Away.map_mk g s hs 0 a a.2]
  have hR : (fromZeroRingHom ℬ (Submonoid.powers (g s))) (gradedZeroHom g a)
      = HomogeneousLocalization.mk ℬ ⟨0, g (a : A), 1, one_mem _⟩ := rfl
  rw [hL, hR]

/-- **THE BASE-NATURALITY OF `Proj.map`** — the missing pin lemma (the
architecture's R3 core): the Proj map of a graded hom commutes with the
structure maps to the degree-zero spectra.  The proof is the pin's own
`map_comp` doctrine (Functor.lean): open-cover `hom_ext` on the
`mapAffineOpenCover` charts, the chart interchange `awayι_comp_map`, the
chart's structure-map square `awayι_toSpecZero` on both sides, the
`Spec.map` merge, and the ring square. -/
theorem Proj_map_comp_toSpecZero (g : 𝒜 →+*ᵍ ℬ)
    (hg : HomogeneousIdeal.irrelevant ℬ ≤
      HomogeneousIdeal.map g (HomogeneousIdeal.irrelevant 𝒜)) :
    Proj.map g hg ≫ Proj.toSpecZero 𝒜 =
      Proj.toSpecZero ℬ ≫
        Spec.map (CommRingCat.ofHom (gradedZeroHom g)) := by
  refine (Proj.mapAffineOpenCover g hg).openCover.hom_ext _ _ fun s ↦ ?_
  simp only [Scheme.AffineOpenCover.openCover_f, Proj.mapAffineOpenCover_f]
  have hL : (awayι ℬ (g s.2) (g.2 s.2.2) s.1.2) ≫
      (Proj.map g hg ≫ Proj.toSpecZero 𝒜) =
      Spec.map (CommRingCat.ofHom
        ((Away.map g s).comp
          (fromZeroRingHom 𝒜 (Submonoid.powers s)))) := by
    rw [← CategoryTheory.Category.assoc,
      Proj.awayι_comp_map g hg s.1.2 s.2 s.2.2,
      CategoryTheory.Category.assoc,
      Proj.awayι_toSpecZero 𝒜 s.2 s.2.2 s.1.2]
    exact (Spec.map_comp _ _).symm
  have hR : (awayι ℬ (g s.2) (g.2 s.2.2) s.1.2) ≫
      (Proj.toSpecZero ℬ ≫
        Spec.map (CommRingCat.ofHom (gradedZeroHom g))) =
      Spec.map (CommRingCat.ofHom
        ((fromZeroRingHom ℬ (Submonoid.powers (g s.2))).comp
          (gradedZeroHom g))) := by
    rw [← CategoryTheory.Category.assoc,
      Proj.awayι_toSpecZero ℬ (g s.2) (g.2 s.2.2) s.1.2]
    exact (Spec.map_comp _ _).symm
  rw [hL, hR]
  exact congrArg (Spec.map ∘ CommRingCat.ofHom)
    (fromZeroRingHom_comp_awayMap g s.1.2 s.2 s.2.2)

end General

/-! ## §1 The constants-fixing triangles -/

/-- **THE QUOTIENT FIXES THE CONSTANTS** — the degree-zero restriction of
the graded quotient presentation carries the ambient algebra map to the
line algebra map (both degree-zero pieces are the constants, and the
quotient fixes them). -/
theorem lineGradedQuotientHom_gradedZero_algebraMap (M : ℕ) [NeZero M] :
    (gradedZeroHom (lineGradedQuotientHom M)).comp
        (algebraMap ℂ (ProjectiveGrading (2 * M - 1) 0)) =
      algebraMap ℂ (lineGrading M 0) := by
  ext c
  apply Subtype.ext
  have hA : algebraMap ℂ (ProjectiveGrading (2 * M - 1) 0) c
      = ⟨MvPolynomial.C c, by
          rw [mem_homogeneousSubmodule]
          exact isHomogeneous_C⟩ := rfl
  have hB : algebraMap ℂ (lineGrading M 0) c
      = ⟨algebraMap ℂ (lineQuotient M) c, by
          exact lineQuotientMap_mem_lineGrading M 0 _
            (by
              rw [mem_homogeneousSubmodule]
              exact isHomogeneous_C)⟩ := rfl
  show (lineGradedQuotientHom M)
      ((algebraMap ℂ (ProjectiveGrading (2 * M - 1) 0)) c) =
    (algebraMap ℂ (lineGrading M 0)) c
  rw [hA, hB]
  show (ambientQuotientHom M) (MvPolynomial.C c) = algebraMap ℂ (lineQuotient M) c
  exact (ambientQuotientHom M).commutes c

/-- **THE ROTATION FIXES THE CONSTANTS** — the degree-zero restriction of
the graded M-cycle rotation is the identity on the algebra map (the
rotation is a ℂ-algebra automorphism). -/
theorem lineRotateGraded_gradedZero_algebraMap (M : ℕ) :
    (gradedZeroHom (lineRotateGraded M)).comp
        (algebraMap ℂ (lineGrading M 0)) =
      algebraMap ℂ (lineGrading M 0) := by
  ext c
  apply Subtype.ext
  have hB : algebraMap ℂ (lineGrading M 0) c
      = ⟨algebraMap ℂ (lineQuotient M) c, by
          exact lineQuotientMap_mem_lineGrading M 0 _
            (by
              rw [mem_homogeneousSubmodule]
              exact isHomogeneous_C)⟩ := rfl
  show (lineRotateGraded M) ((algebraMap ℂ (lineGrading M 0)) c) =
    (algebraMap ℂ (lineGrading M 0)) c
  rw [hB]
  show (lineRotateHom M) (algebraMap ℂ (lineQuotient M) c) =
    algebraMap ℂ (lineQuotient M) c
  exact (lineRotateHom M).commutes c

/-! ## §2 THE OVER-BASE SQUARES -/

/-- **R3 — THE EMBEDDING'S OVER-BASE SQUARE.**  The closed embedding into
`ℙ^{2M-1}` commutes with the projective-space structure map: the world's
`ProjectiveOverC` field.  The base-naturality instantiated at the graded
quotient presentation, with the constants triangle closing the base maps. -/
theorem finiteLineEmbedding_over_base (M : ℕ) [NeZero M] :
    finiteLineEmbedding M ≫ projectiveSpaceToBase (2 * M - 1) =
      finiteLineStructureMap M := by
  show Proj.map (lineGradedQuotientHom M) (line_irrelevant_le M) ≫
      (Proj.toSpecZero (ProjectiveGrading (2 * M - 1)) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap ℂ (ProjectiveGrading (2 * M - 1) 0)))) =
    Proj.toSpecZero (lineGrading M) ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (lineGrading M 0)))
  rw [← CategoryTheory.Category.assoc,
    Proj_map_comp_toSpecZero (lineGradedQuotientHom M) (line_irrelevant_le M),
    CategoryTheory.Category.assoc, Spec.map_comp]
  exact congrArg (Spec.map ∘ CommRingCat.ofHom)
    (lineGradedQuotientHom_gradedZero_algebraMap M)

/-- **R1 — THE CYCLE'S OVER-BASE SQUARE.**  The M-cycle automorphism
commutes with the structure map: it is a complex-scheme endomorphism of
the finite-line world. -/
theorem finiteLineCycle_over_base (M : ℕ) :
    finiteLineCycle M ≫ finiteLineStructureMap M =
      finiteLineStructureMap M := by
  show Proj.map (lineRotateGraded M) (lineRotate_irrelevant_le M) ≫
      (Proj.toSpecZero (lineGrading M) ≫
        Spec.map (CommRingCat.ofHom (algebraMap ℂ (lineGrading M 0)))) =
    Proj.toSpecZero (lineGrading M) ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (lineGrading M 0)))
  rw [← CategoryTheory.Category.assoc,
    Proj_map_comp_toSpecZero (lineRotateGraded M) (lineRotate_irrelevant_le M),
    CategoryTheory.Category.assoc, Spec.map_comp]
  exact congrArg (Spec.map ∘ CommRingCat.ofHom)
    (lineRotateGraded_gradedZero_algebraMap M)

/-! ## §3 THE ACTUAL WORLD BUNDLE -/

/-- **THE FINITE-LINE WORLD** — the actual smooth projective complex
scheme of the finite-line variety: the F1 carrier (the Proj of the
cross-monomial quotient grading), the F2 projective witness (the closed
embedding into `ℙ^{2M-1}` commuting with the base, both kernel-certified),
and the F3 smoothness (the chartwise locality cascade) — the
`finitePointWorld` pattern (GSTFinitePointWorldCarrier.lean:735) at the
finite-line world. -/
noncomputable def finiteLineWorld (M : ℕ) [NeZero M] :
    SmoothProjectiveComplexScheme :=
  ⟨finiteLineScheme M, finiteLineStructureMap M, finiteLine_smoothness M,
    ⟨2 * M - 1, finiteLineEmbedding M, finiteLine_closedImmersion M,
      finiteLineEmbedding_over_base M⟩⟩

/-- **THE WORLD-GATE IDENTIFICATIONS** — the law module's `hWX` gate
discharges by `rfl` at the actual world. -/
theorem finiteLineWorld_hWX (M : ℕ) [NeZero M] :
    (finiteLineWorld M).X = finiteLineScheme M := rfl

/-- **THE WORLD-GATE STRUCTURE-MAP IDENTIFICATION** — the law module's
`hWmap` gate discharges by `rfl` at the actual world. -/
theorem finiteLineWorld_hWmap (M : ℕ) [NeZero M]
    (hWX : (finiteLineWorld M).X = finiteLineScheme M) :
    hWX ▸ (finiteLineWorld M).structureMap = finiteLineStructureMap M := rfl

/-- The world's smoothness receipt (the F3 field, exported). -/
theorem finiteLineWorld_smooth (M : ℕ) [NeZero M] :
    Smooth (finiteLineWorld M).structureMap :=
  (finiteLineWorld M).smooth

/-- The world's projective witness (the F2 field, exported). -/
theorem finiteLineWorld_projective (M : ℕ) [NeZero M] :
    ∃ n : ℕ, ∃ f : (finiteLineWorld M).X ⟶ projectiveSpace n,
      IsClosedImmersion f ∧
        f ≫ projectiveSpaceToBase n = (finiteLineWorld M).structureMap :=
  exists_closed_projective_embedding (finiteLineWorld M)

/-! ## Receipts -/

#check gradedZeroHom
#check fromZeroRingHom_comp_awayMap
#check Proj_map_comp_toSpecZero
#check lineGradedQuotientHom_gradedZero_algebraMap
#check lineRotateGraded_gradedZero_algebraMap
#check finiteLineEmbedding_over_base
#check finiteLineCycle_over_base
#check finiteLineWorld
#check finiteLineWorld_hWX
#check finiteLineWorld_hWmap

#print axioms fromZeroRingHom_comp_awayMap
#print axioms Proj_map_comp_toSpecZero
#print axioms finiteLineEmbedding_over_base
#print axioms finiteLineCycle_over_base
#print axioms finiteLineWorld
#print axioms finiteLineWorld_hWX
#print axioms finiteLineWorld_hWmap

end GSTFiniteLineOverBase
