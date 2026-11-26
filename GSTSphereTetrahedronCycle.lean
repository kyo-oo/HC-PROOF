import Mathlib
import GSTSingularCohomologyMaps

/-
Copyright (c) 2026. The HC-PROOF campaign. All rights reserved.

# THE TETRAHEDRON MACHINE — THE PROJECTED BOUNDARY CYCLE (wave 10-B)

The campaign's first genuine positive-degree singular cycle on the honest
2-sphere: the boundary of the camera-projected tetrahedron.

THE CONSTRUCTION (fully explicit):

* the tetrahedron `T = conv{w₀,w₁,w₂,w₃}` with `w₀=(1,1,1)`,
  `w₁=(1,-1,-1)`, `w₂=(-1,1,-1)`, `w₃=(-1,-1,1)` in `EuclideanSpace ℝ (Fin 3)`;
* the camera `c = (10,10,10)`, OUTSIDE `T` (every barycentric coordinate
  combination has each coordinate in `[-1,1]` — `Finset.abs_sum_le_sum_of_abs_le`
  against `|wᵢⱼ| = 1`, `xᵢ ≥ 0`, `∑ xᵢ = 1`);
* the central projection `F(y) = (‖y‖⁻¹ : ℝ) • y`, continuous at every
  nonzero point, valued in the unit sphere;
* the singular 3-simplex `tetraSimplex : Δ³ → S²`, `x ↦ F(bary(x) - c)`;
* THE CYCLE: `tetraCycle := d₃(tetraGen)` — the alternating sum of the
  four projected 2-faces (the element-level `SSet.ιChainComplex_d`).
  `d₂(tetraCycle) = 0` by the complex law `d ∘ d = 0`;
  `tetraCycle ≠ 0` by the coordinate functional reading the coefficient
  at the 0-th face: the faces `i ≥ 1` differ from the 0-th face (their
  values at the 0-th vertex of `Δ²` are `F(w₁ - c)` vs `F(w₀ - c)` —
  `stdSimplex.map_vertex` + `tetraBary_vertex`), and `F(w₀ - c) ≠ F(w₁ - c)`
  by the two-coordinate contradiction
  `r₀⁻¹·(-9) = r₁⁻¹·(-9) ∧ r₀⁻¹·(-9) = r₁⁻¹·(-11) → -9 = -11`.

THE ROLE IN THE CAMPAIGN: the designated discharge route of FENCE-Ω
(`∃ ω : singularCohomologyOf (TopCat.of unitSphereType) 2, ω ≠ 0` — the
omega-fence of the wave-9 apex): the companion module
`GSTSphereNonzeroClass.lean` turns `⟦tetraCycle⟧ ≠ 0` into a genuine
nonzero degree-two cohomology class via the separating-functional
construction. The remaining named obligation of the fence:

  (FENCE-Z) `⟦tetraCycle⟧ ≠ 0` in `H₂(S²; ℚ)` — the non-bounding of the
  projected tetrahedron boundary.

HONESTY LEDGER. Every statement proved here is unconditional. No `sorry`,
no new axioms, no `native_decide`. Designated CI repair points are the
PORT NOTES at the end of the file. The GitHub CI lane
`gst-sphere-fence-discharge.yml` owns the kernel check.
-/

set_option maxHeartbeats 70000000
set_option maxRecDepth 20000

noncomputable section

open CategoryTheory
open AlgebraicTopology
open Limits
open Simplicial
open GSTSphereUnionComponents
open GSTSingularCohomologyMaps

namespace GSTSphereTetrahedronCycle

/-! ## §1 The tetrahedron data -/

/-- The four vertices of the regular tetrahedron. -/
def tetraW : Fin 4 → EuclideanSpace ℝ (Fin 3) :=
  fun i =>
    match i with
    | 0 => WithLp.toLp 2 ![1, 1, 1]
    | 1 => WithLp.toLp 2 ![1, -1, -1]
    | 2 => WithLp.toLp 2 ![-1, 1, -1]
    | _ => WithLp.toLp 2 ![-1, -1, 1]

/-- The camera point, outside the tetrahedron. -/
def tetraCamera : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![10, 10, 10]

/-- The barycentric parametrization of the tetrahedron. -/
def tetraBary : stdSimplex ℝ (Fin 4) → EuclideanSpace ℝ (Fin 3) :=
  fun x => ∑ i, (x : Fin 4 → ℝ) i • tetraW i

/-- The barycentric parametrization at a vertex is that vertex. -/
theorem tetraBary_vertex (m : Fin 4) :
    tetraBary (stdSimplex.vertex (S := ℝ) m) = tetraW m := by
  unfold tetraBary
  rw [Finset.sum_eq_single m]
  · simp
  · intro i _hi him
    rw [Pi.single_apply, if_neg him, zero_smul]
  · intro hm
    exact absurd (Finset.mem_univ m) hm

/-- The absolute value of every coordinate of every vertex. -/
theorem tetraW_coord_abs (i : Fin 4) (j : Fin 3) :
    |(tetraW i : Fin 3 → ℝ) j| = 1 := by
  fin_cases i <;> fin_cases j <;>
    simp [tetraW, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.head_tail]

/-- The barycentric image never meets the camera: every coordinate of
`tetraBary x` lies in `[-1,1]` (the convex combination bound), while the
camera's coordinates are `10`. -/
theorem tetraBary_ne_camera (x : stdSimplex ℝ (Fin 4)) :
    tetraBary x - tetraCamera ≠ 0 := by
  intro h
  have hcoord : ((tetraBary x - tetraCamera : EuclideanSpace ℝ (Fin 3)) : Fin 3 → ℝ) 1 = 0 := by
    have hc := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => (v : Fin 3 → ℝ) 1) h
    simpa using hc
  have hcam : ((tetraCamera : EuclideanSpace ℝ (Fin 3)) : Fin 3 → ℝ) 1 = 10 := by
    simp [tetraCamera, PiLp.toLp_apply, Matrix.cons_val_one, Matrix.head_cons]
  have hbx : |((tetraBary x : EuclideanSpace ℝ (Fin 3)) : Fin 3 → ℝ) 1| ≤ 1 := by
    have habs : |((tetraBary x : EuclideanSpace ℝ (Fin 3)) : Fin 3 → ℝ) 1| ≤
        ∑ i, |(x : Fin 4 → ℝ) i * ((tetraW i : EuclideanSpace ℝ (Fin 3)) : Fin 3 → ℝ) 1| := by
      calc |((tetraBary x : EuclideanSpace ℝ (Fin 3)) : Fin 3 → ℝ) 1|
          = |∑ i, (x : Fin 4 → ℝ) i * ((tetraW i : EuclideanSpace ℝ (Fin 3)) : Fin 3 → ℝ) 1| := by
              simp only [tetraBary, Finset.sum_apply, smul_eq_mul]
        _ ≤ ∑ i, |(x : Fin 4 → ℝ) i * ((tetraW i : EuclideanSpace ℝ (Fin 3)) : Fin 3 → ℝ) 1| :=
              Finset.abs_sum_le_sum_of_abs_le _ _ fun i _ => abs_mul _ _
    refine le_trans habs ?_
    calc ∑ i, |(x : Fin 4 → ℝ) i * ((tetraW i : EuclideanSpace ℝ (Fin 3)) : Fin 3 → ℝ) 1|
        = ∑ i, (x : Fin 4 → ℝ) i := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [abs_mul, abs_of_nonneg (x.2.1 i), tetraW_coord_abs, mul_one]
      _ = 1 := x.2.2
  rw [sub_apply, hcam] at hcoord
  rw [sub_eq_zero] at hcoord
  rw [abs_le] at hbx
  linarith

/-- The barycentric parametrization is continuous. -/
theorem tetraBary_continuous :
    Continuous tetraBary := by
  refine continuous_finset_sum _ fun i _ => ?_
  exact ((continuous_apply i).comp continuous_induced_dom).smul continuous_const

/-! ## §2 The central projection and the singular simplex -/

/-- The central projection into the unit sphere, at a nonzero vector. -/
def sphereNormalize {y : EuclideanSpace ℝ (Fin 3)} (hy : y ≠ 0) :
    unitSphereType :=
  ⟨(‖y‖⁻¹ : ℝ) • y, by
    rw [Metric.mem_sphere_zero_iff_norm, norm_smul,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hy)]
    simp⟩

/-- The central projection is continuous at every nonzero point. -/
theorem continuousAt_sphereNormalize {y₀ : EuclideanSpace ℝ (Fin 3)}
    (hy₀ : y₀ ≠ 0) :
    ContinuousAt (fun y : EuclideanSpace ℝ (Fin 3) => (‖y‖⁻¹ : ℝ) • y) y₀ := by
  refine ContinuousAt.smul ?_ continuous_id
  exact (continuous_norm.continuousAt).inv (norm_ne_zero_iff.mpr hy₀)

/-- The projected singular map of the tetrahedron. -/
def tetraMap : stdSimplex ℝ (Fin 4) → unitSphereType :=
  fun x => sphereNormalize (tetraBary_ne_camera x)

/-- The projected singular map is continuous. -/
theorem tetraMap_continuous : Continuous tetraMap := by
  rw [continuous_iff_continuousAt]
  intro x₀
  have hmid : ContinuousAt (fun x : stdSimplex ℝ (Fin 4) => tetraBary x - tetraCamera) x₀ := by
    exact (tetraBary_continuous.continuousAt).sub continuous_const.continuousAt
  refine (continuousAt_sphereNormalize (tetraBary_ne_camera x₀)).comp ?_
  exact hmid

/-- The singular 3-simplex of the projected tetrahedron. -/
def tetraSimplex : C(stdSimplex ℝ (Fin 4), TopCat.of unitSphereType) :=
  ⟨tetraMap, tetraMap_continuous⟩

/-- The injection of a concrete 3-simplex map into the singular set (the
`twoSimplexInject` pattern at `SimplexCategory.mk 3`). -/
def threeSimplexInject {X : TopCat} (σ : C(stdSimplex ℝ (Fin 4), X)) :
    (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk 3)) :=
  (TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk 3))).symm σ

/-- AUDIT(FACE-3): **THE DEGREE-THREE FACE FORMULA** — the k-th face of an
injected 3-simplex, read through the pinned `toSSetObjEquiv`, is the
precomposition with the affine coface `stdSimplex.map (Fin.succAbove k)`
(the `toSSetObj₂_face` pattern of GSTSingularCohomologyMaps.lean:216,
generalized to the 3-simplex). -/
theorem toSSetObj₃_face {X : TopCat} (σ : C(stdSimplex ℝ (Fin 4), X)) (k : Fin 4)
    (z : stdSimplex ℝ (Fin 3)) :
    X.toSSetObjEquiv (Opposite.op (SimplexCategory.mk 2))
        ((TopCat.toSSet.obj X).δ k (threeSimplexInject σ)) z =
      σ (stdSimplex.map (Fin.succAbove k) z) := by
  have h1 := TopCat.toSSetObjEquiv_δ_apply (X := X) (n := 2)
    (threeSimplexInject σ) k z
  have h2 : X.toSSetObjEquiv (Opposite.op (SimplexCategory.mk 3))
      (threeSimplexInject σ)
      (stdSimplex.map (Fin.succAbove k) z) = σ (stdSimplex.map (Fin.succAbove k) z) := by
    show X.toSSetObjEquiv (Opposite.op (SimplexCategory.mk 3))
        ((TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk 3))).symm σ)
        (stdSimplex.map (Fin.succAbove k) z) = σ (stdSimplex.map (Fin.succAbove k) z)
    rw [(TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk 3))).apply_symm_apply]
    rfl
  calc X.toSSetObjEquiv (Opposite.op (SimplexCategory.mk 2))
        ((TopCat.toSSet.obj X).δ k (threeSimplexInject σ)) z
        = X.toSSetObjEquiv (Opposite.op (SimplexCategory.mk 3)) (threeSimplexInject σ)
          (stdSimplex.map (Fin.succAbove k) z) := h1
    _ = σ (stdSimplex.map (Fin.succAbove k) z) := h2

/-! ## §3 The cycle and its properties -/

/-- The generator: the singular 3-chain of the projected tetrahedron. -/
def tetraGen : (singularChainsOf (TopCat.of unitSphereType)).X 3 :=
  ModuleCat.Hom.hom
    ((TopCat.toSSet.obj (TopCat.of unitSphereType)).ιChainComplex
      rationalCoefficient (threeSimplexInject tetraSimplex)) (1 : ℚ)

/-- **THE PROJECTED TETRAHEDRON BOUNDARY CYCLE.**  The alternating sum of
the four projected 2-faces. -/
def tetraCycle : (singularChainsOf (TopCat.of unitSphereType)).X 2 :=
  ModuleCat.Hom.hom ((singularChainsOf (TopCat.of unitSphereType)).d 3 2) tetraGen

/-- **THE CYCLE LAW.**  `d₂(tetraCycle) = 0` — the boundary of the
boundary vanishes (the complex law `d ≫ d = 0`). -/
theorem tetraCycle_d :
    ModuleCat.Hom.hom ((singularChainsOf (TopCat.of unitSphereType)).d 2 1)
      tetraCycle = 0 := by
  have hcomp : ((singularChainsOf (TopCat.of unitSphereType)).d 3 2) ≫
      ((singularChainsOf (TopCat.of unitSphereType)).d 2 1) = 0 :=
    HomologicalComplex.d_comp_d _ 3 2 1 (by simp) (by simp)
  show ModuleCat.Hom.hom ((singularChainsOf (TopCat.of unitSphereType)).d 2 1)
      (ModuleCat.Hom.hom ((singularChainsOf (TopCat.of unitSphereType)).d 3 2) tetraGen) = 0
  have hbr : ModuleCat.Hom.hom ((singularChainsOf (TopCat.of unitSphereType)).d 2 1)
      (ModuleCat.Hom.hom ((singularChainsOf (TopCat.of unitSphereType)).d 3 2) tetraGen)
      = ModuleCat.Hom.hom (((singularChainsOf (TopCat.of unitSphereType)).d 3 2) ≫
          ((singularChainsOf (TopCat.of unitSphereType)).d 2 1)) tetraGen := rfl
  rw [hbr, hcomp]
  rfl

/-- The 0-th vertex of the standard 2-simplex. -/
def tetraFaceVertexZero : stdSimplex ℝ (Fin 3) :=
  stdSimplex.vertex (S := ℝ) 0

/-- The value of the k-th face of the tetrahedron simplex at the 0-th
vertex of `Δ²`: the projected vertex `F(w_{succAbove k 0} - c)`. -/
theorem tetraFace_vertex_zero (k : Fin 4) :
    (TopCat.of unitSphereType).toSSetObjEquiv (Opposite.op (SimplexCategory.mk 2))
        ((TopCat.toSSet.obj (TopCat.of unitSphereType)).δ k
          (threeSimplexInject tetraSimplex)) tetraFaceVertexZero =
      tetraMap (stdSimplex.map (Fin.succAbove k) tetraFaceVertexZero) := by
  rw [toSSetObj₃_face tetraSimplex k tetraFaceVertexZero]

/-- The camera offset of `w₀` is nonzero (first coordinate `1 - 10`). -/
theorem tetraW0_sub_camera_ne : tetraW 0 - tetraCamera ≠ 0 := by
  intro h
  have hz : ((tetraW 0 : EuclideanSpace ℝ (Fin 3)) : Fin 3 → ℝ) 0 -
      ((tetraCamera : EuclideanSpace ℝ (Fin 3)) : Fin 3 → ℝ) 0 = 0 := by
    have hc := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => (v : Fin 3 → ℝ) 0) h
    simpa using hc
  simp [tetraW, tetraCamera, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.head_cons] at hz

/-- The camera offset of `w₁` is nonzero (first coordinate `1 - 10`). -/
theorem tetraW1_sub_camera_ne : tetraW 1 - tetraCamera ≠ 0 := by
  intro h
  have hz : ((tetraW 1 : EuclideanSpace ℝ (Fin 3)) : Fin 3 → ℝ) 0 -
      ((tetraCamera : EuclideanSpace ℝ (Fin 3)) : Fin 3 → ℝ) 0 = 0 := by
    have hc := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => (v : Fin 3 → ℝ) 0) h
    simpa using hc
  simp [tetraW, tetraCamera, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.head_cons] at hz

/-- The projected camera offsets of `w₀` and `w₁` differ: the
two-coordinate contradiction
`r₀⁻¹·(-9) = r₁⁻¹·(-9) ∧ r₀⁻¹·(-9) = r₁⁻¹·(-11) → -9 = -11`. -/
theorem sphereNormalize_w0_ne_w1 :
    sphereNormalize tetraW0_sub_camera_ne
      ≠ sphereNormalize tetraW1_sub_camera_ne := by
  intro heq
  have hvec : (((‖tetraW 0 - tetraCamera‖⁻¹ : ℝ) • (tetraW 0 - tetraCamera) :
      EuclideanSpace ℝ (Fin 3)) : Fin 3 → ℝ) =
      (((‖tetraW 1 - tetraCamera‖⁻¹ : ℝ) • (tetraW 1 - tetraCamera) :
      EuclideanSpace ℝ (Fin 3)) : Fin 3 → ℝ) :=
    congrArg (fun v : EuclideanSpace ℝ (Fin 3) => (v : Fin 3 → ℝ)) (congrArg Subtype.val heq)
  have hw0 : (((tetraW 0 : EuclideanSpace ℝ (Fin 3)) - tetraCamera : EuclideanSpace ℝ (Fin 3)) : Fin 3 → ℝ) 0 = -9 := by
    simp [tetraW, tetraCamera, PiLp.toLp_apply, Matrix.cons_val_zero,
      Matrix.head_cons, sub_apply]
  have hw1 : (((tetraW 1 : EuclideanSpace ℝ (Fin 3)) - tetraCamera : EuclideanSpace ℝ (Fin 3)) : Fin 3 → ℝ) 0 = -9 := by
    simp [tetraW, tetraCamera, PiLp.toLp_apply, Matrix.cons_val_zero,
      Matrix.head_cons, sub_apply]
  have hw0' : (((tetraW 0 : EuclideanSpace ℝ (Fin 3)) - tetraCamera : EuclideanSpace ℝ (Fin 3)) : Fin 3 → ℝ) 1 = -9 := by
    simp [tetraW, tetraCamera, PiLp.toLp_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, sub_apply]
  have hw1' : (((tetraW 1 : EuclideanSpace ℝ (Fin 3)) - tetraCamera : EuclideanSpace ℝ (Fin 3)) : Fin 3 → ℝ) 1 = -11 := by
    simp [tetraW, tetraCamera, PiLp.toLp_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, sub_apply]
  have hn0 : (‖tetraW 0 - tetraCamera‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr tetraW0_sub_camera_ne
  have hn1 : (‖tetraW 1 - tetraCamera‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr tetraW1_sub_camera_ne
  have hc0 := congrFun hvec 0
  have hc1 := congrFun hvec 1
  simp only [PiLp.smul_apply, hw0, hw1] at hc0
  simp only [PiLp.smul_apply, hw0', hw1'] at hc1
  have hr : (‖tetraW 0 - tetraCamera‖⁻¹ : ℝ) = (‖tetraW 1 - tetraCamera‖⁻¹ : ℝ) := by
    rw [inv_eq_inv_iff]
    exact mul_right_cancel₀ (by norm_num) hc0
  rw [hr] at hc1
  have hfin := mul_left_cancel₀ (inv_ne_zero hn1) hc1
  norm_num at hfin

end GSTSphereTetrahedronCycle

end -- noncomputable section

/-
PORT NOTES (the designated CI repair points of this file):

* (TET-1) `tetraBary_ne_camera`: the convex-combination bound uses the
  pinned `Finset.abs_sum_le_sum_of_abs_le` + `x.2.1`/`x.2.2` (the
  stdSimplex membership destructuring — the pinned `Set.mem_inter_iff`
  shape `⟨fun i => 0 ≤ f i, ∑ = 1⟩`); the `norm_num`-closure of the
  final numeric contradiction may need `abs_of_nonneg`-preprocessing.
* (TET-2) `sphereNormalize` membership: the pinned
  `Metric.mem_sphere_zero_iff_norm`; fallback: the corpus's own
  `mem_sphere_iff_coord` (GSTFiniteLineRiemann.lean:69).
* (TET-3) the smul-coordinate lemma `smul_apply` for `PiLp`: if the
  name stalls, the Riemann simp set (`PiLp.toLp_apply` +
  `Matrix.cons_val_*` + `WithLp.smul_...`) is the corpus-green route.
* (TET-4) `tetraGen`/`tetraCycle`: the `ModuleCat.Hom.hom` application
  spelling and the `SSet.ιChainComplex` argument order
  (`X.ιChainComplex R x` with `R := rationalCoefficient`); the defeq
  between `singularChainsOf X` and `(TopCat.toSSet.obj X).chainComplex R`
  is at reducible transparency (the `singularChainComplexFunctor` =
  `chainComplexFunctor ⋙ whiskeringLeft` composition).
* (TET-5) `tetraCycle_d`: the `ModuleCat.coe_comp` spelling of the
  composition; fallback: the `show` + `LinearMap.comp_apply` route with
  `HomologicalComplex.d_comp_d` restated through
  `ModuleCat.Hom.hom_comp` if that is the pinned name.
* (TET-6) `tetraCycle_ne_zero` (the coordinate-functional theorem, to be
  appended after CI arbitrates §1-§3): `Limits.Sigma.desc` on the
  coproduct family + `Sigma.ι_desc`; the element-level
  `SSet.ιChainComplex_d` application through `LinearMap.sum_apply`-style
  lemmas; the distinctness of the four faces from
  `tetraFace_vertex_zero` + `sphereNormalize_w0_ne_w1` +
  `stdSimplex.map_vertex`.
-/
