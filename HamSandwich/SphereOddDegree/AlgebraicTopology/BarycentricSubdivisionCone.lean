import HamSandwich.SphereOddDegree.AlgebraicTopology.BarycentricBoundaryCancellation
import HamSandwich.SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionChainMap
import Mathlib

/-!
# The cone operator for the barycentric subdivision homotopy

This file defines the affine **cone over a point** construction at the level of
the topological standard simplices, bundles it as a continuous map, extends it to
singular chains of `Δⁿ`, and proves the boundary identity

```text
∂ Cone_v(c) = c - Cone_v(∂ c)
```

in the exact degree-indexed form needed for the recursive proof that barycentric
subdivision is chain-homotopic to the identity.

For a point `v : Δⁿ` and a (continuous) `k`-simplex `τ : Δᵏ → Δⁿ`, the cone
`Cone_v(τ) : Δᵏ⁺¹ → Δⁿ` sends the new apex vertex to `v` and the remaining
vertices to the vertices of `τ`.  In barycentric coordinates, writing
`x = (t, x₁, …, x_{k+1})` for a point of `Δᵏ⁺¹`,

```text
Cone_v(τ)(x) = t · v + (1 - t) · τ( x₁/(1-t), …, x_{k+1}/(1-t) )
```

away from `t = 1`, and `= v` at `t = 1` (the apex).

This file does **not** assert the barycentric subdivision homotopy itself; it only
builds the cone operator and its boundary formula.

STRIKE 18 (run 46161630202 receipt): the v4.28-era proofs of ten theorems of this
file died at the v4.33-rc2 pin through coe-display drift in `simpa`, ambiguous
`|·|` elaboration, `convert`-leftover metavariables, filter/setOf pattern drift
in `rw`, and `Fin.sum_univ_*` rewrites firing on non-normalized numerals.  The
rebuilds below follow the campaign's pin discipline: every name pin-verified
(`stdSimplex.map_coe`, `FunOnFinite.linearMap_apply_apply`,
`Fin.succ_succAbove_succ`, `Fin.succ_succAbove_zero`, `Sigma.ι_desc`,
`ModuleCat.hom_comp`-family rfl-bridges), every fiber computation in the
coordinate style of the green sibling `BarycentricBoundaryCancellation.lean`,
and the generator-level lifts in the green sibling's `Sigma.hom_ext` +
`convert … using 1` + `rfl` shape (the strike-15 receipt, run 46159201696).
-/

open scoped BigOperators
open CategoryTheory AlgebraicTopology Simplicial SimplexCategory Limits
open Finset

namespace SphereOddDegree
namespace AffineBarycentricSubdivision

/-! ## 1. The normalized tail of a point of `Δᵏ⁺¹` -/

/-- The (un-normalized) coordinate function of the normalized tail of a point
`x : Δᵏ⁺¹`: the `i`-th coordinate is `x_{i+1} / (1 - x₀)`.  (Lean's `/0 = 0`
convention makes this total; the genuine simplex point is `coneTail` below.) -/
noncomputable def coneTailFun {k : ℕ} (x : Delta (k + 1)) : Fin (k + 1) → ℝ :=
  fun i => (x : Fin (k + 1 + 1) → ℝ) i.succ / (1 - (x : Fin (k + 1 + 1) → ℝ) 0)

/-
When `x₀ ≠ 1`, the normalized tail coordinates form a genuine point of `Δᵏ`.
-/
theorem coneTailFun_mem {k : ℕ} (x : Delta (k + 1))
    (hx : (x : Fin (k + 1 + 1) → ℝ) 0 ≠ 1) :
    coneTailFun x ∈ stdSimplex ℝ (Fin (k + 1)) := by
  refine' ⟨ fun i => _, _ ⟩;
  · exact div_nonneg ( x.2.1 _ ) ( sub_nonneg.2 ( by
      have hle := Finset.single_le_sum (fun a _ => x.2.1 a) (Finset.mem_univ (0 : Fin (k + 1 + 1)))
      have hsum : ∑ i : Fin (k + 1 + 1), (x : Fin (k + 1 + 1) → ℝ) i = 1 := x.2.2
      rw [Fin.sum_univ_succ] at hsum
      linarith ) );
  · have h_sum : ∑ i : Fin (k + 1), (x : Fin (k + 1 + 1) → ℝ) i.succ = 1 - (x : Fin (k + 1 + 1) → ℝ) 0 := by
      have hsum : (x : Fin (k + 1 + 1) → ℝ) 0 + ∑ i : Fin (k + 1), (x : Fin (k + 1 + 1) → ℝ) i.succ = 1 := by
        have h := x.2.2
        rw [Fin.sum_univ_succ] at h
        exact h
      linarith
    unfold coneTailFun;
    rw [ ← Finset.sum_div, h_sum, div_self ( sub_ne_zero_of_ne <| Ne.symm hx ) ]

/-- The normalized tail of `x : Δᵏ⁺¹`, as a point of `Δᵏ`.  Away from the apex
(`x₀ = 1`) it is the genuine normalized tail; at the apex it is given an
irrelevant fallback value. -/
noncomputable def coneTail {k : ℕ} (x : Delta (k + 1)) : Delta k :=
  if h : (x : Fin (k + 1 + 1) → ℝ) 0 = 1 then stdSimplex.vertex (0 : Fin (k + 1))
  else ⟨coneTailFun x, coneTailFun_mem x h⟩

/-
Coordinate formula for `coneTail` away from the apex.
-/
theorem coneTail_apply {k : ℕ} (x : Delta (k + 1))
    (hx : (x : Fin (k + 1 + 1) → ℝ) 0 ≠ 1) (i : Fin (k + 1)) :
    (coneTail x : Fin (k + 1) → ℝ) i
      = (x : Fin (k + 1 + 1) → ℝ) i.succ / (1 - (x : Fin (k + 1 + 1) → ℝ) 0) := by
  unfold coneTail; aesop;

/-! ## 2. The affine cone map -/

/-- The coordinate function of the cone of `τ` over `v` at the point `x`. -/
noncomputable def affineConeMapFun {n k : ℕ} (v : Delta n) (τ : Delta k → Delta n)
    (x : Delta (k + 1)) : Fin (n + 1) → ℝ :=
  fun j => (x : Fin (k + 1 + 1) → ℝ) 0 * (v : Fin (n + 1) → ℝ) j
      + (1 - (x : Fin (k + 1 + 1) → ℝ) 0) * ((τ (coneTail x)) : Fin (n + 1) → ℝ) j

/-
The cone coordinate function always defines a point of `Δⁿ`.
-/
theorem affineConeMapFun_mem {n k : ℕ} (v : Delta n) (τ : Delta k → Delta n)
    (x : Delta (k + 1)) : affineConeMapFun v τ x ∈ stdSimplex ℝ (Fin (n + 1)) := by
  refine' ⟨ fun j => _, _ ⟩;
  · exact add_nonneg ( mul_nonneg ( stdSimplex.zero_le x 0 ) ( stdSimplex.zero_le v j ) ) ( mul_nonneg ( sub_nonneg.mpr ( stdSimplex.le_one x 0 ) ) ( stdSimplex.zero_le ( τ ( coneTail x ) ) j ) );
  · unfold affineConeMapFun;
    simp +decide [ Finset.sum_add_distrib, ← Finset.mul_sum _ _ _, ← Finset.sum_mul, stdSimplex.sum_eq_one ]

/-- **The affine cone map** `Cone_v(τ) : Δᵏ⁺¹ → Δⁿ`. -/
noncomputable def affineConeMap {n k : ℕ} (v : Delta n) (τ : Delta k → Delta n) :
    Delta (k + 1) → Delta n :=
  fun x => ⟨affineConeMapFun v τ x, affineConeMapFun_mem v τ x⟩

@[simp] theorem affineConeMap_coord {n k : ℕ} (v : Delta n) (τ : Delta k → Delta n)
    (x : Delta (k + 1)) (j : Fin (n + 1)) :
    (affineConeMap v τ x : Fin (n + 1) → ℝ) j
      = (x : Fin (k + 1 + 1) → ℝ) 0 * (v : Fin (n + 1) → ℝ) j
        + (1 - (x : Fin (k + 1 + 1) → ℝ) 0) * ((τ (coneTail x)) : Fin (n + 1) → ℝ) j := rfl

/-! ## 3. Vertex formulas -/

/-
The cone sends the apex vertex `0` to `v`.
-/
theorem affineConeMap_vertex_zero {n k : ℕ} (v : Delta n) (τ : Delta k → Delta n) :
    affineConeMap v τ (stdSimplex.vertex (0 : Fin (k + 1 + 1))) = v := by
  unfold affineConeMap; simp +decide [ stdSimplex.vertex ] ;
  unfold affineConeMapFun; simp +decide [ Fin.ext_iff, Pi.single_apply ] ;
  rfl

/-
The cone sends the vertex `i+1` to the vertex `τ(i)` of `τ`.
-/
theorem affineConeMap_vertex_succ {n k : ℕ} (v : Delta n) (τ : Delta k → Delta n)
    (i : Fin (k + 1)) :
    affineConeMap v τ (stdSimplex.vertex i.succ) = τ (stdSimplex.vertex i) := by
  ext j;
  rw [ affineConeMap_coord ] ; simp +decide [ Fin.succ_ne_zero ];
  congr;
  ext j; simp +decide [ coneTail_apply, stdSimplex.vertex ] ;
  simp +decide [ Pi.single_apply, Fin.ext_iff ]

/-! ## 4. Continuity and the bundled continuous cone map -/

/-
`coneTail` is continuous away from the apex.
-/
theorem continuousOn_coneTail {k : ℕ} :
    ContinuousOn (coneTail (k := k))
      (setOf fun x : Delta (k + 1) => x 0 ≠ (1 : ℝ)) := by
  -- Write `S := {x : Delta (k+1) | (x:_) 0 ≠ 1}`.
  set S : Set (Delta (k + 1)) := {x | x 0 ≠ 1};
  have h_cont_tail : ContinuousOn (fun x : Delta (k + 1) => (coneTail x : Fin (k + 1) → ℝ)) S := by
    refine' ContinuousOn.congr _ _;
    exact fun x i => ( x : Fin ( k + 1 + 1 ) → ℝ ) i.succ / ( 1 - ( x : Fin ( k + 1 + 1 ) → ℝ ) 0 );
    · exact continuousOn_pi.mpr fun i => ContinuousOn.div ( continuous_apply _ |> Continuous.comp_continuousOn <| continuous_subtype_val.continuousOn ) ( continuousOn_const.sub <| continuous_apply _ |> Continuous.comp_continuousOn <| continuous_subtype_val.continuousOn ) fun x hx => sub_ne_zero_of_ne <| Ne.symm hx;
    · intro x hx; ext i; exact coneTail_apply x hx i;
  rw [ continuousOn_iff_continuous_restrict ] at *;
  exact continuous_induced_rng.mpr h_cont_tail

/-
The cone of a continuous `τ` over `v` is continuous.
-/
theorem continuous_affineConeMap {n k : ℕ} (v : Delta n) (τ : C(Delta k, Delta n)) :
    Continuous (affineConeMap v (⇑τ)) := by
  refine' continuous_induced_rng.mpr _;
  refine' continuous_pi fun j => _;
  -- The function $B(x) = (1 - x 0) * ((τ (coneTail x)) j)$ is continuous because
  -- it is a product of continuous functions.
  have hB_cont : Continuous (fun x : Delta (k + 1) => (1 - x 0) * ((τ (coneTail x)) j)) := by
    refine' continuous_iff_continuousAt.mpr _;
    intro x;
    by_cases hx : x 0 = 1;
    · refine' tendsto_iff_norm_sub_tendsto_zero.mpr _;
      -- STRIKE 18: the ambiguous `|1 - e 0|` elaboration (SSet.toTop.obj vs
      -- ℝ-abs) is eliminated by the named continuity `have` with fully-ascribed
      -- subterms, and the `Continuous.tendsto'` metavars are supplied
      -- explicitly (x and 0), so the apex-value proof is `rw [hx]; simp`.
      have h_abs : Continuous fun e : Delta (k + 1) =>
          |(1 : ℝ) - (e : Fin (k + 1 + 1) → ℝ) 0| :=
        Continuous.abs (continuous_const.sub
          ((continuous_apply 0).comp continuous_subtype_val))
      refine' squeeze_zero (fun _ => norm_nonneg _) (fun e => _) ?_;
      · exact mul_le_of_le_one_right ( abs_nonneg _ ) ( abs_le.mpr ⟨ by linarith [ stdSimplex.zero_le ( τ ( coneTail e ) ) j ], by linarith [ stdSimplex.le_one ( τ ( coneTail e ) ) j ] ⟩ );
      · have hT := h_abs.tendsto x
        rw [hx] at hT
        simpa using hT
    · refine' ContinuousAt.mul _ _;
      · exact ContinuousAt.sub continuousAt_const ( continuousAt_subtype_val.comp continuousAt_id |> ContinuousAt.comp ( continuousAt_apply _ _ ) );
      · refine' ContinuousAt.comp ( continuous_apply j |> Continuous.continuousAt ) _;
        refine' ContinuousAt.comp _ _;
        · exact Continuous.continuousAt ( by continuity );
        · refine' ContinuousAt.comp _ _;
          · exact τ.continuous.continuousAt;
          · exact ContinuousOn.continuousAt continuousOn_coneTail ( IsOpen.mem_nhds ( isOpen_compl_singleton.preimage ( continuous_apply 0 |> Continuous.comp <| continuous_subtype_val ) ) hx );
  -- STRIKE 18: the `convert … using 1` (which left a `?m` metavariable plus a
  -- bare `ℝ` goal at the pin) is replaced by the defeq `exact`: the goal's
  -- coordinate function is pointwise-`rfl` to the cone-coordinate formula
  -- (`affineConeMap_coord` is `rfl`), so `exact` unifies at default
  -- transparency.
  exact Continuous.add ( Continuous.mul ( continuous_apply 0 |> Continuous.comp <| continuous_subtype_val ) continuous_const ) hB_cont

/-- **The bundled continuous cone map** `Cone_v(τ) : C(Δᵏ⁺¹, Δⁿ)`. -/
noncomputable def affineConeContinuousMap {n k : ℕ} (v : Delta n) (τ : C(Delta k, Delta n)) :
    C(Delta (k + 1), Delta n) :=
  ⟨affineConeMap v (⇑τ), continuous_affineConeMap v τ⟩

@[simp] theorem affineConeContinuousMap_apply {n k : ℕ} (v : Delta n) (τ : C(Delta k, Delta n))
    (x : Delta (k + 1)) : affineConeContinuousMap v τ x = affineConeMap v (⇑τ) x := rfl

/-! ## 5. Face formulas -/

/-
**Face opposite the apex.** Restricting the cone along the `0`-th coface
recovers the base simplex `τ`.
-/
theorem cone_face_zero {n k : ℕ} (v : Delta n) (τ : Delta k → Delta n) :
    (fun y : Delta k => affineConeMap v τ (cofaceTop k 0 y)) = τ := by
  ext y j;
  rw [ affineConeMap_coord ];
  rw [ show ( cofaceTop k 0 ) y = stdSimplex.map ( S := ℝ ) ( Fin.succAbove 0 ) y from rfl ];
  rw [ show coneTail ( stdSimplex.map ( Fin.succAbove 0 ) y ) = y from _ ];
  · simp +decide [ stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply ];
  · ext i;
    convert coneTail_apply _ _ i using 1;
    · simp +decide [ stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply ];
      rw [ Finset.sum_eq_single i ] <;> aesop;
    · simp +decide [ stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply ]

/-
**Tail commutes with internal cofaces.** For `y` away from the apex, the
normalized tail of `cofaceTop (k+1) (j+1) y` is the `j`-th coface of the
normalized tail of `y`.
-/
theorem coneTail_cofaceTop_succ {k : ℕ} (j : Fin (k + 1 + 1)) (y : Delta (k + 1))
    (hy : (y : Fin (k + 1 + 1) → ℝ) 0 ≠ 1) :
    coneTail (cofaceTop (k + 1) j.succ y) = cofaceTop k j (coneTail y) := by
  -- STRIKE 18: the whole coordinate computation is rebuilt in the green
  -- sibling's fiber style (`stdSimplex.map_coe` +
  -- `FunOnFinite.linearMap_apply_apply` + `Finset.sum_eq_single`), replacing
  -- the v4.28 filter/setOf `rw` chain that no longer matches the pin's
  -- `Finset.filter` elaboration.
  -- The `0`-coordinate of the `(j+1)`-coface of `y` is `y 0`: the fiber of
  -- `j.succ.succAbove` over `0` is exactly `{0}`.
  have h0 : (cofaceTop (k + 1) j.succ y : Fin (k + 1 + 1 + 1) → ℝ) 0
      = (y : Fin (k + 1 + 1) → ℝ) 0 := by
    show (stdSimplex.map (S := ℝ) (Fin.succAbove j.succ) y : Fin (k + 1 + 1 + 1) → ℝ) 0
      = (y : Fin (k + 1 + 1) → ℝ) 0
    rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply,
      Finset.sum_eq_single (0 : Fin (k + 1 + 1))]
    · rw [Fin.succ_succAbove_zero j]
    · intro b hb hbt
      have hb2 : j.succ.succAbove b = 0 := (Finset.mem_filter.mp hb).2
      simp only [Fin.succAbove] at hb2
      split at hb2
      · exact (Fin.succ_ne_zero _ hb2).elim
      · exact hbt (Fin.val_eq_zero.mp (by
          have hb3 := congrArg Fin.val hb2
          simpa using hb3))
    · intro h
      exact (h (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Fin.succ_succAbove_zero j⟩)).elim
  -- The fiber of `j.succ.succAbove` over `i.succ` reindexes, through
  -- `Fin.succ_succAbove_succ`, to the fiber of `j.succAbove` over `i`.
  have hfib : ∑ m ∈ Finset.univ.filter
        (fun m : Fin (k + 1 + 1) => j.succ.succAbove m = i.succ), (y : Fin (k + 1 + 1) → ℝ) m
      = ∑ m ∈ Finset.univ.filter
        (fun m : Fin (k + 1) => j.succAbove m = i), (y : Fin (k + 1 + 1) → ℝ) m.succ := by
    refine' (Finset.sum_bij
      (fun (m : Fin (k + 1)) (_ : m ∈ Finset.univ.filter
        (fun m : Fin (k + 1) => j.succAbove m = i)) => m.succ) ?_ ?_ ?_ ?_).symm
    · intro m hm
      rw [Finset.mem_filter] at hm ⊢
      refine' ⟨Finset.mem_univ _, ?_⟩
      rw [Fin.succ_succAbove_succ]
      exact congrArg Fin.succ hm.2
    · intro m hm
      rfl
    · intro m₁ _ m₂ _ h
      exact Fin.succ_injective h
    · intro b hb
      rw [Finset.mem_filter] at hb
      have hb0 : b ≠ 0 := by
        intro h
        rw [h, Fin.succ_succAbove_zero] at hb
        exact (Fin.succ_ne_zero i hb.2).elim
      rcases Fin.exists_eq_succ_of_ne_zero hb0 with ⟨m, rfl⟩
      refine' ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
      rw [Fin.succ_succAbove_succ] at hb
      exact Fin.succ_injective hb.2
  ext i
  rw [coneTail_apply _ (by rw [h0]; exact hy), h0]
  have hL : (cofaceTop (k + 1) j.succ y : Fin (k + 1 + 1 + 1) → ℝ) i.succ
      = ∑ m ∈ Finset.univ.filter
        (fun m : Fin (k + 1 + 1) => j.succ.succAbove m = i.succ), (y : Fin (k + 1 + 1) → ℝ) m := by
    show (stdSimplex.map (S := ℝ) (Fin.succAbove j.succ) y : Fin (k + 1 + 1 + 1) → ℝ) i.succ = _
    rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  have hR : (cofaceTop k j (coneTail y) : Fin (k + 1 + 1) → ℝ) i
      = ∑ m ∈ Finset.univ.filter
        (fun m : Fin (k + 1) => j.succAbove m = i),
        ((y : Fin (k + 1 + 1) → ℝ) m.succ / (1 - (y : Fin (k + 1 + 1) → ℝ) 0)) := by
    show (stdSimplex.map (S := ℝ) (Fin.succAbove j) (coneTail y) : Fin (k + 1 + 1) → ℝ) i = _
    rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
    refine' Finset.sum_congr rfl fun m _ => _
    exact coneTail_apply y hy m
  rw [hL, hR, ← Finset.sum_div]
  congr 1
  exact hfib

/-
**Every other face.** Restricting the cone along the `(j+1)`-th coface gives
the cone over the `j`-th face of `τ`.
-/
theorem cone_face_succ {n k : ℕ} (v : Delta n) (τ : Delta (k + 1) → Delta n)
    (j : Fin (k + 1 + 1)) :
    (fun y : Delta (k + 1) => affineConeMap v τ (cofaceTop (k + 1) j.succ y))
      = (fun y : Delta (k + 1) => affineConeMap v (fun z : Delta k => τ (cofaceTop k j z)) y) := by
  funext y;
  ext c;
  by_cases hy : ( y : Fin ( k + 1 + 1 ) → ℝ ) 0 = 1 <;> simp_all +decide [ affineConeMap_coord, cofaceTop_eq ];
  · simp +decide [ cofaceTop, stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply, Fin.succ_succAbove_zero ];
    rw [ Finset.sum_eq_single 0 ] <;> simp_all +decide [ Fin.succ_succAbove_zero ];
    intro b hb hb'; rw [ Fin.succAbove ] at hb; aesop;
  · rw [ show ( cofaceTop ( k + 1 ) j.succ ) y 0 = y 0 from ?_, coneTail_cofaceTop_succ j y hy ];
    unfold cofaceTop; simp +decide [ stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply, Fin.succ_succAbove_zero ] ;
    rw [ Finset.sum_eq_single 0 ] <;> simp_all +decide [ Fin.succ_succAbove_zero ];
    intro b hb hb'; rw [ Fin.succAbove ] at hb; aesop;

/-! ## 6. The cone on singular simplices and chains of `Δⁿ` -/

/-- The cone of a singular `k`-simplex of `Δⁿ` over `v`, as a singular
`(k+1)`-simplex of `Δⁿ`. -/
noncomputable def coneSimplex (n k : ℕ) (v : Delta n)
    (σ : singularSimplices (TopCat.of (Delta n)) k) :
    singularSimplices (TopCat.of (Delta n)) (k + 1) :=
  continuousMapAsSingularSimplex (TopCat.of (Delta n)) (k + 1)
    (affineConeContinuousMap v (singularSimplexAsContinuousMap (TopCat.of (Delta n)) k σ))

/-- The continuous map underlying `coneSimplex`. -/
theorem coneSimplex_continuousMap (n k : ℕ) (v : Delta n)
    (σ : singularSimplices (TopCat.of (Delta n)) k) :
    singularSimplexAsContinuousMap (TopCat.of (Delta n)) (k + 1) (coneSimplex n k v σ)
      = affineConeContinuousMap v (singularSimplexAsContinuousMap (TopCat.of (Delta n)) k σ) := by
  rw [coneSimplex, singularSimplexAsContinuousMap, continuousMapAsSingularSimplex,
    Equiv.apply_symm_apply]

/-- The `0`-simplex with value `v` at every vertex. -/
noncomputable def constSimplex0 (n : ℕ) (v : Delta n) :
    singularSimplices (TopCat.of (Delta n)) 0 :=
  continuousMapAsSingularSimplex (TopCat.of (Delta n)) 0
    (ContinuousMap.const (Delta 0) v)

/-
**Apex face of `coneSimplex`.** The `0`-th boundary face of the cone of `σ`
is `σ`.
-/
theorem coneSimplex_face_zero (n k : ℕ) (v : Delta n)
    (σ : singularSimplices (TopCat.of (Delta n)) k) :
    AlexanderWhitney.faceSimplex (TopCat.of (Delta n)) k 0 (coneSimplex n k v σ) = σ := by
  -- STRIKE 18: the `convert congr_fun … |> congr_arg … using 1` scaffold (which
  -- left an unassigned-metavariable goal at the pin) is replaced by the
  -- green sibling's lift shape: rewrite through the pin-verified
  -- `faceSimplex_continuousMap`/`coneSimplex_continuousMap`, then close
  -- pointwise by `cone_face_zero` through the defeq comp/coe bridges.
  apply singularSimplices_ext
  rw [faceSimplex_continuousMap, coneSimplex_continuousMap]
  refine' ContinuousMap.ext fun a => _
  have h := cone_face_zero v (fun y => singularSimplexAsContinuousMap (TopCat.of (Delta n)) k σ y)
  exact congrFun h a

/-
**Internal faces of `coneSimplex`.** The `(j+1)`-th boundary face of the cone
of `σ` is the cone of the `j`-th boundary face of `σ`.
-/
theorem coneSimplex_face_succ (n k : ℕ) (v : Delta n)
    (σ : singularSimplices (TopCat.of (Delta n)) (k + 1)) (j : Fin (k + 1 + 1)) :
    AlexanderWhitney.faceSimplex (TopCat.of (Delta n)) (k + 1) j.succ (coneSimplex n (k + 1) v σ)
      = coneSimplex n k v (AlexanderWhitney.faceSimplex (TopCat.of (Delta n)) k j σ) := by
  -- STRIKE 18: same rebuild as `coneSimplex_face_zero`, through
  -- `cone_face_succ` pointwise.
  apply singularSimplices_ext
  rw [faceSimplex_continuousMap, coneSimplex_continuousMap, coneSimplex_continuousMap,
    faceSimplex_continuousMap]
  refine' ContinuousMap.ext fun a => _
  have h := cone_face_succ v
    (fun z => singularSimplexAsContinuousMap (TopCat.of (Delta n)) (k + 1) σ z) j
  exact congrFun h a

/-
**The second face of a 1-dimensional cone.** The `1`-st boundary face of the
cone of a `0`-simplex `σ` is the simplex with value `v` at every vertex.
-/
theorem coneSimplex_face_one_zero (n : ℕ) (v : Delta n)
    (σ : singularSimplices (TopCat.of (Delta n)) 0) :
    AlexanderWhitney.faceSimplex (TopCat.of (Delta n)) 0 1 (coneSimplex n 0 v σ)
      = constSimplex0 n v := by
  apply singularSimplices_ext;
  rw [ faceSimplex_continuousMap, coneSimplex_continuousMap ];
  ext y; simp [affineConeContinuousMap_apply, affineConeMap_coord];
  simp +decide [ cofaceTop, stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply ];
  simp +decide [ Finset.filter_singleton, Fin.succAbove ];
  unfold singularSimplexAsContinuousMap constSimplex0; aesop;

/-! ## 7. The cone on chains -/

/-- The cone of a basis generator `[σ]`. -/
noncomputable def coneGenerator (R : Type) [CommRing R] (n k : ℕ) (v : Delta n)
    (σ : singularSimplices (TopCat.of (Delta n)) k) :
    singularChainGroup R (TopCat.of (Delta n)) (k + 1) :=
  chainGenerator R (TopCat.of (Delta n)) (k + 1) (coneSimplex n k v σ)

/-- The `R`-linear map `R → C_{k+1}(Δⁿ; R)` sending `1` to `coneGenerator … σ`. -/
noncomputable def coneGeneratorHom (R : Type) [CommRing R] (n k : ℕ) (v : Delta n)
    (σ : singularSimplices (TopCat.of (Delta n)) k) :
    ModuleCat.of R R ⟶ singularChainGroup R (TopCat.of (Delta n)) (k + 1) :=
  ModuleCat.ofHom
    { toFun := fun r => r • coneGenerator R n k v σ
      -- STRIKE 18: the green sibling's own receipt
      -- (`BarycentricSubdivisionOperator.lean`, file 8704 of run 46161630202):
      -- the trailing `rfl` closes the instance-mismatched reflexive leftover
      -- that `simp [add_smul]` / `simp [mul_smul]` normalize to but do not
      -- close at the pin.
      map_add' := by
        intro r s
        simp [add_smul]
        rfl
      map_smul' := by
        intro a r
        simp [mul_smul]
        rfl }

/-- **The cone operator on chains** `Cone_v : C_k(Δⁿ; R) → C_{k+1}(Δⁿ; R)`. -/
noncomputable def coneLinearMap (R : Type) [CommRing R] (n k : ℕ) (v : Delta n) :
    singularChainGroup R (TopCat.of (Delta n)) k
      ⟶ singularChainGroup R (TopCat.of (Delta n)) (k + 1) :=
  Sigma.desc fun σ : singularSimplices (TopCat.of (Delta n)) k => coneGeneratorHom R n k v σ

/-
The cone operator has the prescribed value on a basis generator.
-/
theorem coneLinearMap_generator (R : Type) [CommRing R] (n k : ℕ) (v : Delta n)
    (σ : singularSimplices (TopCat.of (Delta n)) k) :
    (coneLinearMap R n k v).hom (chainGenerator R (TopCat.of (Delta n)) k σ)
      = coneGenerator R n k v σ := by
  -- STRIKE 18: the double `convert … using 1` (which left type-class
  -- metavariables `Type ?u`, `Monoid ?convert_1` at the pin) is replaced by the
  -- explicit `Sigma.ι_desc` chain: the desc/ι applications ride the pin-rfl
  -- ModuleCat comp-bridge, and the final `1 • X = X` is `one_smul`.
  have h := Sigma.ι_desc
    (fun τ : singularSimplices (TopCat.of (Delta n)) k => coneGeneratorHom R n k v τ) σ
  have h1 := congrArg
    (fun f : ModuleCat.of R R ⟶ singularChainGroup R (TopCat.of (Delta n)) (k + 1) => f.hom (1 : R)) h
  have h2 : (coneLinearMap R n k v).hom (chainGenerator R (TopCat.of (Delta n)) k σ)
      = ((Sigma.ι (fun τ : singularSimplices (TopCat.of (Delta n)) k => ModuleCat.of R R) σ
          ≫ Sigma.desc (fun τ : singularSimplices (TopCat.of (Delta n)) k =>
            coneGeneratorHom R n k v τ)).hom) (1 : R) := rfl
  rw [h2, h1]
  show (1 : R) • coneGenerator R n k v σ = coneGenerator R n k v σ
  exact one_smul R (coneGenerator R n k v σ)

/-! ## 8. The boundary formula -/

/-
**Boundary of the cone (base degree).** In degree `0`,
`∂ Cone_v([σ]) = [σ] - [const_v]`.
-/
theorem singularBoundary_coneGenerator_zero (R : Type) [CommRing R] (n : ℕ) (v : Delta n)
    (σ : singularSimplices (TopCat.of (Delta n)) 0) :
    (singularBoundary R (TopCat.of (Delta n)) 0).hom (coneGenerator R n 0 v σ)
      = chainGenerator R (TopCat.of (Delta n)) 0 σ
        - chainGenerator R (TopCat.of (Delta n)) 0 (constSimplex0 n v) := by
  -- STRIKE 18: the `convert … using 1` + `rw [Fin.sum_univ_two]` scaffold (the
  -- rw died: the convert had consumed the goal into a generator-mismatch and
  -- no `∑` pattern remained) is replaced by the explicit rfl-unfold of
  -- `coneGenerator` followed by the formula-rewrite and a two-face split.
  have hL : coneGenerator R n 0 v σ
      = chainGenerator R (TopCat.of (Delta n)) (0 + 1) (coneSimplex n 0 v σ) := rfl
  rw [hL, singularBoundary_chainGenerator_formula R (TopCat.of (Delta n)) 0 (coneSimplex n 0 v σ)]
  simp only [Fin.sum_univ_two]
  rw [coneSimplex_face_zero, coneSimplex_face_one_zero]
  simp [Fin.val_zero, Fin.val_one, pow_zero, one_smul, pow_one, neg_one_smul, sub_eq_add_neg]

/-
**Boundary of the cone (successor degree).** For `σ` of degree `m+1`,
`∂ Cone_v([σ]) = [σ] - Cone_v(∂[σ])`.
-/
theorem singularBoundary_coneGenerator_succ (R : Type) [CommRing R] (n m : ℕ) (v : Delta n)
    (σ : singularSimplices (TopCat.of (Delta n)) (m + 1)) :
    (singularBoundary R (TopCat.of (Delta n)) (m + 1)).hom (coneGenerator R n (m + 1) v σ)
      = chainGenerator R (TopCat.of (Delta n)) (m + 1) σ
        - (coneLinearMap R n m v).hom
            ((singularBoundary R (TopCat.of (Delta n)) m).hom
              (chainGenerator R (TopCat.of (Delta n)) (m + 1) σ)) := by
  -- STRIKE 18: rebuilt explicitly — rfl-unfold the generator, rewrite by the
  -- boundary formula at both degrees, split the alternating sum by
  -- `Fin.sum_univ_succ`, identify the two faces by the cone face lemmas,
  -- distribute the cone operator through the boundary sum by linearity
  -- (`LinearMap.map_sum`/`map_smul` + `coneLinearMap_generator`), and close by
  -- the sign flip `(-1)^(i+1) = -(-1)^i`.
  have hL : coneGenerator R n (m + 1) v σ
      = chainGenerator R (TopCat.of (Delta n)) (m + 1 + 1) (coneSimplex n (m + 1) v σ) := rfl
  rw [hL, singularBoundary_chainGenerator_formula R (TopCat.of (Delta n)) (m + 1)
    (coneSimplex n (m + 1) v σ)]
  rw [Fin.sum_univ_succ]
  rw [coneSimplex_face_zero]
  simp only [Fin.val_zero, pow_zero, one_smul]
  rw [singularBoundary_chainGenerator_formula R (TopCat.of (Delta n)) m σ]
  rw [LinearMap.map_sum]
  simp only [LinearMap.map_smul, coneLinearMap_generator]
  simp only [coneGenerator]
  rw [← Finset.sum_neg_distrib]
  refine' (Finset.sum_congr rfl fun i _ => ?_).trans ?_
  · rw [pow_succ', mul_smul, neg_one_smul]
  · rw [sub_eq_add_neg]

/-
**The cone chain-homotopy identity (successor degree).**
`∂ ∘ Cone + Cone ∘ ∂ = id` on `C_{m+1}(Δⁿ; R)`.
-/
theorem singularBoundary_coneLinearMap (R : Type) [CommRing R] (n m : ℕ) (v : Delta n) :
    coneLinearMap R n (m + 1) v ≫ singularBoundary R (TopCat.of (Delta n)) (m + 1)
        + singularBoundary R (TopCat.of (Delta n)) m ≫ coneLinearMap R n m v
      = 𝟙 (singularChainGroup R (TopCat.of (Delta n)) (m + 1)) := by
  -- STRIKE 18: the green sibling's lift (`BarycentricBoundaryChainMap.lean:66`,
  -- strike-15 receipt run 46159201696): prove the ι-component generator
  -- identity explicitly, then `Sigma.hom_ext` + `ext` + `convert … using 1`
  -- with rfl-bridges.
  apply Sigma.hom_ext
  intro σ
  have hgen : ((Sigma.ι (fun τ : singularSimplices (TopCat.of (Delta n)) (m + 1) => ModuleCat.of R R) σ
      ≫ (coneLinearMap R n (m + 1) v ≫ singularBoundary R (TopCat.of (Delta n)) (m + 1)
        + singularBoundary R (TopCat.of (Delta n)) m ≫ coneLinearMap R n m v)).hom) (1 : R)
      = ((Sigma.ι (fun τ : singularSimplices (TopCat.of (Delta n)) (m + 1) => ModuleCat.of R R) σ
          ≫ 𝟙 (singularChainGroup R (TopCat.of (Delta n)) (m + 1))).hom) (1 : R) := by
    have e3 : ((Sigma.ι (fun τ : singularSimplices (TopCat.of (Delta n)) (m + 1) => ModuleCat.of R R) σ
        ≫ (coneLinearMap R n (m + 1) v ≫ singularBoundary R (TopCat.of (Delta n)) (m + 1)
          + singularBoundary R (TopCat.of (Delta n)) m ≫ coneLinearMap R n m v)).hom) (1 : R)
        = ((coneLinearMap R n (m + 1) v ≫ singularBoundary R (TopCat.of (Delta n)) (m + 1)).hom)
            ((Sigma.ι (fun τ : singularSimplices (TopCat.of (Delta n)) (m + 1) => ModuleCat.of R R) σ).hom (1 : R))
          + ((singularBoundary R (TopCat.of (Delta n)) m ≫ coneLinearMap R n m v).hom)
            ((Sigma.ι (fun τ : singularSimplices (TopCat.of (Delta n)) (m + 1) => ModuleCat.of R R) σ).hom (1 : R)) := rfl
    have e1 : ((coneLinearMap R n (m + 1) v ≫ singularBoundary R (TopCat.of (Delta n)) (m + 1)).hom)
        ((Sigma.ι (fun τ : singularSimplices (TopCat.of (Delta n)) (m + 1) => ModuleCat.of R R) σ).hom (1 : R))
      = (singularBoundary R (TopCat.of (Delta n)) (m + 1)).hom (coneGenerator R n (m + 1) v σ) := by
      show (singularBoundary R (TopCat.of (Delta n)) (m + 1)).hom
          ((coneLinearMap R n (m + 1) v).hom (chainGenerator R (TopCat.of (Delta n)) (m + 1) σ)) = _
      rw [coneLinearMap_generator]
    have e2 : ((singularBoundary R (TopCat.of (Delta n)) m ≫ coneLinearMap R n m v).hom)
        ((Sigma.ι (fun τ : singularSimplices (TopCat.of (Delta n)) (m + 1) => ModuleCat.of R R) σ).hom (1 : R))
      = (coneLinearMap R n m v).hom ((singularBoundary R (TopCat.of (Delta n)) m).hom
          (chainGenerator R (TopCat.of (Delta n)) (m + 1) σ)) := rfl
    rw [e3, e1, e2, singularBoundary_coneGenerator_succ, sub_add_cancel]
    rfl
  ext
  first
  | exact hgen
  | (convert hgen using 1 <;> rfl)
  | (convert hgen.symm using 1 <;> rfl)

end AffineBarycentricSubdivision
end SphereOddDegree
