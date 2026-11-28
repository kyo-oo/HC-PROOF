# DESIGN SPEC 13-B3 — `GSTSphereRadialTriangulation.lean`: THE RADIAL TRIANGULATION BRIDGE

- **Date:** 2026-11-28
- **Task:** WAR COUNCIL 13-B3 (authoring spec; every Mathlib name verified against the pin
  `/tmp/ml4` = Mathlib `51e6992` = `v4.33.0-rc2` (`lean-toolchain: leanprover/lean4:v4.33.0-rc2`,
  `git log -1`: `51e6992 chore: bump toolchain to v4.33.0-rc2 (#42401)`); every corpus name
  verified against `/home/z/hc-repo` at the current HEAD, all cited corpus facts CI-green).
- **Target:** the sset morphism κ from the boundary-of-tetrahedron simplicial set
  `K := (∂Δ[3] : SSet)` to the singular simplicial set `Sing(S²) = TopCat.toSSet.obj
  (TopCat.of unitSphereType)`, sending the four nondegenerate 2-faces of `K` to the corpus's
  four radial `faceSimplex`, plus THE BRIDGE THEOREM: the induced chain map sends the
  simplicial fundamental cycle `zK` to the corpus's `fundCycle`
  (`GSTSphereFundamentalCycle.lean:400`).

---

## 0. WHAT IS BUILT AND WHY (the one-paragraph architecture)

The map κ assigns to every simplex `a` of `∂Δ[3]` (an order-preserving `α : Fin (m+1) → Fin 4`
whose image misses a tetrahedron vertex) the singular simplex
`x ↦ sphereNormalize (Σᵢ xᵢ • tetraW (α i))` of the sphere. Three facts make this a *map of
simplicial sets* and a *chain-level bridge*:

1. **Nonvanishing** — the barycentric image is never 0, because the involved vertices lie in a
   common face where the corpus's `face_indep` applies (`GSTSphereFundamentalCycle.lean:121`).
   This is the fiber-weight reduction over `Fin 4` (§2), and it needs **no monotonicity and no
   nonnegativity** — only `∑ xᵢ = 1` and linear independence.
2. **Naturality** — the barycentric-radial assignment commutes with precomposition because the
   pushed-forward barycentric coordinates are fiber sums: the corpus's `faceBary_coface`
   pattern (`GSTSphereFundamentalCycle.lean:240`) *is already the general fiber-sum shape*; we
   generalize it from `Fin.succAbove k : Fin 2 → Fin 3` to an arbitrary `θ : ⦋q⦌ ⟶ ⦋p⦌` (§4.1)
   and prove naturality for ALL structure maps at once. No generating-coface reduction needed.
3. **The bridge** — Mathlib's pinned `SSet.ι_chainChainMap_f`
   (`SimplicialSet/Homology/Basic.lean:99`) says the chain functor sends the generator
   `ιChainComplex x` to `ιChainComplex (κ.app _ x)`; composing with the specialization
   `κ (Kface i) = twoSimplexInject (faceSimplex i)` (§4.3) gives the theorem term by term.

**No `homotopyEquivNormalizedChainComplex` is needed**: the corpus's `fundCycle` lives in the
UNnormalized alternating-face complex via `ιChainComplex`, and `SSet.chainComplexFunctor`
(`SimplicialSet/Homology/Basic.lean:41`) is functorial on exactly that complex, so the bridge
is a plain functoriality statement. (The normalized-complex comparison is a *later* campaign
concern, not this file's.)

**No `yonedaEquiv` is needed**: `Kface i` is defined directly as the subtype element
`⟨stdSimplex.objEquiv.symm (SimplexCategory.δ i), membership⟩` rather than as
`yonedaEquiv (SSet.boundary.ι i)`. This avoids the Yoneda bookkeeping entirely; the membership
proof is two lines through the pinned `mem_boundary_iff_notMem_range` +
`Fin.succAbove_ne`. (The `boundary.ι` route is documented as an alternative in §7.)

---

## 1. FILE SKELETON

```lean
import Mathlib
import GSTSingularCohomologyMaps
import GSTSphereFundamentalCycle

/-!
# THE RADIAL TRIANGULATION BRIDGE (wave 13-B)

[module docstring: the κ construction, the bridge statement, honesty ledger —
 see §8 for the full text]
-/

set_option maxHeartbeats 70000000
set_option maxRecDepth 20000

noncomputable section

open CategoryTheory
open AlgebraicTopology
open Simplicial
open GSTSphereUnionComponents
open GSTSingularCohomologyMaps
open GSTSphereTetrahedronCycle
open GSTSphereFundamentalCycle

namespace GSTSphereRadialTriangulation

/-! ## §1 The barycentric-radial vertex assignment -/
-- radialBary, tetraWeight_indep_of_mem_compl, radialBary_ne_zero

/-! ## §2 The singular maps of a boundary simplex -/
-- missedVertex_of_mem, κMap_ne_zero, radialBary_continuous, κMap, κMap_continuous

/-! ## §3 The four boundary faces -/
-- Kface, Kface_mem (if inlined: not separate), Kface_apply

/-! ## §4 The sset morphism -/
-- radialBary_map (the general fiber-sum lemma), κApp, κ (the NatTrans), κ_naturality
-- (if not inlined in the def), κ_face (the specialization)

/-! ## §5 The chain bridge -/
-- κChain, Kchain, zK, κChain_face, κChain_zK, κChain_zK_d

/-! ## Receipts -/
-- #check / #print axioms block

end GSTSphereRadialTriangulation
end -- noncomputable section

/- PORT NOTES (see §7) -/
```

Import closure (verified): `GSTSphereFundamentalCycle` imports `GSTSphereNonzeroClass`
(→ `GSTSphereTetrahedronCycle` → `GSTSphereUnionComponents` transitively) and
`GSTComponentCohomologyZero`; `GSTSingularCohomologyMaps` imports `GSTGeometricRealizationStage2F`
(home of `rationalCoefficient`, line 66) and `GSTSphereUnionComponents`. Two corpus imports +
`Mathlib` therefore cover every name below.

---

## 2. §1 THE VERTEX ASSIGNMENT (nonvanishing)

### 2.1 `radialBary` — the raw builder

```lean
/-- The barycentric builder: the raw Euclidean vector under a vertex
assignment `f` (tetrahedron vertices indexed by `Fin 4`), at a point `x` of
the standard `k`-simplex.  (`tetraFaceBary` with the face index abstracted
to an arbitrary vertex list.) -/
def radialBary {k : ℕ} (f : Fin (k + 1) → Fin 4)
    (x : stdSimplex ℝ (Fin (k + 1))) : EuclideanSpace ℝ (Fin 3) :=
  ∑ i, (x : Fin (k + 1) → ℝ) i • tetraW (f i)
```

- Shape precedent: `tetraFaceBary` (`GSTSphereFundamentalCycle.lean:83-85`), `tetraBary`
  (`GSTSphereTetrahedronCycle.lean:116-117`).
- `tetraW : Fin 4 → EuclideanSpace ℝ (Fin 3)` — `GSTSphereTetrahedronCycle.lean:103`.
- No proof obligations.

### 2.2 `tetraWeight_indep_of_mem_compl` — the face reduction of independence (Lemma A)

```lean
/-- **THE FACE REDUCTION OF INDEPENDENCE.**  A `Fin 4`-weighting that vanishes
at `i₀` and whose weighted tetrahedron sum is zero vanishes identically: the
remaining three weights ride the face opposite `i₀`, where the corpus's
`face_indep` applies. -/
theorem tetraWeight_indep_of_mem_compl {i₀ : Fin 4} {ν : Fin 4 → ℝ}
    (hν₀ : ν i₀ = 0) (h : ∑ k, ν k • tetraW k = 0) : ∀ k, ν k = 0 := by
  have hface : ∑ j : Fin 3, ν (i₀.succAbove j) • faceVert i₀ j = 0 := by
    have hs := Fin.sum_univ_succAbove (fun k => ν k • tetraW k) i₀
    rw [h, hν₀, zero_smul, add_zero] at hs
    exact hs.symm
  have h3 : ∀ j : Fin 3, ν (i₀.succAbove j) = 0 := face_indep i₀ _ hface
  intro k
  by_cases hk : k = i₀
  · rw [hk, hν₀]
  · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq (Ne.symm hk)
    rw [← hj]
    exact h3 j
```

Verified names:
- `Fin.sum_univ_succAbove (f : Fin (n+1) → M) (x : Fin (n+1)) :
  ∑ i, f i = f x + ∑ i : Fin n, f (x.succAbove i)` — to_additive of `Fin.prod_univ_succAbove`,
  `Mathlib/Algebra/BigOperators/Fin.lean:68-71`; used as `Fin.sum_univ_succAbove` at
  `Mathlib/LinearAlgebra/Matrix/Determinant/Misc.lean:49`.
- `face_indep (i : Fin 4) (μ : Fin 3 → ℝ) (h : ∑ j, μ j • faceVert i j = 0) : ∀ j, μ j = 0` —
  corpus `GSTSphereFundamentalCycle.lean:121-122` (CI-green).
- `faceVert i j := tetraW (i.succAbove j)` — corpus `:79-80`; the `hface` step `rfl`-closes
  through this definition (`faceVert i₀ j` is *definitionally* `tetraW (i₀.succAbove j)`).
- `Fin.exists_succAbove_eq {x y : Fin (n+1)} (h : x ≠ y) : ∃ z, y.succAbove z = x` —
  `Mathlib/Data/Fin/SuccPred.lean:672`.

Proof-strategy notes: `hface`'s `exact hs.symm` rides two definitional equalities (the `faceVert`
unfold, and the beta-reduction of `(fun k => ν k • tetraW k) (i₀.succAbove j)`); if `exact`
stalls, close by `show ∑ j, ν (i₀.succAbove j) • tetraW (i₀.succAbove j) = 0; exact hs.symm`.

### 2.3 `radialBary_ne_zero` — the nonvanishing (Lemma B)

```lean
/-- **THE NONVANISHING.**  A vertex assignment that misses the tetrahedron
vertex `r` has no barycentric combination of total weight `1` at the origin:
the fiber weights ride the face opposite `r`, where the three vertices are
independent, while their total weight is `1`.  (No monotonicity and no
nonnegativity needed — linear independence does all the work.) -/
theorem radialBary_ne_zero {k : ℕ} (f : Fin (k + 1) → Fin 4) (r : Fin 4)
    (hr : ∀ i, f i ≠ r) (x : stdSimplex ℝ (Fin (k + 1))) :
    radialBary f x ≠ 0 := by
  obtain ⟨hnonneg, hsumone⟩ :
      (∀ i, 0 ≤ (x : Fin (k + 1) → ℝ) i) ∧ ∑ i, (x : Fin (k + 1) → ℝ) i = 1 := x.2
  intro h
  set ν : Fin 4 → ℝ :=
    fun c => ∑ i ∈ Finset.univ.filter (fun i => f i = c), (x : Fin (k + 1) → ℝ) i with hνdef
  -- (1) the fiber-weighted tetrahedron sum is the barycentric one:
  have hreg : ∑ c : Fin 4, ν c • tetraW c = radialBary f x := by
    calc ∑ c : Fin 4, ν c • tetraW c
        = ∑ c : Fin 4, ∑ i ∈ Finset.univ.filter (fun i => f i = c),
            (x : Fin (k + 1) → ℝ) i • tetraW c := by
              refine Finset.sum_congr rfl fun c _ => ?_
              simp only [hνdef]
              rw [Finset.sum_smul]
      _ = ∑ c : Fin 4, ∑ i ∈ Finset.univ.filter (fun i => f i = c),
            (x : Fin (k + 1) → ℝ) i • tetraW (f i) := by
              refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun i hi => ?_
              rw [(Finset.mem_filter.1 hi).2]
      _ = radialBary f x := by
            exact Finset.sum_fiberwise Finset.univ f
              (fun i => (x : Fin (k + 1) → ℝ) i • tetraW (f i))
  -- (2) the missed vertex carries no weight:
  have hr₀ : ν r = 0 := by
    have hempty : Finset.univ.filter (fun i => f i = r) = ∅ :=
      Finset.filter_eq_empty_iff.2 (fun i _ => hr i)
    simp [hνdef, hempty]
  -- (3) independence kills all fiber weights:
  have hkill : ∀ c, ν c = 0 := tetraWeight_indep_of_mem_compl hr₀ (by rw [← hreg]; exact h)
  -- (4) but their total is 1 — contradiction:
  have htotal : ∑ c : Fin 4, ν c = 1 := by
    have hfib := Finset.sum_fiberwise Finset.univ f (fun i => (x : Fin (k + 1) → ℝ) i)
    rw [← hsumone]
    exact hfib.symm
  have hzero : ∑ c : Fin 4, ν c = 0 := Finset.sum_congr rfl fun c _ => hkill c
  exact zero_ne_one (hzero.trans htotal)
```

Verified names:
- `Finset.sum_smul` (scalar out of a filtered sum) — same use as corpus
  `faceBary_coface` (`GSTSphereFundamentalCycle.lean:258-259`).
- `Finset.sum_fiberwise (s : Finset ι) (g : ι → κ) (f : ι → M) :
  ∑ j, ∑ i ∈ s with g i = j, f i = ∑ i ∈ s, f i` — to_additive of `Finset.prod_fiberwise`,
  `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:275-277` (section `[Fintype κ]` at
  :273; here `κ := Fin 4`).
- `Finset.filter_eq_empty_iff`, `Finset.mem_filter` — standard Finset API.
- The `obtain ⟨hnonneg, hsumone⟩ ... := x.2` destructuring of the `stdSimplex` membership —
  corpus precedent `tetraFaceBary_ne_zero` (`GSTSphereFundamentalCycle.lean:188-189`).
- Note `hnonneg` is *unused* — independence needs no nonnegativity (see §0). If the linter
  complains, replace the destructuring by `have hsumone : ∑ i, (x : Fin (k+1) → ℝ) i = 1 := x.2.2`.

---

## 3. §2 THE SINGULAR MAPS OF A BOUNDARY SIMPLEX (continuity block)

### 3.1 `missedVertex_of_mem` — extracting the missed vertex

```lean
/-- Every simplex of the boundary misses a tetrahedron vertex: the boundary
predicate is non-surjectivity of the vertex function
(`SSet.boundary`, `Mathlib/AlgebraicTopology/SimplicialSet/Boundary.lean:37-39`). -/
theorem missedVertex_of_mem {M : SimplexCategoryᵒᵖ} {α : (Δ[3] : SSet).obj M}
    (hα : α ∈ (SSet.boundary 3).obj M) :
    ∃ r : Fin 4, ∀ j : Fin (M.unop.len + 1), α j ≠ r := by
  by_contra hcon
  push_neg at hcon
  exact hα (fun r => hcon r)
```

Mechanism: `hα` is *definitionally* `¬ Function.Surjective (stdSimplex.asOrderHom α)`
(`SSet.boundary`'s `obj` field is `Set.ofPred (fun s ↦ ¬Function.Surjective
(stdSimplex.asOrderHom s))`, `Boundary.lean:38`; membership in `Set.ofPred` is `Iff.rfl` by
`Set.mem_ofPred`, `Mathlib/Data/Set/Operations.lean:92`), and the FunLike application `α j`
(`Mathlib/AlgebraicTopology/SimplicialSet/StdSimplex.lean:76-78`) is definitionally
`(stdSimplex.asOrderHom α) j` (`asOrderHom` at `StdSimplex.lean:142-143`; both read
`(objEquiv α).toOrderHom j`). `push_neg` turns `¬∃ r, ∀ j, α j ≠ r` into `∀ r, ∃ j, α j = r`,
which is the Surjective witness. If `exact hα (fun r => hcon r)` stalls on the defeq chain,
repair by `have hns : ¬ Function.Surjective (fun j : Fin (M.unop.len + 1) => α j) := hα` and
`exact absurd (fun r => hcon r) hns` (PORT NOTE R-4).

### 3.2 `κMap_ne_zero`, `radialBary_continuous`, `κMap`, `κMap_continuous`

```lean
/-- The barycentric image of a boundary simplex is nonzero (the missed vertex
reduction of §1). -/
theorem κMap_ne_zero {M : SimplexCategoryᵒᵖ} (a : (∂Δ[3] : SSet).obj M)
    (x : stdSimplex ℝ (Fin (M.unop.len + 1))) :
    radialBary (⇑a.1) x ≠ 0 := by
  obtain ⟨r, hr⟩ := missedVertex_of_mem a.2
  exact radialBary_ne_zero (⇑a.1) r (fun j => by simpa using hr j) x

/-- The barycentric builder is continuous (the `tetraFaceBary_continuous`
pattern at general degree). -/
theorem radialBary_continuous {k : ℕ} (f : Fin (k + 1) → Fin 4) :
    Continuous (radialBary f) := by
  have hcoe : Continuous fun x : stdSimplex ℝ (Fin (k + 1)) => (x : Fin (k + 1) → ℝ) :=
    continuous_induced_dom
  have hterm : ∀ i : Fin (k + 1),
      Continuous fun x : stdSimplex ℝ (Fin (k + 1)) =>
        ((x : Fin (k + 1) → ℝ) i : ℝ) • (tetraW (f i) : EuclideanSpace ℝ (Fin 3)) := by
    intro i
    have hap : Continuous fun x : stdSimplex ℝ (Fin (k + 1)) =>
        ((x : Fin (k + 1) → ℝ) i : ℝ) :=
      (continuous_apply i).comp hcoe
    exact hap.smul continuous_const
  exact continuous_finsetSum _ fun i _ => hterm i

/-- **THE RADIAL SINGULAR MAP OF A BOUNDARY SIMPLEX.**  The center-radial
projection of the barycentric parametrization: `x ↦ sphereNormalize
(∑ i, x i • tetraW (a.1 i))`. -/
def κMap {M : SimplexCategoryᵒᵖ} (a : (∂Δ[3] : SSet).obj M) :
    stdSimplex ℝ (Fin (M.unop.len + 1)) → unitSphereType :=
  fun x => sphereNormalize (κMap_ne_zero a x)

/-- The radial map is continuous (the staged composition — the
`faceMap_continuous` pattern at general degree). -/
theorem κMap_continuous {M : SimplexCategoryᵒᵖ} (a : (∂Δ[3] : SSet).obj M) :
    Continuous (κMap a) := by
  have hco : Continuous fun x : stdSimplex ℝ (Fin (M.unop.len + 1)) =>
      ((‖radialBary (⇑a.1) x‖⁻¹ : ℝ) • radialBary (⇑a.1) x :
        EuclideanSpace ℝ (Fin 3)) := by
    rw [continuous_iff_continuousAt]
    intro x₀
    have hg : ContinuousAt (fun y : EuclideanSpace ℝ (Fin 3) => (‖y‖⁻¹ : ℝ) • y)
        (radialBary (⇑a.1) x₀) :=
      continuousAt_sphereNormalize (κMap_ne_zero a x₀)
    have hf : ContinuousAt (radialBary (⇑a.1)) x₀ := (radialBary_continuous _).continuousAt
    exact ContinuousAt.comp (f := radialBary (⇑a.1)) (x := x₀) hg hf
  exact Continuous.subtype_mk hco _
```

Verified names (all corpus-green at the exact same shapes):
- `sphereNormalize {y} (hy : y ≠ 0) : unitSphereType` — `GSTSphereTetrahedronCycle.lean:196-202`.
- `continuousAt_sphereNormalize` — `GSTSphereTetrahedronCycle.lean:206-212`.
- `continuous_induced_dom`, `continuous_apply`, `Continuous.smul`, `continuous_const`,
  `continuous_finsetSum` — the `tetraFaceBary_continuous` pattern,
  `GSTSphereFundamentalCycle.lean:101-114`.
- `ContinuousAt.comp (f := ..) (x := ..)` two-explicit-arg pin shape; `continuous_iff_continuousAt`;
  `Continuous.subtype_mk hco _` — the `faceMap_continuous` pattern,
  `GSTSphereFundamentalCycle.lean:215-228` (per the wave-10-B-REPAIR-IV discipline: composition
  pinned by named arguments).
- `(∂Δ[3] : SSet)` — the `CoeOut X.Subcomplex SSet` coercion (`Subcomplex.toSSet`,
  `Mathlib/AlgebraicTopology/SimplicialSet/Subcomplex.lean:52-55`; `∂Δ[n]` notation
  `Boundary.lean:42`, scoped `Simplicial`). The carrier at `M` is the subtype
  `{α : (Δ[3]).obj M // α ∈ (boundary 3).obj M}` (`Subfunctor.toFunctor`,
  `Mathlib/CategoryTheory/Subfunctor/Basic.lean:141-144`), so `a.1 : (Δ[3]).obj M` and the
  FunLike application `⇑a.1 : Fin (M.unop.len + 1) → Fin 4`
  (`StdSimplex.lean:76-78`).
- `simpa using hr j` bridge: `hr j : α j ≠ r` vs needed `⇑a.1 j ≠ r` — same FunLike coe,
  trivially true; if `simpa` is heavy, `hr j` directly (defeq).

---

## 4. §3 THE FOUR BOUNDARY FACES

### 4.1 `Kface` and `Kface_apply`

```lean
/-- **THE i-TH FACE OF `∂Δ[3]`.**  The 2-simplex carried by the
order-preserving injection skipping the vertex `i`: the pinned coface
`SimplexCategory.δ i : ⦋2⦌ ⟶ ⦋3⦌`, read through `stdSimplex.objEquiv`. -/
def Kface (i : Fin 4) : (∂Δ[3] : SSet) _⦋2⦌ :=
  ⟨stdSimplex.objEquiv.symm (SimplexCategory.δ i), by
    rw [mem_boundary_iff_notMem_range]
    refine ⟨i, fun hj => ?_⟩
    obtain ⟨j, hj'⟩ := Set.mem_range.1 hj
    have hsucc : i.succAbove j = i := by
      simpa using hj'
    exact Fin.succAbove_ne i j hsucc⟩

/-- The vertices of the i-th face are the tetrahedron vertices other than
`i`, in increasing order — exactly the corpus's `faceVert` list. -/
theorem Kface_apply (i : Fin 4) (j : Fin 3) :
    (Kface i).1 j = i.succAbove j := by
  show (stdSimplex.objEquiv.symm (SimplexCategory.δ i) : (Δ[3] : SSet) _⦋2⦌) j = _
  rw [stdSimplex.objEquiv_symm_apply]
  simp [SimplexCategory.δ, Fin.succAboveOrderEmb_apply]
```

Verified names:
- `SimplexCategory.δ (i : Fin (n+2)) : ⦋n⦌ ⟶ ⦋n+1⦌ := mkHom (Fin.succAboveOrderEmb i).toOrderHom`
  — `Mathlib/AlgebraicTopology/SimplexCategory/Basic.lean:231-232`; `i : Fin 4 = Fin (2+2)`
  gives `δ i : ⦋2⦌ ⟶ ⦋3⦌`. ✓
- `stdSimplex.objEquiv {n m} : (stdSimplex.obj n).obj m ≃ (m.unop ⟶ n)` —
  `StdSimplex.lean:67-68`; `objEquiv.symm (δ i) : (Δ[3]).obj (op ⦋2⦌) = Δ[3] _⦋2⦌`.
- `mem_boundary_iff_notMem_range {n d} (s : Δ[n] _⦋d⦌) :
  s ∈ (boundary n).obj _ ↔ ∃ j : Fin (n+1), j ∉ Set.range s` —
  `Mathlib/AlgebraicTopology/SimplicialSet/Boundary.lean:55-58`. Our membership goal is at
  `op ⦋2⦌`, exactly the lemma's shape (n := 3, d := 2). ✓
- `Fin.succAbove_ne (p : Fin (n+1)) (i : Fin n) : p.succAbove i ≠ p` —
  `Mathlib/Data/Fin/SuccPred.lean:571`.
- `stdSimplex.objEquiv_symm_apply {n m} (f : ⦋m⦌ ⟶ ⦋n⦌) (i) :
  (objEquiv.symm f : Δ[n] _⦋m⦌) i = f.toOrderHom i` — `StdSimplex.lean:108-110`.
- `Fin.succAboveOrderEmb` — `Mathlib/Order/Fin/Basic.lean:382-384`
  (`OrderEmbedding.ofStrictMono (succAbove p) _`); `Fin.succAboveOrderEmb_apply` is the
  `@[simps! apply]`-generated coe lemma (used e.g. at
  `Mathlib/AlgebraicTopology/SimplexCategory/Basic.lean:452` together with
  `OrderEmbedding.toOrderHom_coe`); `Fin.range_succAboveOrderIso` /
  `Set.range` route is the fallback if the `simpa` needs help.
- `Set.mem_range : a ∈ Set.range f ↔ ∃ b, f b = a` — standard.

The `hsucc` step's normalization chain: `hj' : (⇑(objEquiv.symm (δ i))) j = i` →
`(δ i).toOrderHom j = i` (objEquiv_symm_apply) → `i.succAbove j = i` (δ-unfold +
`Fin.succAboveOrderEmb_apply`). If `simpa using hj'` does not close it, spell the simp set:
`simpa [stdSimplex.objEquiv_symm_apply, SimplexCategory.δ, Fin.succAboveOrderEmb_apply] using hj'`
(PORT NOTE R-6).

**Design note (why not `yonedaEquiv (SSet.boundary.ι i)`):** `SSet.boundary.ι (i : Fin (n+2)) :
Δ[n] ⟶ (∂Δ[n+1] : SSet)` exists at the pin (`Boundary.lean:169-174`, built by `Subcomplex.lift`),
and `yonedaEquiv (boundary.ι i) : (∂Δ[3]).obj (op ⦋2⦌)` is the Yoneda-dual of it. The direct
subtype construction above is preferred: it avoids `yonedaEquiv` roundtrips entirely, and the
specialization `Kface_apply` becomes a two-rewrite computation. The two descriptions agree
(`boundary.ι_ι : ι i ≫ ∂Δ[n+1].ι = stdSimplex.δ i`, `Boundary.lean:176-178`), so the seam is
documented but unused.

---

## 5. §4 THE SSET MORPHISM κ (the core technical section)

### 5.1 `radialBary_map` — the general fiber-sum lemma (generalized `faceBary_coface`)

```lean
/-- **THE FIBER-SUM PUSHFORWARD (the generalized coface calculus).**  The
barycentric image of a `stdSimplex.map`-pushed point, under a vertex
assignment `f`, is the barycentric image under the composed assignment
`f ∘ θ`: the pushed coordinates are the fiber sums.  This is the corpus's
`faceBary_coface` pattern (`GSTSphereFundamentalCycle.lean:240`) at general
degree — `Fin.succAbove k : Fin 2 → Fin 3` generalized to any `θ`. -/
theorem radialBary_map {p q : ℕ} (θ : ⦋q⦌ ⟶ ⦋p⦌)
    (f : Fin (p + 1) → Fin 4) (y : stdSimplex ℝ (Fin (q + 1))) :
    radialBary f (stdSimplex.map θ y) = radialBary (fun j => f (θ j)) y := by
  have hcoord : ∀ i : Fin (p + 1),
      ((stdSimplex.map θ y : Fin (p + 1) → ℝ) i)
        = ∑ j : Fin (q + 1), (if θ j = i then (y : Fin (q + 1) → ℝ) j else 0) := by
    intro i
    rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply, Finset.sum_filter]
  calc radialBary f (stdSimplex.map θ y)
      = ∑ i : Fin (p + 1), ((stdSimplex.map θ y : Fin (p + 1) → ℝ) i) •
          tetraW (f i) := rfl
    _ = ∑ i : Fin (p + 1), (∑ j : Fin (q + 1),
          (if θ j = i then (y : Fin (q + 1) → ℝ) j else 0)) • tetraW (f i) := by
        exact Finset.sum_congr rfl fun i _ => by rw [hcoord i]
    _ = ∑ i : Fin (p + 1), ∑ j : Fin (q + 1),
          ((if θ j = i then (y : Fin (q + 1) → ℝ) j else 0)) • tetraW (f i) := by
        exact Finset.sum_congr rfl fun i _ => by rw [Finset.sum_smul]
    _ = ∑ j : Fin (q + 1), ∑ i : Fin (p + 1),
          ((if θ j = i then (y : Fin (q + 1) → ℝ) j else 0)) • tetraW (f i) := Finset.sum_comm
    _ = ∑ j : Fin (q + 1), (y : Fin (q + 1) → ℝ) j • tetraW (f (θ j)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_eq_single (θ j)]
        · rw [if_pos rfl]
        · intro i _hi hne
          rw [if_neg (fun hh => hne hh.symm), zero_smul]
        · intro hmem
          exact absurd (Finset.mem_univ _) hmem
    _ = radialBary (fun j => f (θ j)) y := rfl
```

This is the corpus's `faceBary_coface` skeleton (`GSTSphereFundamentalCycle.lean:249-271`)
VERBATIM at general degrees. Verified names:
- `stdSimplex.map (f : X → Y)` (the ANALYSIS-side map on convex std simplices) —
  `Mathlib/Analysis/Convex/StdSimplex.lean:317-318`; `stdSimplex.map_coe` — `:321-322`;
  `stdSimplex.continuous_map` (`@[continuity]`) — `:347-348`.
- `FunOnFinite.linearMap_apply_apply (f) (s) (y) :
  linearMap R M f s y = (Finset.univ.filter (fun x ↦ f x = y)).sum s` —
  `Mathlib/LinearAlgebra/Finsupp/Pi.lean:302-305`.
- `Finset.sum_filter`, `Finset.sum_smul`, `Finset.sum_comm`, `Finset.sum_eq_single`,
  `Finset.sum_congr` — the corpus's green set (PORT NOTE FC-3 of
  `GSTSphereFundamentalCycle.lean:517-521`).
- **The `θ` coercion**: `SimplexCategory` is a `ConcreteCategory` with homs `→o`
  (`Mathlib/AlgebraicTopology/SimplexCategory/Basic.lean:595-598`), so `CoeFun (X ⟶ Y)
  (fun _ ↦ ToType X → ToType Y)` (`Mathlib/CategoryTheory/ConcreteCategory/Basic.lean:100-102`)
  makes `θ` elaborate as a function `Fin (q+1) → Fin (p+1)` in `stdSimplex.map θ` and `θ j` —
  exactly how the pinned `TopCat.toSSetObjEquiv_naturality_apply` states `stdSimplex.map f`
  for `f : n ⟶ m` (`Mathlib/AlgebraicTopology/SimplicialSet/TopAdj.lean:106-110`).
  `SimplexCategory.coe_δ : dsimp% ⇑(δ i) = Fin.succAbove i` (`Basic.lean:604-605`) is the
  generating-case normalization.
- **Why stated with the Hom-coe spelling**: the naturality proof (§5.3) rewrites with the
  pinned `toSSetObjEquiv_naturality_apply`, whose RHS contains `stdSimplex.map f` elaborated
  through this same coercion; stating `radialBary_map` identically makes the `rw`-pattern
  match syntactically (risk R-1).

### 5.2 `κApp` and `κ` — the component functions and the natTrans

```lean
/-- The degree-`M` component of κ, as a plain function. -/
def κApp (M : SimplexCategoryᵒᵖ) :
    (∂Δ[3] : SSet).obj M → (TopCat.toSSet.obj (TopCat.of unitSphereType)).obj M :=
  fun a => (TopCat.toSSetObjEquiv (TopCat.of unitSphereType) M).symm
    ⟨fun x => κMap a x, κMap_continuous a⟩

/-- **THE RADIAL TRIANGULATION MAP** — the morphism of simplicial sets
`κ : ∂Δ[3] ⟶ Sing(S²)` sending each boundary simplex to the center-radial
singular simplex of its barycentric image. -/
def κ : (∂Δ[3] : SSet) ⟶ TopCat.toSSet.obj (TopCat.of unitSphereType) where
  app M := ↾κApp M
  naturality := by
    intro M M' F
    ext a
    apply (TopCat.toSSetObjEquiv (TopCat.of unitSphereType) M').injective
    refine ContinuousMap.ext (fun z => ?_)
    -- RHS: the pinned naturality of the singular sset, at `F.unop`:
    have hR := TopCat.toSSetObjEquiv_naturality_apply
      (X := TopCat.of unitSphereType) (f := F.unop) (x := κ.app M a) (z := z)
    simp only [Quiver.Hom.op_unop] at hR
    -- LHS: the equiv roundtrip of the component:
    have hL : TopCat.toSSetObjEquiv (TopCat.of unitSphereType) M'
        (κ.app M' ((∂Δ[3] : SSet).map F a)) z
        = κMap ((∂Δ[3] : SSet).map F a) z := by
      show _ ((TopCat.toSSetObjEquiv (TopCat.of unitSphereType) M').symm
        ⟨fun x => κMap _ x, _⟩) z = _
      rw [(TopCat.toSSetObjEquiv (TopCat.of unitSphereType) M').apply_symm_apply]
      rfl
    rw [hL, hR]
    -- the value equality: both sides are `sphereNormalize` of raw vectors;
    -- the composite's vertex function vs the fiber pushforward:
    have hvert : ∀ j : Fin (M'.unop.len + 1),
        ((∂Δ[3] : SSet).map F a).1 j = (⇑a.1) (⇑F.unop j) := by
      intro j
      have h1 : ((∂Δ[3] : SSet).map F a).1 = (Δ[3] : SSet).map F a.1 := rfl
      have h2 : (Δ[3] : SSet).map F a.1
          = stdSimplex.objEquiv.symm (F.unop ≫ stdSimplex.objEquiv a.1) := by
        rw [show a.1 = stdSimplex.objEquiv.symm (stdSimplex.objEquiv a.1) from
            (stdSimplex.objEquiv (n := ⦋3⦌) (m := M)).symm_apply_apply a.1]
        exact stdSimplex.map_objEquiv_symm (stdSimplex.objEquiv a.1) F
      show ((∂Δ[3] : SSet).map F a).1 j = _
      rw [h1, h2]
      simp [stdSimplex.objEquiv_symm_apply, SimplexCategory.comp_toOrderHom]
    show sphereNormalize (κMap_ne_zero ((∂Δ[3] : SSet).map F a) z)
        = sphereNormalize (κMap_ne_zero a (stdSimplex.map F.unop z))
    refine sphereNormalize_eq_of_eq _ _ ?_
    unfold κMap radialBary
    rw [Finset.sum_congr rfl fun j _ => by rw [hvert j]]
    exact (radialBary_map F.unop (⇑a.1) z).symm
```

Verified names and mechanism:
- **The `↾` packaging**: `app M := ↾κApp M` — `↾f` is `TypeCat.ofHom f`
  (`Mathlib/CategoryTheory/Types/Basic.lean:142`), the way a plain function typechecks as a
  morphism in `Type` (the morphisms of `SSet = SimplexCategoryᵒᵖ ⥤ Type`). Precedents:
  `SSet.const` (`Mathlib/AlgebraicTopology/SimplicialSet/Basic.lean:45-52`),
  `Subfunctor.lift` (`Mathlib/CategoryTheory/Subfunctor/Image.lean:58-63`) — both construct
  sset/presheaf morphisms with `app := ↾fun ...` and `naturality ... := by ext x; ...`.
- **The `ext a` on the naturality goal**: same precedents as above; the equality of
  Type-morphisms admits `ext` (the corpus-adjacent green pattern; `SSet.const`'s proof is
  `ext; dsimp; rw [← CategoryTheory.comp_apply, ← Functor.map_comp]; rfl`).
- **`TopCat.toSSetObjEquiv_naturality_apply`** — THE pinned RHS lemma:
  `{X} {n m : SimplexCategory} (f : n ⟶ m) (x : (toSSet.obj X).obj (op m))
  (z : stdSimplex ℝ (Fin (n.len + 1))) : dsimp% X.toSSetObjEquiv _ ((toSSet.obj X).map f.op x) z
  = X.toSSetObjEquiv _ x (stdSimplex.map f z)` — `rfl`, @[simp],
  `Mathlib/AlgebraicTopology/SimplicialSet/TopAdj.lean:104-110`.
  **The abstract-degree application works by record eta**: our `F : M ⟶ M'` in
  `SimplexCategoryᵒᵖ` unifies with `f.op` (since `F ≡ op F.unop` by structural eta for
  `Opposite`, `Mathlib/Data/Opposite.lean:41-53`, plus `Quiver.Hom.op_unop`,
  `Mathlib/CategoryTheory/Opposites.lean:57-59`), and `M ≡ op M.unop`,
  `M' ≡ op M'.unop`; similarly `⦋q⦌ ≡ SimplexCategory.mk q` by eta for `SimplexCategory`
  (`Mathlib/AlgebraicTopology/SimplexCategory/Defs.lean:51-56`). If the eta-unification
  stalls, the fallback is the explicit elimination
  `induction M using Opposite.rec with | _ A => induction M' using Opposite.rec with | _ B =>`
  (auto-reverting `F`, `a`), after which the lemma applies at literal `op`-shapes
  (risk R-2, with this fallback spelled out).
- **`simp only [Quiver.Hom.op_unop] at hR`**: normalizes `F.unop.op` (the lemma's map
  argument) to `F` — `Quiver.Hom.op_unop (f : X ⟶ Y) : f.unop.op = f`, rfl-simp,
  `Mathlib/CategoryTheory/Opposites.lean:57-59`.
- **`stdSimplex.map_objEquiv_symm {n} {m m'} (f : m.unop ⟶ n) (g : m ⟶ m') :
  (stdSimplex.obj n).map g (objEquiv.symm f) = objEquiv.symm (g.unop ≫ f)`** — `rfl`,
  `Mathlib/AlgebraicTopology/SimplicialSet/StdSimplex.lean:101-104` — the K-side structure
  map, stated at ABSTRACT `m m'` (no eta needed here).
- **`stdSimplex.objEquiv_symm_apply`** — `StdSimplex.lean:108-110` (applied via eta at
  `M'.unop`); **`SimplexCategory.comp_toOrderHom (f ≫ g).toOrderHom = g.toOrderHom.comp
  f.toOrderHom`** — `Mathlib/AlgebraicTopology/SimplexCategory/Defs.lean:126-127`, `rfl`.
- **`Equiv.apply_symm_apply`** + `rfl` — the LHS roundtrip; the corpus's `toSSetObj₂_face`
  h2-step pattern (`GSTSingularCohomologyMaps.lean:223-230`).
- **`sphereNormalize_eq_of_eq`** — corpus `GSTSphereFundamentalCycle.lean:206-210`
  (proof-irrelevance at the subtype — the edgeSimplex_eq tool).
- `TopCat.toSSetObjEquiv (X) (n) : (toSSet.obj X).obj n ≃ C(stdSimplex ℝ (Fin (n.unop.len+1)), X)`
  — `Mathlib/AlgebraicTopology/SingularSet.lean:60-63` (stated at abstract `n`, which is what
  makes the abstract-degree components legal); `TopCat.toSSet` — `SingularSet.lean:52-54`.
- The final rewrite `(radialBary_map F.unop (⇑a.1) z).symm`: `radialBary_map` at
  `θ := F.unop : ⦋M'.unop.len⦌ ⟶ ⦋M.unop.len⦌` (eta) and `f := ⇑a.1` reads
  `radialBary (⇑a.1) (stdSimplex.map F.unop z) = radialBary (fun j => (⇑a.1) ((⇑F.unop) j)) z`,
  which is exactly the goal after `hvert` — modulo the two DEFEQ coe-identifications
  `(⇑((∂Δ[3]).map F a).1) j = (⇑a.1) (⇑F.unop j)` (handled by `hvert` + `Finset.sum_congr`)
  and the `radialBary`-unfold (risk R-1: the coe-spellings `⇑F.unop` vs `⇑(F.unop.toOrderHom)`
  reduce to the same term — `ConcreteCategory.hom F.unop` is `Hom.toOrderHom F.unop` by the
  instance field — repair with `show`/`dsimp only` if `rw` mismatches).

### 5.3 `κ_face` — the specialization at the four faces

```lean
/-- **THE SPECIALIZATION AT THE FOUR FACES.**  The radial triangulation map
sends the i-th boundary face to the corpus's center-radial face simplex
(`faceSimplex i`, `GSTSphereFundamentalCycle.lean:231`). -/
theorem κ_face (i : Fin 4) :
    κ.app (Opposite.op (SimplexCategory.mk 2)) (Kface i)
      = twoSimplexInject (faceSimplex i) := by
  apply (TopCat.toSSetObjEquiv (TopCat.of unitSphereType)
    (Opposite.op (SimplexCategory.mk 2))).injective
  refine ContinuousMap.ext (fun z => ?_)
  have hL : TopCat.toSSetObjEquiv (TopCat.of unitSphereType)
      (Opposite.op (SimplexCategory.mk 2)) (κ.app _ (Kface i)) z = κMap (Kface i) z := by
    show _ ((TopCat.toSSetObjEquiv _ _).symm
      ⟨fun x => κMap (Kface i) x, _⟩) z = _
    rw [(TopCat.toSSetObjEquiv (TopCat.of unitSphereType)
      (Opposite.op (SimplexCategory.mk 2))).apply_symm_apply]
    rfl
  have hR : TopCat.toSSetObjEquiv (TopCat.of unitSphereType)
      (Opposite.op (SimplexCategory.mk 2)) (twoSimplexInject (faceSimplex i)) z
      = faceMap i z := by
    exact congrArg (fun σ : C(StdTwoSimplex, TopCat.of unitSphereType) => σ z)
      ((TopCat.toSSetObjEquiv (TopCat.of unitSphereType)
        (Opposite.op (SimplexCategory.mk 2))).symm_apply_apply (faceSimplex i))
  rw [hL, hR]
  show sphereNormalize (κMap_ne_zero (Kface i) z)
      = sphereNormalize (tetraFaceBary_ne_zero i z)
  refine sphereNormalize_eq_of_eq _ _ ?_
  unfold κMap radialBary tetraFaceBary faceVert
  exact Finset.sum_congr rfl fun j _ => by rw [Kface_apply i j]
```

Mechanism: the `edgeSimplex_eq` pattern of the corpus
(`GSTSphereFundamentalCycle.lean:276-294`): equiv-injectivity → `ContinuousMap.ext` →
the two `toSSetObjEquiv` roundtrips (`Equiv.apply_symm_apply` / `symm_apply_apply`) →
value equality by `sphereNormalize_eq_of_eq` — the raw vectors agree because
`radialBary (⇑(Kface i).1) z = ∑ j, z j • tetraW (i.succAbove j) = tetraFaceBary i z`
through `Kface_apply` and the `faceVert` definition (rfl-defeq). Verified corpus names:
`twoSimplexInject` (`GSTSingularCohomologyMaps.lean:204-206`), `StdTwoSimplex` (`:185-186`),
`faceSimplex` (`GSTSphereFundamentalCycle.lean:231-232`), `faceMap` (`:201-202`),
`tetraFaceBary` (`:83-85`), `tetraFaceBary_ne_zero` (`:186-196`), `faceVert` (`:79-80`).

---

## 6. §5 THE CHAIN BRIDGE

### 6.1 The chain map, the faces' chains, the simplicial fundamental cycle

```lean
/-- **THE INDUCED CHAIN MAP.**  The morphism of simplicial chain complexes
induced by κ (the pinned `SSet.chainComplexFunctor`'s functoriality; the
target is spelled with the corpus's `singularChainsOf`, definitionally the
same complex by the `chains_eq` receipt). -/
noncomputable def κChain :
    (∂Δ[3] : SSet).chainComplex (ModuleCat.of ℚ ℚ) ⟶
      singularChainsOf (TopCat.of unitSphereType) :=
  SSet.chainComplexMap κ (ModuleCat.of ℚ ℚ)

/-- The degree-2 chain carried by the i-th boundary face (the `faceChain`
spelling on the K side). -/
def Kchain (i : Fin 4) :
    ((∂Δ[3] : SSet).chainComplex (ModuleCat.of ℚ ℚ)).X 2 :=
  (((∂Δ[3] : SSet).ιChainComplex (Kface i) :
    ModuleCat.of ℚ ℚ ⟶ ((∂Δ[3] : SSet).chainComplex (ModuleCat.of ℚ ℚ)).X 2).hom (1 : ℚ))

/-- **THE SIMPLICIAL FUNDAMENTAL CYCLE OF `∂Δ[3]`.**  The alternating sum of
the four face chains — the simplicial avatar of the corpus's `fundCycle`.
(INTERFACE: the planned sibling `GSTSphereSimplicialFundamentalClass` owns
this cycle; if it has landed, these three definitions move there and this
file imports them — see PORT NOTE R-8.) -/
def zK : ((∂Δ[3] : SSet).chainComplex (ModuleCat.of ℚ ℚ)).X 2 :=
  Kchain 0 - Kchain 1 + Kchain 2 - Kchain 3
```

Verified names:
- `SSet.chainComplexFunctor (C) : C ⥤ SSet ⥤ ChainComplex C ℕ` —
  `Mathlib/AlgebraicTopology/SimplicialSet/Homology/Basic.lean:41-42`; `X.chainComplex R` —
  `:74-75` (abbrev); `SSet.chainComplexMap (f : X ⟶ Y) (R : C) : X.chainComplex R ⟶
  Y.chainComplex R` — `:80-81` (abbrev; call shape `SSet.chainComplexMap κ (ModuleCat.of ℚ ℚ)`).
- `X.ιChainComplex (x : X _⦋n⦌) : R ⟶ (X.chainComplex R).X n := Sigma.ι ...` — `:86-87`;
  the coefficient `R` is implicit, inferred from the type ascription (the corpus's
  `faceChain` spelling, `GSTSphereFundamentalCycle.lean:299-304`; per the wave-10-B
  repair note, `rationalCoefficient` is dropped and `ModuleCat.of ℚ ℚ` is written
  explicitly — `rationalCoefficient` IS `ModuleCat.of ℚ ℚ`
  (`GSTGeometricRealizationStage2F.lean:66-67`, abbrev)).
- `singularChainsOf (X : TopCat) : ChainComplex (ModuleCat ℚ) ℕ :=
  ((singularChainComplexFunctor (ModuleCat ℚ)).obj rationalCoefficient).obj X` —
  `GSTSingularCohomologyMaps.lean:42-43`; DEFEQ to
  `(TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℚ ℚ)` because
  `singularChainComplexFunctor C = SSet.chainComplexFunctor C ⋙ (whiskeringLeft).obj
  TopCat.toSSet` (`Mathlib/AlgebraicTopology/SingularHomology/Basic.lean:36-38`) — the
  corpus's `chains_eq` is `rfl` (`GSTComponentCohomologyZero.lean:145-148`). This is what
  makes the `κChain` type ascription (and hence the bridge statement's syntactic type)
  legal.
- `X _⦋n⦌` notation — `Mathlib/AlgebraicTopology/SimplicialObject/Basic.lean:60`
  (scoped `Simplicial`).
- Universe note: `κ` fixes the SSet universe of `∂Δ[3]` to that of
  `TopCat.toSSet.obj (TopCat.of unitSphereType)` (unitSphereType : Type 0,
  `GSTSphereUnionComponents.lean:161`); `SSet.boundary.{u}` is universe-polymorphic
  (`Boundary.lean:37`) so it instantiates; the `HasCoproducts` instance needed by
  `chainComplexFunctor` at that universe is the same one the corpus's `singularChainsOf`
  already uses (CI-green).

### 6.2 The bridge theorems

```lean
/-- **THE PER-FACE BRIDGE.**  The chain map sends the i-th face generator to
the corpus's i-th face chain. -/
theorem κChain_face (i : Fin 4) :
    ModuleCat.Hom.hom (κChain.f 2) (Kchain i) = faceChain i := by
  -- the pinned generator-naturality receipt (element-level reading by calc):
  have h := ((∂Δ[3] : SSet).ι_chainComplexMap_f
    (TopCat.toSSet.obj (TopCat.of unitSphereType)) κ (ModuleCat.of ℚ ℚ) (Kface i))
  -- h : (∂Δ[3]).ιChainComplex (Kface i) ≫ (chainComplexMap κ R).f 2
  --     = (toSSet.obj S²).ιChainComplex (κ.app _ (Kface i))
  calc ModuleCat.Hom.hom (κChain.f 2) (Kchain i)
      = ModuleCat.Hom.hom (κChain.f 2)
          (((∂Δ[3] : SSet).ιChainComplex (Kface i) :
            ModuleCat.of ℚ ℚ ⟶ ((∂Δ[3] : SSet).chainComplex (ModuleCat.of ℚ ℚ)).X 2).hom
            (1 : ℚ)) := rfl
    _ = ModuleCat.Hom.hom
          (((∂Δ[3] : SSet).ιChainComplex (Kface i) ≫ κChain.f 2 :
            ModuleCat.of ℚ ℚ ⟶ singularChainsOf (TopCat.of unitSphereType)).X 2)
          (1 : ℚ) := rfl
    _ = ModuleCat.Hom.hom ((TopCat.toSSet.obj (TopCat.of unitSphereType)).ιChainComplex
          (κ.app (Opposite.op (SimplexCategory.mk 2)) (Kface i))) (1 : ℚ) := by
          rw [show ((∂Δ[3] : SSet).ιChainComplex (Kface i) ≫ κChain.f 2) = _ from h]
    _ = faceChain i := by rw [κ_face i]; rfl

/-- **THE RADIAL TRIANGULATION BRIDGE.**  The chain map induced by κ sends
the simplicial fundamental cycle of `∂Δ[3]` to the corpus's center-radial
fundamental cycle. -/
theorem κChain_zK :
    ModuleCat.Hom.hom (κChain.f 2) zK = fundCycle := by
  unfold zK
  simp only [LinearMap.map_sub, LinearMap.map_add]
  rw [κChain_face 0, κChain_face 1, κChain_face 2, κChain_face 3]
  rfl

/-- **THE CYCLE LAW PULLBACK.**  The image of the simplicial fundamental
cycle is a singular cycle (immediate from the bridge and the corpus's
`fundCycle_d`). -/
theorem κChain_zK_d :
    ModuleCat.Hom.hom ((singularChainsOf (TopCat.of unitSphereType)).d 2 1)
      (ModuleCat.Hom.hom (κChain.f 2) zK) = 0 := by
  rw [κChain_zK]
  exact fundCycle_d
```

Verified names:
- **`SSet.ι_chainComplexMap_f {n} (x : X _⦋n⦌) : X.ιChainComplex x ≫ (chainComplexMap f R).f n
  = Y.ιChainComplex (f.app _ x)`** — @[simp, reassoc],
  `Mathlib/AlgebraicTopology/SimplicialSet/Homology/Basic.lean:97-104`. This is the
  ιChainComplex-naturality receipt the task asked to locate: the chain functor's action on
  generator inclusions is stated directly (no colimit cofan gymnastics needed —
  `SSet.chainComplexXCofan`/`SSet.isColimitChainComplexXCofan`/`SSet.chainComplex_hom_ext`
  at `:108-122` exist if a repair needs them).
- Call shape: dot-notation `(∂Δ[3] : SSet).ι_chainComplexMap_f` supplies `X`; the remaining
  explicit section variables are `Y f R` then the lemma's own `x`
  (section variable order `variable (X Y Z : SSet.{w}) (f : X ⟶ Y) (g : Y ⟶ Z) (R : C)`,
  `Homology/Basic.lean:69`; only mentioned variables are included — `Z`, `g` drop out).
- Element-level congrArg discipline: `ModuleCat.hom_comp`, `LinearMap.comp_apply`,
  `ModuleCat.hom_add`/`hom_sub`, `LinearMap.map_sub`, `LinearMap.map_add` — the corpus's
  `faceChain_d` / `d_path_element` patterns (`GSTSphereFundamentalCycle.lean:327-361`,
  `GSTComponentCohomologyZero.lean:193-201`); the two `rfl` steps in the `calc` are the
  corpus's `e1`-style composite-application bridges (defeq at default transparency).
- `faceChain i` is *definitionally* `(((toSSet.obj S²).ιChainComplex
  (twoSimplexInject (faceSimplex i)) : ModuleCat.of ℚ ℚ ⟶ ...).hom 1`
  (`GSTSphereFundamentalCycle.lean:299-304`) — hence the terminal `rfl` after `κ_face`.
- `fundCycle := faceChain 0 - faceChain 1 + faceChain 2 - faceChain 3` —
  `GSTSphereFundamentalCycle.lean:400-401`; `fundCycle_d` — `:408-410`
  (`ModuleCat.Hom.hom ((singularChainsOf _).d 2 1) fundCycle = 0`).
- `κChain.f 2` vs the lemma's `(chainComplexMap κ R).f 2`: `κChain` is *defined* as
  `SSet.chainComplexMap κ (ModuleCat.of ℚ ℚ)`, so the `rw` matches after the def-delta
  (the `calc`'s first step pins it).

---

## 7. RISK LIST (the designated CI repair points)

- **(R-1) THE COE-SPELLING MATCH in `radialBary_map`'s application (§5.2/§5.3).** The pinned
  `toSSetObjEquiv_naturality_apply` contains `stdSimplex.map f` elaborated through the
  `ConcreteCategory SimplexCategory` coercion (`SimplexCategory/Basic.lean:595` +
  `ConcreteCategory/Basic.lean:100`); our `radialBary_map` is stated in the same spelling so
  the rewrite matches. If `rw`/`exact` still mismatches (`⇑F.unop` vs `⇑(F.unop.toOrderHom)`,
  `ConcreteCategory.hom` vs `Hom.toOrderHom`), repair with `show`/`dsimp only`
  restatement at the goal's own form — the corpus's `dsimp%` discipline
  (`GSTSingularCohomologyMaps.lean:212-215`). This is the file's #1 repair point.
- **(R-2) THE ETA-UNIFICATIONS at abstract degrees.** Applying
  `toSSetObjEquiv_naturality_apply` at abstract `M M'` (and `radialBary_map` at
  `M.unop.len` degrees) leans on structural eta for `Opposite` (`Data/Opposite.lean:41-53`)
  and `SimplexCategory` (`Defs.lean:51-56`). Fallback (spelled in §5.2): prepend
  `induction M using Opposite.rec with | _ A => induction M' using Opposite.rec with | _ B =>`
  (auto-reverting `F a`) and apply the lemmas at literal `op`-shapes; the rest of the proof
  is unchanged.
- **(R-3) THE `↾` PACKAGING of `κ`'s components.** The `app` field must be a Type-morphism;
  `↾κApp M` (`TypeCat.ofHom`, `Types/Basic.lean:142`) is the pinned spelling
  (`SSet.const` `SimplicialSet/Basic.lean:50`, `Subfunctor.lift`
  `Subfunctor/Image.lean:60`). If the anonymous-structure elaboration of the whole
  `where`-block stalls, split: `def κApp ...` (given) + `κ : ... where app M := ↾κApp M`.
- **(R-4) THE DEFEQ CHAIN in `missedVertex_of_mem`** (Set.ofPred-membership ↔
  ¬Surjective ↔ the ∃-form; FunLike-coe vs `asOrderHom`). All steps are `Iff.rfl`/defeq;
  if `exact hα (fun r => hcon r)` stalls, insert the explicit
  `have hns : ¬ Function.Surjective (fun j : Fin (M.unop.len + 1) => α j) := hα` and
  `exact absurd (fun r => hcon r) hns`.
- **(R-5) THE SUBCOMPLEX-CARRIER COERCION.** `(∂Δ[3] : SSet)` is `Subcomplex.toSSet`
  (abbrev) → `Subfunctor.toFunctor`; the carrier at `M` is the subtype, and
  `((∂Δ[3]).map F a).1 = (Δ[3]).map F a.1` is `rfl` (the `map` field is
  `↾fun x => ⟨F.map i x, G.map i x.prop⟩`, `Subfunctor/Basic.lean:143`). If the `rfl`
  (`h1` in §5.2's `hvert`) is blocked, repair with `Subfunctor.toFunctor_map` (the
  `@[simps map]` lemma; used at `Mathlib/AlgebraicTopology/SimplicialSet/Degenerate.lean:297`)
  + `Subcomplex.toSSet` unfolding. The universe unification of `boundary.{u} 3` with the
  target sset is automatic but verify the elaborated `κ`'s type once (§6.1 note).
- **(R-6) THE SUCCABOVE NORMALIZATIONS** (`Kface`'s membership, `Kface_apply`): the chain
  `objEquiv_symm_apply` → `δ`-unfold → `Fin.succAboveOrderEmb_apply`
  (+ `OrderEmbedding.toOrderHom_coe` if needed). All closed by `simp`/`simpa` with the
  spelled sets; the FC-2 discipline (`decide` on closed Fin equalities) applies if a
  residual survives.
- **(R-7) COEFFICIENT INSTANTIATION.** Every chain-level statement uses
  `ModuleCat.of ℚ ℚ` explicitly (the corpus's wave-10-B repaired shape — the implicit-`R`
  `ιChainComplex` calls infer it from ascriptions; `rationalCoefficient` is the same abbrev
  and only appears inside `singularChainsOf`'s definition). Do NOT pass
  `rationalCoefficient` explicitly to `ιChainComplex`/`ιChainComplex_d`-style calls — the
  pin's implicit-argument discipline (PORT NOTE of `GSTSphereTetrahedronCycle.lean:61-64`).
- **(R-8) THE SIBLING SEAM.** `Kface`/`Kchain`/`zK` are owned here because
  `GSTSphereSimplicialFundamentalClass` does not exist in the repo yet (verified by search).
  If it lands first, move §6.1's three definitions there verbatim and import it; the bridge
  statements (`κChain_face`, `κChain_zK`, `κChain_zK_d`) are unchanged. The alternating
  signs `+ - + -` match `fundCycle`'s (`GSTSphereFundamentalCycle.lean:400-401`) by design.
- **(R-9) `simp only [Quiver.Hom.op_unop] at hR`** in §5.2: the lemma's `f.op` argument
  normalizes to our `F`; if the `dsimp%`-prefixed statement resists, restate via
  `have hR' : ... := hR` after `rw [← Quiver.Hom.op_unop F] at hR`-style juggling, or
  apply the SYMM-form `TopCat.toSSetObjEquiv_symm_naturality` (`TopAdj.lean:99-102`)
  instead and bridge with `Equiv.apply_symm_apply` on both sides.

---

## 8. MODULE DOCSTRING (full text) + RECEIPTS

```lean
/-!
# THE RADIAL TRIANGULATION BRIDGE — the sset map κ : ∂Δ[3] ⟶ Sing(S²) (wave 13-B)

The simplicial avatar of the center-radial fundamental cycle: the boundary of
the tetrahedron, as a simplicial set (`∂Δ[3]`, the pinned `SSet.boundary`),
mapped into the singular simplicial set of the honest 2-sphere by the
barycentric center-radial assignment.  The four nondegenerate 2-faces of
`∂Δ[3]` land EXACTLY on the corpus's four radial `faceSimplex`
(`GSTSphereFundamentalCycle.lean`), so the induced chain map carries the
simplicial fundamental cycle `zK` to the corpus's `fundCycle` — THE BRIDGE
THEOREM `κChain_zK`.

* `radialBary` — the barycentric builder on an abstract vertex list;
* `radialBary_ne_zero` — the nonvanishing: a vertex list missing a tetrahedron
  vertex has no barycentric combination of total weight 1 at the origin (the
  fiber-weight reduction to `face_indep`; no monotonicity, no nonnegativity);
* `radialBary_map` — the general fiber-sum pushforward (the corpus's
  `faceBary_coface` at arbitrary degree) — the naturality engine;
* `κ` — the morphism of simplicial sets (components + naturality for ALL
  structure maps at once, via the fiber-sum computation);
* `κ_face` — the specialization: `κ (Kface i) = twoSimplexInject (faceSimplex i)`;
* `κChain_zK` — THE BRIDGE: `κ# (zK) = fundCycle`;
* `κChain_zK_d` — the cycle law pullback (via the corpus's `fundCycle_d`).

HONESTY LEDGER. Every statement here is unconditional. No `sorry`, no new
axioms, no `native_decide`. The GitHub CI lane `gst-sphere-fence-discharge.yml`
owns the kernel check.
-/
```

Receipts block (corpus convention):

```lean
#check radialBary
#check tetraWeight_indep_of_mem_compl
#check radialBary_ne_zero
#check missedVertex_of_mem
#check κMap_ne_zero
#check radialBary_continuous
#check κMap
#check κMap_continuous
#check Kface
#check Kface_apply
#check radialBary_map
#check κApp
#check κ
#check κ_face
#check κChain
#check Kchain
#check zK
#check κChain_face
#check κChain_zK
#check κChain_zK_d

#print axioms tetraWeight_indep_of_mem_compl
#print axioms radialBary_ne_zero
#print axioms κMap_continuous
#print axioms radialBary_map
#print axioms κ_face
#print axioms κChain_face
#print axioms κChain_zK
#print axioms κChain_zK_d
```

---

## 9. LINE COUNT ESTIMATE

| Section | Lines |
|---|---|
| header (imports, docstring, opens, settings) | 75 |
| §1 vertex assignment (radialBary, Lemma A, Lemma B) | 110 |
| §2 singular maps (missedVertex, κMap_ne_zero, continuity ×2, κMap) | 100 |
| §3 the four faces (Kface, Kface_apply) | 55 |
| §4 the sset map (radialBary_map, κApp, κ + naturality, κ_face) | 190 |
| §5 the bridge (κChain, Kchain, zK, three theorems) | 130 |
| receipts | 40 |
| PORT NOTES | 60 |
| **total** | **≈ 760** |

(Bracket 700–850; the naturality block §5.2 is the elastic part — R-1/R-2 repairs may cost
up to +60 lines of `show`-bridging.)

## 10. REGISTRATION

- New lib root in `lakefile.toml` (the monolith registry, flat layout):
  `[[lean_lib]] name = "GSTSphereRadialTriangulationLib"` with roots
  `["GSTSphereRadialTriangulation"]` (pattern of `GSTSphereFundamentalCycleLib` at
  `lakefile.toml:1772-1774`).
- Import list of the file itself (exactly three lines):
  `import Mathlib`, `import GSTSingularCohomologyMaps`, `import GSTSphereFundamentalCycle`.
- No new CI lane needed: the file joins the existing `gst-sphere-fence-discharge.yml` lane
  as a new ladder rung (RADIAL-TRIANGULATION).
