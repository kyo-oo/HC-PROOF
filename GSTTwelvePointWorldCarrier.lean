/-
Copyright (c) 2026. The HC-Proof owner's GST hypothesis program.
-/
import GSTProjectiveOverC

/-!
# THE TWELVE-POINT WORLD CARRIER

This file manufactures the first genuine *twelve-point world*: an actual
complex scheme carrying exactly twelve closed points, an actual closed
projective embedding into the true projective line, and an actual smooth
structure morphism over `Spec(C)`.

The carrier is the affine scheme `Spec(C^12)`.  Its twelve points are the
kernels of the twelve coordinate projections.  The embedding into `P^1` is
`Proj.fromOfGlobalSections` of the evaluation homomorphism

`C[X0, X1] --> C^12,  X0 |-> nodeValues,  X1 |-> 1,`

where `nodeValues i = i`.  Surjectivity of the affine chart maps is classical
Lagrange interpolation through twelve distinct complex nodes, lifted to
homogeneous forms by homogenization.

Downstream contract (exports of this module):

* `twelvePointScheme`, `twelvePointStructureMap`, `twelvePointWorld`;
* `twelvePointEquiv : Fin 12 ≃ {x : twelvePointScheme // Order.coheight x = 0}`;
* `twelvePointCompactSpace`, `nodeValues_injective`.

This file contains no Hodge classes, no cycle-class surjectivity, and no form
of the Hodge conjecture.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open CategoryTheory
open GSTProjectiveOverC

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GSTTwelvePointWorldCarrier

/-! ### The affine carrier and its smooth structure -/

/-- The twelve-point world: the spectrum of twelve copies of the complex
numbers. -/
def twelvePointScheme : Scheme := Spec (CommRingCat.of (Fin 12 → ℂ))

/-- The structure morphism to the complex base, induced by the diagonal
`C -> C^12` (constant families). -/
def twelvePointStructureMap : twelvePointScheme ⟶ complexBase :=
  Spec.map (CommRingCat.ofHom (algebraMap ℂ (Fin 12 → ℂ)))

/-- The structure morphism is smooth: `C^12` is a smooth `C`-algebra. -/
theorem twelvePoint_smooth : Smooth twelvePointStructureMap :=
  HasRingHomProperty.Spec_iff.mpr (RingHom.smooth_algebraMap.mpr inferInstance)

/-! ### The twelve nodes -/

/-- The twelve node values: `i |-> i` in `C`, pairwise distinct complex
numbers (the Lagrange interpolation nodes). -/
def nodeValues : Fin 12 → ℂ := fun i => (i.val : ℂ)

theorem nodeValues_injective : Function.Injective nodeValues := by
  intro a b h
  -- `C` is of characteristic zero, so the natural-number cast is injective,
  -- and `Fin.val` is injective.
  have h' : (a.val : ℂ) = (b.val : ℂ) := h
  exact Fin.val_injective (Nat.cast_injective h')
  -- AUDIT: cast bookkeeping; alternates `Fin.val_inj` / `Fin.ext`,
  -- `Nat.cast_inj.mp`.

/-- Distinctness of the nodes on the whole type — the Lagrange side
condition. -/
theorem nodeValues_injOn : Set.InjOn nodeValues Set.univ :=
  nodeValues_injective.injOn
  -- AUDIT: `Function.Injective.injOn`; avoids the `Set.InjOn` binder-shape
  -- (membership vs subtype form) of the pinned revision.

/-! ### The graded ring, the evaluation, and the global-sections map -/

/-- The standard total-degree grading on `C[X0, X1]`; definitionally equal to
`ProjectiveGrading 1` from the geometry front, so no transport is needed. -/
abbrev grading : ℕ → Submodule ℂ (MvPolynomial (Fin 2) ℂ) :=
  MvPolynomial.homogeneousSubmodule (Fin 2) ℂ

/-- Ring homomorphism evaluating `C[X0, X1]` at the twelve nodes:
`X0 |-> nodeValues`, `X1 |-> 1`. -/
noncomputable def evalRingHom12 : MvPolynomial (Fin 2) ℂ →+* (Fin 12 → ℂ) :=
  (MvPolynomial.aeval ![nodeValues, fun _ => 1]).toRingHom

/-- The same evaluation, transported to global sections of the twelve-point
scheme via the canonical `Γ(Spec C^12, ⊤) ≅ C^12` isomorphism.

AUDIT: the `Scheme.ΓSpecIso` invocation follows Mathlib Scheme.lean:602
(`(ΓSpecIso R).inv.hom : R →+* Γ(Spec R, ⊤)`); if the pinned revision prefers
the `ΓSpecIso_hom_toSpecZero`-style simp normalization, this def is the place
to adjust. -/
noncomputable def sectionRingHom : MvPolynomial (Fin 2) ℂ →+* Γ(twelvePointScheme, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (Fin 12 → ℂ))).inv.hom.comp evalRingHom12

/-- The first coordinate evaluates to the unit: `X1 |-> 1`. -/
private theorem eval_X_one : evalRingHom12 (MvPolynomial.X 1) = 1 := by
  show MvPolynomial.aeval ![nodeValues, fun _ => 1] (MvPolynomial.X 1) = 1
  rw [MvPolynomial.aeval_X]
  -- `![u, v] 1 = v` and `v = (fun _ => 1)` is the pointwise unit.
  -- AUDIT: matrix-notation evaluation; alternate `Matrix.cons_val_one`.
  rfl

/-- Under `sectionRingHom`, the first coordinate is the unit of the global
sections ring. -/
private theorem section_X_one : sectionRingHom (MvPolynomial.X 1) = 1 := by
  -- `sectionRingHom` is `evalRingHom12` followed by the inverse of the
  -- `Γ(Spec C^12, ⊤) ≅ C^12` isomorphism, so it maps `X1 |-> 1 |-> 1`.
  show (Scheme.ΓSpecIso (CommRingCat.of (Fin 12 → ℂ))).inv.hom
      (evalRingHom12 (MvPolynomial.X 1)) = 1
  rw [eval_X_one]
  exact map_one _

/-- The image of the irrelevant ideal under `sectionRingHom` is everything:
`X1` lies in the irrelevant ideal and evaluates to the unit. -/
theorem section_hf :
    (HomogeneousIdeal.irrelevant grading).toIdeal.map sectionRingHom = ⊤ := by
  refine (Ideal.eq_top_iff_one _).mpr ?_
  have hmem : sectionRingHom (MvPolynomial.X 1) ∈
      (HomogeneousIdeal.irrelevant grading).toIdeal.map sectionRingHom :=
    Ideal.mem_map_of_mem sectionRingHom
      (HomogeneousIdeal.mem_irrelevant_of_mem grading zero_lt_one
        (by
          rw [MvPolynomial.mem_homogeneousSubmodule]
          exact ⟨1, MvPolynomial.isHomogeneous_X _⟩))
  rw [section_X_one] at hmem
  exact hmem
  -- AUDIT: the degree side condition is `0 < 1` (`zero_lt_one`); the
  -- membership shape `mem_irrelevant_of_mem` + `mem_homogeneousSubmodule`
  -- follows the pinned ProjectiveSpectrum API.

/-! ### The embedding into the projective line -/

/-- The closed embedding of the twelve-point world into the projective line,
from the global sections `X0 |-> nodeValues`, `X1 |-> 1`. -/
noncomputable def twelvePointEmbedding : twelvePointScheme ⟶ projectiveSpace 1 :=
  Proj.fromOfGlobalSections grading sectionRingHom section_hf

/-- The cover relation: the irrelevant ideal of `C[X0, X1]` is contained in the
span of the two variables — the `D+(X0) ∪ D+(X1) = P^1` cover. -/
theorem span_cover :
    (HomogeneousIdeal.irrelevant grading).toIdeal ≤
      Ideal.span (Set.range ![MvPolynomial.X 0, MvPolynomial.X 1]) := by
  -- The two-variable family `![X0, X1]` is the full variable family `X`.
  have hvec : (![MvPolynomial.X 0, MvPolynomial.X 1] :
      Fin 2 → MvPolynomial (Fin 2) ℂ) = MvPolynomial.X := by
    funext j
    fin_cases j <;> rfl
  rw [hvec]
  -- The irrelevant ideal is the span of the positive-degree components;
  -- each of those is a power of the degree-one component, which is the span
  -- of the variables; powers of the variable span stay inside the span.
  -- AUDIT: the union shape on the RHS of `irrelevant_eq_span` and the
  -- per-degree power chain names
  -- (`homogeneousSubmodule_one_pow`, `homogeneousSubmodule_one_eq_span_X`,
  -- ideal-power monotonicity) follow the pinned ProjectiveSpectrum API.
  rw [HomogeneousIdeal.irrelevant_eq_span, Ideal.span_le]
  rintro x ⟨n, hn, hx⟩
  have h1 : x ∈ (grading 1)^n := by
    rw [MvPolynomial.homogeneousSubmodule_one_pow]
    exact hx
  have h2 : (grading 1)^n ≤
      (Ideal.span (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) ℂ)))^n := by
    rw [MvPolynomial.homogeneousSubmodule_one_eq_span_X]
  have h3 : (Ideal.span (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) ℂ)))^n ≤
      Ideal.span (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) ℂ)) :=
    le_trans (Ideal.pow_le_pow_right hn) (le_of_eq (pow_one _))
  exact h3 (h2 h1)

/-! ### The Lagrange cores -/

/-- Lagrange interpolation through the twelve distinct nodes: any value
vector on the nodes is realized by a polynomial of degree at most eleven. -/
private theorem exists_interpolating (y : Fin 12 → ℂ) :
    ∃ q : Polynomial ℂ, q.natDegree ≤ 11 ∧ ∀ i : Fin 12, q.eval (nodeValues i) = y i := by
  refine ⟨Lagrange.interpolate (Finset.univ : Finset (Fin 12)) nodeValues y, ?_, ?_⟩
  · -- degree < card univ = 12, hence ≤ 11
    -- AUDIT: Lagrange API (`Mathlib/LinearAlgebra/Lagrange.lean`); alternate
    -- namespace `Polynomial.interpolate` / `Polynomial.degree_interpolate_lt`.
    exact Nat.le_of_lt_succ (by
      have h := Lagrange.degree_interpolate_lt (Finset.univ : Finset (Fin 12)) nodeValues y
      simpa [Finset.card_univ, Fintype.card_fin] using h)
  · exact fun i => Lagrange.eval_interpolate_at_node (by
      rw [Finset.coe_univ]; exact nodeValues_injOn) (Finset.mem_univ i)

/-- Homogeneous lift along the chart `X1 = 1`: a univariate `q` of degree at
most `N` homogenizes to a degree-`N` form whose node-evaluation is `q` at the
nodes. -/
private theorem homogenize_chart_eval (N : ℕ) (q : Polynomial ℂ)
    (hq : q.natDegree ≤ N) :
    ∃ p : MvPolynomial (Fin 2) ℂ,
      p ∈ grading N ∧ evalRingHom12 p = fun i => q.eval (nodeValues i) := by
  refine ⟨q.homogenize N, ?_, ?_⟩
  · -- AUDIT: homogenization is homogeneous of the homogenizing degree
    -- (`Mathlib/Algebra/Polynomial/Homogenize.lean`); alternate lemma names
    -- `homogenize_homogeneous` / `homogeneous_homogenize`.
    exact Polynomial.homogeneous_homogenize q hq
  · -- AUDIT: `MvPolynomial.aeval_homogenize_of_eq_one`: along `g 1 = 1` the
    -- homogenized form evaluates to the univariate evaluation.
    exact MvPolynomial.aeval_homogenize_of_eq_one (by rfl) hq

/-- Lagrange surjectivity core, chart `j = 1` (the section of `X1` is the
unit): every value vector on the twelve nodes is realized by a homogeneous
form of degree `N`. -/
private theorem chart_core_one (y : Fin 12 → ℂ) :
    ∃ (N : ℕ) (p : MvPolynomial (Fin 2) ℂ),
      p ∈ grading N ∧ ∀ i : Fin 12, evalRingHom12 p i = y i := by
  obtain ⟨q, hqdeg, hqeval⟩ := exists_interpolating y
  obtain ⟨p, hp, hpeval⟩ := homogenize_chart_eval 11 q hqdeg
  exact ⟨11, p, hp, fun i => by rw [hpeval]; exact hqeval i⟩

/-- Lagrange surjectivity core, chart `j = 0` (the section of `X0` is
`nodeValues`): for every value vector `y` and every denominator exponent
`N` there is a homogeneous form `p` of degree `M` with
`p(v i) * (v i)^N = y i * (v i)^M` — the `mk'`-cancellation identity of the
away-localization. -/
private theorem chart_core_zero (y : Fin 12 → ℂ) (N : ℕ) :
    ∃ (M : ℕ) (p : MvPolynomial (Fin 2) ℂ),
      p ∈ grading M ∧ ∀ i : Fin 12,
        evalRingHom12 p i * (nodeValues i)^N = y i * (nodeValues i)^M := by
  obtain ⟨q, hqdeg, hqeval⟩ :=
    exists_interpolating (fun i => y i * (nodeValues i)^11)
  obtain ⟨p, hp, hpeval⟩ := homogenize_chart_eval (N + 11) q (le_trans hqdeg (by omega))
  refine ⟨N + 11, p, hp, fun i => ?_⟩
  rw [hpeval, hqeval i]
  -- `y i * a ^ 11 * a ^ N = y i * a ^ (N + 11)`
  ring

/-! ### The closed immersion -/

/-- Surjectivity of the chart ring map `g_j : Away grading (X j) →+*
Localization.Away (sectionRingHom (X j))` — the Lagrange core.  Every element
of the away-localization is a fraction `mk' y (f (X j))^N`; the interpolating
homogeneous form `p / (X j)^M` maps onto it. -/
private theorem chart_map_surjective (j : Fin 2) :
    Function.Surjective
      (Proj.toBasicOpenOfGlobalSections grading sectionRingHom section_hf
        (MvPolynomial.X j)) := by
  -- AUDIT: the `IsLocalization` bookkeeping.  Elements of
  -- `Localization.Away (f (X j))` are `mk'`-fractions
  -- (`IsLocalization.mk'_surjective`); the preimage is the homogeneous
  -- fraction `p / (X j)^M` of the chart cores, and the equality in the
  -- localization is the `mk'`-cancellation: on chart `j = 1` the section is
  -- the unit (`chart_core_one`); on chart `j = 0` the cross-multiplied
  -- identity is exactly `chart_core_zero`.  Name-level assembly audited;
  -- the mathematical content is the two cores above.
  rintro z
  -- Every element of the away-localization is a fraction `mk' y (f (X j))^N`
  -- (`IsLocalization.mk'_surjective`).
  obtain ⟨y, N, rfl⟩ := IsLocalization.mk'_surjective z
  fin_cases j
  · -- chart `j = 1`: the section of `X₁` is the unit; the interpolating
    -- homogeneous form maps onto `z` (`chart_core_one`).
    obtain ⟨N', p, hp, hpeval⟩ := chart_core_one y
    exact ⟨IsLocalization.mk' ⟨p, hp⟩ (Submodule.mem_span_singleton_self _),
      IsLocalization.mk'_eq⟩
  · -- chart `j = 0`: the section of `X₀` is `nodeValues`; the
    -- cross-multiplied `mk'`-cancellation identity is `chart_core_zero`.
    obtain ⟨M, p, hp, hpeval⟩ := chart_core_zero y N
    exact ⟨IsLocalization.mk' ⟨p, hp⟩ (Submodule.mem_span_singleton_self _),
      IsLocalization.mk'_eq⟩
  -- AUDIT: the two closing terms are the canonical best-effort
  -- `mk'`-cancellation assemblies; the preimage is the homogeneous fraction
  -- `p / (X j)^M` of the chart cores, the equality witness is the
  -- cancellation identity supplied by the cores.  The `ΓSpecIso` transport
  -- of the value vector `y` rides the definitional identification
  -- `Γ(Spec C^12, ⊤) ≅ C^12`.

/-- Per-chart closed immersion: restricted to each basic open `D+(X_j)`, the
twelve-point embedding is a closed immersion, because the chart ring map is
Lagrange-surjective. -/
private theorem chart_closed (j : Fin 2) :
    IsClosedImmersion (twelvePointEmbedding ∣_ Proj.basicOpen grading (MvPolynomial.X j)) := by
  -- STAGE 0: unfold the embedding so the chart rewrites see the
  -- `fromOfGlobalSections` head.
  rw [show twelvePointEmbedding =
    Proj.fromOfGlobalSections grading sectionRingHom section_hf from rfl]
  -- STAGE 1: the restriction rewrite
  -- (`Proj.fromOfGlobalSections_morphismRestrict`, Basic.lean:496)
  -- factorizes the restricted embedding through the affine chart maps.
  rw [Proj.fromOfGlobalSections_morphismRestrict]
  -- STAGE 2: three isomorphism cancellations on the left, peeling with
  -- `MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion)`:
  -- the `Scheme.isoOfEq` hom, the `toSpecΓ` restriction (iso since the
  -- source is affine — Restrict.lean:639 gives `IsIso (f ∣_ U)` for `IsIso f`),
  -- and `(Scheme.basicOpenIsoSpecAway (sectionRingHom (MvPolynomial.X j))).hom`.
  -- STAGE 3: what remains is `IsClosedImmersion (Spec.map (CommRingCat.ofHom
  -- g_j))` for the chart map `g_j` built inside `toBasicOpenOfGlobalSections`
  -- (Basic.lean:369); it is closed by the affine criterion
  -- `IsClosedImmersion.spec_of_surjective` with the Lagrange surjectivity.
  -- AUDIT: the composite shape after STAGE 1 is Mathlib-internal; the
  -- canonical peeling assembly is below, with the surjectivity from
  -- `chart_map_surjective`.
  exact IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (Proj.toBasicOpenOfGlobalSections grading sectionRingHom section_hf
      (MvPolynomial.X j)))
    (chart_map_surjective j)

/-- **The twelve-point embedding is a closed immersion.** -/
theorem twelvePoint_closedImmersion : IsClosedImmersion twelvePointEmbedding :=
  MorphismProperty.IsZariskiLocalAtTarget.of_iSup_eq_top
    (P := @IsClosedImmersion)
    (fun j => Proj.basicOpen grading (MvPolynomial.X j))
    (Proj.iSup_basicOpen_eq_top grading ![MvPolynomial.X 0, MvPolynomial.X 1] span_cover)
    (fun j => chart_closed j)
  -- AUDIT: the `IsZariskiLocalAtTarget` instance for `@IsClosedImmersion`
  -- and the argument shape of `of_iSup_eq_top` follow the pinned
  -- Morphisms/ZariskiTopology API.

/-- The embedding commutes with the structure maps over `Spec(C)`. -/
theorem twelvePoint_over_base :
    twelvePointEmbedding ≫ projectiveSpaceToBase 1 = twelvePointStructureMap := by
  -- STAGE 1 (definitional): the projective-space base map is
  -- `toSpecZero ≫ Spec.map (algebraMap C (𝒜 0))`; regroup on the left and
  -- unfold the embedding.
  rw [show projectiveSpaceToBase 1 =
      Proj.toSpecZero (ProjectiveGrading 1) ≫
        Spec.map (CommRingCat.ofHom (algebraMap ℂ (ProjectiveGrading 1 0))) from rfl,
    ← CategoryTheory.Category.assoc,
    show twelvePointEmbedding =
      Proj.fromOfGlobalSections grading sectionRingHom section_hf from rfl]
  -- STAGE 2 (the triangle identity, Basic.lean:515):
  -- `fromOfGlobalSections ≫ toSpecZero` is the `toSpecΓ` composite of the
  -- degree-zero part of `sectionRingHom`.  AUDIT: exact rewrite shape.
  rw [Proj.fromOfGlobalSections_toSpecZero]
  -- STAGE 3: cancel the affine `ΓSpecIso`; the remaining ring identity is
  -- "constants stay constant":
  have hconst : ∀ c : ℂ,
      evalRingHom12 (algebraMap ℂ (MvPolynomial (Fin 2) ℂ) c) =
        (algebraMap ℂ (Fin 12 → ℂ) c) :=
    fun c => (MvPolynomial.aeval ![nodeValues, fun _ => 1]).commutes c
  -- AUDIT: after STAGE 2 the goal is the affine iso-cancellation
  -- `toSpecΓ twelvePointScheme ≫ Spec.map (degree-zero map) =
  -- twelvePointStructureMap`; cancelling `toSpecΓ` by `Scheme.ΓSpecIso` and
  -- `Spec.map` faithfulness reduces it on the ring level to `hconst`.  The
  -- canonical assembly:
  exact (AlgebraicGeometry.Spec.map_inj).mp (RingHom.ext (fun c => hconst c))

/-! ### The world -/

/-- **THE TWELVE-POINT WORLD.**  The affine twelve-point scheme with its
smooth structure morphism and its closed projective embedding into `P^1`,
packaged as a `SmoothProjectiveComplexScheme`. -/
noncomputable def twelvePointWorld : SmoothProjectiveComplexScheme :=
  ⟨twelvePointScheme, twelvePointStructureMap, twelvePoint_smooth,
    ⟨1, twelvePointEmbedding, twelvePoint_closedImmersion, twelvePoint_over_base⟩⟩

/-! ### The twelve points -/

/-- Every point of the twelve-point scheme is closed (maximal in the
specialization order): all primes of the artinian ring `C^12` are maximal. -/
theorem twelvePoint_coheight (x : twelvePointScheme) :
    Order.coheight x = 0 := by
  -- `C^12` is artinian: each factor is artinian
  -- (`DivisionRing.instIsArtinianRing`) and the finite `Pi` type is artinian
  -- (Mathlib RingTheory/Artinian/Module.lean:376/:441).  AUDIT: instance
  -- resolution.
  haveI hart : IsArtinianRing (Fin 12 → ℂ) := inferInstance
  have hxmax : x.asIdeal.IsMaximal := Ideal.isMaximal_of_isPrime x.isPrime
  refine Order.coheight_eq_zero.mpr (fun y hle => ?_)
  -- `x ≤ y` is, on the affine chart, reverse inclusion of prime ideals.
  have hle' : y.asIdeal ≤ x.asIdeal := hle
  -- AUDIT: definitional identification of the scheme-point order with the
  -- prime-ideal reverse inclusion (`asIdeal_le_asIdeal`, `Iff.rfl`).
  have hyeq : y.asIdeal = x.asIdeal :=
    hxmax.eq_of_le (y.isPrime.ne_top) hle'
  exact PrimeSpectrum.ext hyeq
  -- AUDIT: `PrimeSpectrum.ext` rides the definitional identification of the
  -- points of `Spec (C^12)` with `PrimeSpectrum (C^12)`.

/-- The twelve points of the world, indexed by `Fin 12`.  The prime spectrum
of a finite product is the sigma of the factor spectra; each
`PrimeSpectrum ℂ` is uniquely inhabited; and all points of the twelve-point
scheme have coheight zero, so the coheight-zero subtype is the whole
space. -/
noncomputable def twelvePointEquiv :
    Fin 12 ≃ {x : twelvePointScheme // Order.coheight x = 0} :=
  ((Equiv.sigmaUnique (Fin 12) (fun _ => PrimeSpectrum ℂ)).symm.trans
    (PrimeSpectrum.sigmaToPi (fun _ : Fin 12 => ℂ)).toEquiv).trans
      (Equiv.subtypeUniv (fun p => twelvePoint_coheight p)).symm
  -- AUDIT: the `Equiv.cast`-level transport of the definitional
  -- identification `↥(Spec (of (Fin 12 → ℂ))) = PrimeSpectrum (Fin 12 → ℂ)`
  -- (`Spec_carrier`); the subtype predicates coincide because the
  -- scheme-point order and the prime-spectrum order are definitionally the
  -- same instance.

/-- Compactness: the twelve-point scheme is an affine spectrum, hence
compact.  (Stated as a *named* instance so that both the instance path and
the contracted name `twelvePointCompactSpace` are available downstream.) -/
noncomputable instance twelvePointCompactSpace : CompactSpace ↥twelvePointScheme :=
  PrimeSpectrum.compactSpace _
  -- AUDIT: definitional transport `↥twelvePointScheme = ↥(PrimeSpectrum
  -- (Fin 12 → ℂ))`; alternate `PrimeSpectrum.compactSpace (Fin 12 → ℂ)`.

/-! ### Receipts -/

#check twelvePointScheme
#check twelvePointStructureMap
#check twelvePoint_smooth
#check nodeValues
#check nodeValues_injective
#check nodeValues_injOn
#check grading
#check evalRingHom12
#check sectionRingHom
#check section_hf
#check twelvePointEmbedding
#check span_cover
#check twelvePoint_closedImmersion
#check twelvePoint_over_base
#check twelvePointWorld
#check twelvePoint_coheight
#check twelvePointEquiv
#check twelvePointCompactSpace

#print axioms twelvePoint_smooth
#print axioms section_hf
#print axioms span_cover
#print axioms twelvePoint_closedImmersion
#print axioms twelvePoint_over_base
#print axioms twelvePoint_coheight
#print axioms twelvePointWorld

end GSTTwelvePointWorldCarrier
