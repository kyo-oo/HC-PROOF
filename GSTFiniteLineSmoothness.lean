import Mathlib
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import GSTFiniteLineRing
import GSTProjectiveOverC
import GSTFiniteLineWorldCarrier

/-
Copyright (c) 2026. The HC-PROOF campaign. All rights reserved.

# WAVE 67-B — F3 STAGE 0 + STAGE 2: the smoothness substrate (paste section)

The F3 (smoothness) substrate lemmas of the finite-line world, per the frozen
wave-67 route (`repairs/wave67_A_smoothness_route.md`, sections Stage 0 and
Stage 2).  This is a STANDALONE PASTE-SECTION file: the preamble and namespace
follow the `GSTFiniteLineClosedImmersion.lean` pattern; the assembler pastes
the body into `GSTFiniteLineSmoothness.lean` (the F3 module) behind Stage 1
(W67-C, the chart equivalence).

## Contents

STAGE 0 (the shared substrate, twins of CI-green corpus lemmas):

* `linePartner` (T1) — the partner involution on `Fin (2*M)`: the other
  element of `j`'s coordinate block `{2b, 2b+1}`, with the spec lemmas
  `linePartner_ne` (≠ j), `linePartner_block` (same block: j'/2 = j/2),
  `linePartner_involution` (j'' = j);
* `lineCoverHomogeneousOneQ` / `lineCoverHomogeneousQ` (T2/T2') — the
  variables are homogeneous of degree 1 (the ∃-form feeds
  `Proj.iSup_basicOpen_eq_top'`, the degree-1 form feeds `awayι`);
* `lineCoverAdjoin` (T3) — the variables adjoin-generate the quotient over
  its degree-0 piece (the twin of the green `span_cover`,
  GSTFinitePointWorldCarrier.lean:202-215, lifted through
  `lineQuotientMap_surjective`);
* `blockEval` / `blockEval_mem_ker` / `blockEvalQuot` (T4/T5) — the block
  projection `ℂ[x_0..x_{2M-1}] → ℂ[t]` (X j ↦ 1, X j' ↦ t, everything else
  ↦ 0), which kills the cross ideal and hence descends to the quotient;
* `hzero` (T6) — constants through degree zero (the
  `SetLike.GradeZero.coe_algebraMap` fold).

STAGE 2 (the chart square — `chartRingHom` is an EXTERNAL W67-C PLUG, see
the §5 contract):

* `chart_awayι_comp'` — the standalone form: the away-chart of the structure
  map is the `Spec` of the canonical ℂ-structure composite of the chart;
* `chart_awayι_comp` — the plug-facing form (chartRingHom + its defining
  equation as explicit binders).

## Deviations from the route-map draft (all pin-verified, see the report)

1. `linePartner` is defined by the parity split `if j.val % 2 = 0 then
   j.val + 1 else j.val - 1`, NOT by `j.val ^^^ 1`: the pin's `omega` frontend
   (lean4 v4.33.0-rc2, src/Lean/Elab/Tactic/Omega/Frontend.lean) has NO
   `Nat.xor` support (xor terms become opaque atoms), so the draft's
   `⟨j.val ^^^ 1, by omega⟩` cannot compile.  The spec lemmas (ne/block/
   involution) are unchanged — all downstream uses (Stage 1's `chartRatio`,
   `blockEval`) go through the INDEX `linePartner M j` and these lemmas only.
2. `blockEvalQuot` uses `Ideal.Quotient.liftₐ (crossIdeal M) (blockEval M j)
   (pointwise)`: at the pin (Mathlib/RingTheory/Ideal/Quotient/Operations.lean:471)
   `liftₐ` has NO explicit base-ring argument and takes the POINTWISE
   hypothesis `∀ a ∈ I, f a = 0` — the CI-green carrier spelling
   (GSTFiniteLineWorldCarrier.lean:285-288), not the draft's `liftₐ ℂ … ≤ ker`
   spelling.
3. `blockEval` writes `MvPolynomial.X (0 : Fin 1)` (corpus style,
   GSTTruncatedWorldCohomologyRing.lean:103) instead of the draft's
   `MvPolynomial.X ()`: the unit-notation does not elaborate at `Fin 1`.
4. The `hm : 0 < 1` argument of `awayι` is the term `zero_lt_one` (the green
   ClosedImmersion spelling, GSTFiniteLineClosedImmersion.lean:226) instead
   of `by norm_num`.
5. THE `chartRingHom` CONTRACT (§5 below): the correct type is
   `ℂ →+* Away (lineGrading M) (q (X j))` (the chart's ℂ-STRUCTURE ring hom,
   route map Stage 1: `(fromZeroRingHom 𝒜 (Submonoid.powers f)).comp
   (algebraMap ℂ (𝒜 0))`), NOT `MvPolynomial (Fin 1) ℂ →+* Away …`: with the
   latter the chart-square statement is ill-typed (its RHS would live in
   `Spec ℂ[t]` while the LHS lands in `Spec ℂ`).

Honesty ledger: zero `sorry`, zero new axioms, zero `native_decide`.  Every
non-local name is pin-verified at Mathlib 51e6992efd06126df61a496bebf8f49482a4e129
(reference copies under research/pin/mathlib-51e6992/) or CI-green in the
corpus (file:line in each docstring).
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry CategoryTheory
open GSTProjectiveOverC GSTFiniteLineRing GSTFiniteLineWorldCarrier
open MvPolynomial DirectSum

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GSTFiniteLineSmoothness

/-! ## §1 Stage 0 (T1) — the partner involution on the coordinate indices -/

/-- **THE PARTNER INVOLUTION (T1)** — `linePartner M j` is the OTHER element
of `j`'s coordinate block `{X (2b), X (2b+1)}` (block `b = j / 2`).  The
route map's spelling is `j.val ^^^ 1`; here it is the parity split, which is
`omega`-provable at the pin (see Deviation 1 in the header).  The spec is
carried entirely by `linePartner_ne`, `linePartner_block` and
`linePartner_involution` below. -/
def linePartner (M : ℕ) [NeZero M] (j : Fin (2 * M)) : Fin (2 * M) :=
  ⟨if j.val % 2 = 0 then j.val + 1 else j.val - 1, by
    have h : j.val < 2 * M := j.isLt
    by_cases hj : j.val % 2 = 0
    · rw [if_pos hj]
      omega
    · rw [if_neg hj]
      omega⟩

/-- The value bridge (the corpus's `blockRot_val` pattern,
GSTFiniteLineWorldCarrier.lean:122-123: a `rfl` unfolding of a `Fin`-valued
def through its `val`). -/
theorem linePartner_val (M : ℕ) [NeZero M] (j : Fin (2 * M)) :
    (linePartner M j).val = if j.val % 2 = 0 then j.val + 1 else j.val - 1 :=
  rfl

/-- The partner of an even index is the next index (the block's odd
element). -/
theorem linePartner_val_even (M : ℕ) [NeZero M] (j : Fin (2 * M))
    (hj : j.val % 2 = 0) : (linePartner M j).val = j.val + 1 := by
  rw [linePartner_val, if_pos hj]

/-- The partner of an odd index is the previous index (the block's even
element). -/
theorem linePartner_val_odd (M : ℕ) [NeZero M] (j : Fin (2 * M))
    (hj : ¬ j.val % 2 = 0) : (linePartner M j).val = j.val - 1 := by
  rw [linePartner_val, if_neg hj]

/-- **T1 (ne)** — the partner is the OTHER element of the block. -/
theorem linePartner_ne (M : ℕ) [NeZero M] (j : Fin (2 * M)) :
    linePartner M j ≠ j := by
  intro h
  have hv : (linePartner M j).val = j.val := by rw [h]
  rw [linePartner_val] at hv
  by_cases hj : j.val % 2 = 0
  · rw [if_pos hj] at hv
    omega
  · rw [if_neg hj] at hv
    omega

/-- **T1 (block)** — the partner lives in the same coordinate block:
`j' / 2 = j / 2`.  This is the block-combinatorics input of
`blockEval_mem_ker` (§3) and of Stage 1's cross-pair bookkeeping. -/
theorem linePartner_block (M : ℕ) [NeZero M] (j : Fin (2 * M)) :
    (linePartner M j).val / 2 = j.val / 2 := by
  rw [linePartner_val]
  by_cases hj : j.val % 2 = 0
  · rw [if_pos hj]
    omega
  · rw [if_neg hj]
    omega

/-- **T1 (involution)** — partnering twice is the identity. -/
theorem linePartner_involution (M : ℕ) [NeZero M] (j : Fin (2 * M)) :
    linePartner M (linePartner M j) = j := by
  have hval : (linePartner M (linePartner M j)).val = j.val := by
    by_cases hj : j.val % 2 = 0
    · have hp : (linePartner M j).val = j.val + 1 := linePartner_val_even M j hj
      have hp' : ¬ (linePartner M j).val % 2 = 0 := by
        rw [hp]
        omega
      rw [linePartner_val_odd M (linePartner M j) hp', hp]
      omega
    · have hp : (linePartner M j).val = j.val - 1 := linePartner_val_odd M j hj
      have hp' : (linePartner M j).val % 2 = 0 := by
        rw [hp]
        omega
      rw [linePartner_val_even M (linePartner M j) hp', hp]
      omega
  exact Fin.ext hval

/-! ## §2 Stage 0 (T2/T2'/T3) — the D₊(q (X j)) cover twins -/

/-- **THE COVER TWIN (DEGREE ONE, T2')** — every variable's image in the
quotient grading is homogeneous of degree 1: the `f_deg` argument of
`Proj.awayι` / `Proj.basicOpenIsoSpec` at `f := q (X j)`, `m := 1`.  The
membership core is the substrate's `lineQuotientMap_mem_lineGrading`
(GSTFiniteLineRing.lean:167-171) fed by `isHomogeneous_X`
(MvPolynomial/Homogeneous.lean:178, `R` explicit) through
`mem_homogeneousSubmodule` (:101, `Iff.rfl`) — the substrate's own
`crossMonomials_homogeneous` cascade (GSTFiniteLineRing.lean:93-94). -/
theorem lineCoverHomogeneousOneQ (M : ℕ) (j : Fin (2 * M)) :
    lineQuotientMap M (MvPolynomial.X j) ∈ lineGrading M 1 :=
  lineQuotientMap_mem_lineGrading M 1 (MvPolynomial.X j)
    ((MvPolynomial.mem_homogeneousSubmodule 1 (MvPolynomial.X j)).mpr
      (MvPolynomial.isHomogeneous_X ℂ j))

/-- **THE COVER TWIN (HOMOGENEITY, T2)** — the ∃-degree form: the `hfn` side
condition of `Proj.iSup_basicOpen_eq_top'`
(Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Basic.lean:97-99) at
`f := fun j => lineQuotientMap M (MvPolynomial.X j)` (the twin of the green
`variables_homogeneous`, GSTFinitePointWorldCarrier.lean:219-223). -/
theorem lineCoverHomogeneousQ (M : ℕ) (j : Fin (2 * M)) :
    ∃ n : ℕ, lineQuotientMap M (MvPolynomial.X j) ∈ lineGrading M n :=
  ⟨1, lineCoverHomogeneousOneQ M j⟩

/-- **THE COVER TWIN (ADJOIN, T3)** — the variables generate the quotient as
an algebra over its degree-0 piece: the `hf` side condition of
`Proj.iSup_basicOpen_eq_top'` (Basic.lean:97-99).  The twin of the green
`span_cover` (GSTFinitePointWorldCarrier.lean:202-215), with the induction
lifted through `lineQuotientMap_surjective` (GSTFiniteLineRing.lean:137-144):
the `C`-case rides `S.algebraMap_mem` on the degree-0 image (the
`SetLike.GradeZero` algebra instances,
Mathlib/Algebra/DirectSum/Internal.lean:364-415), the `mul_X` case rides
`Algebra.subset_adjoin ∘ Set.mem_range_self`. -/
theorem lineCoverAdjoin (M : ℕ) :
    Algebra.adjoin ↥(lineGrading M 0)
      (Set.range (fun j : Fin (2 * M) => lineQuotientMap M (MvPolynomial.X j))) = ⊤ := by
  set S := Algebra.adjoin ↥(lineGrading M 0)
      (Set.range (fun j : Fin (2 * M) => lineQuotientMap M (MvPolynomial.X j)))
  refine top_unique fun x hx => ?_
  obtain ⟨p, rfl⟩ := lineQuotientMap_surjective M x
  clear hx
  induction p using MvPolynomial.induction_on with
  | C a =>
      exact S.algebraMap_mem
        ⟨lineQuotientMap M (MvPolynomial.C a),
          lineQuotientMap_mem_lineGrading M 0 (MvPolynomial.C a)
            ((MvPolynomial.mem_homogeneousSubmodule 0 (MvPolynomial.C a)).mpr
              (MvPolynomial.isHomogeneous_C (σ := Fin (2 * M)) (R := ℂ) a))⟩
  | add p q hp hq =>
      rw [map_add]
      exact S.add_mem hp hq
  | mul_X p k hp =>
      rw [map_mul]
      exact S.mul_mem hp (Algebra.subset_adjoin (Set.mem_range_self k))

/-! ## §3 Stage 0 (T4/T5) — the block projection and its descent -/

/-- **THE BLOCK PROJECTION (T4)** — the ℂ-algebra retraction of the
coordinate ring onto block `j`: `X j ↦ 1`, `X j' ↦ t` (the partner), every
other variable ↦ 0 (`MvPolynomial.aeval`, MvPolynomial/Eval.lean:592).
Stage 1's retraction χ is `Localization.awayLift` of its quotient descent
(`blockEvalQuot`) below. -/
noncomputable def blockEval (M : ℕ) [NeZero M] (j : Fin (2 * M)) :
    lineRing M →ₐ[ℂ] MvPolynomial (Fin 1) ℂ :=
  MvPolynomial.aeval fun a =>
    if a = j then (1 : MvPolynomial (Fin 1) ℂ)
    else if a = linePartner M j then MvPolynomial.X (0 : Fin 1) else 0

/-- The computation rule of the block projection on variables
(`MvPolynomial.aeval_X`, MvPolynomial/Eval.lean:611). -/
theorem blockEval_X (M : ℕ) [NeZero M] (j k : Fin (2 * M)) :
    blockEval M j (MvPolynomial.X k) =
      (if k = j then (1 : MvPolynomial (Fin 1) ℂ)
        else if k = linePartner M j then MvPolynomial.X (0 : Fin 1) else 0) := by
  simp only [blockEval, MvPolynomial.aeval_X]

/-- **T5 (generators, pointwise)** — every cross-monomial generator
evaluates to zero on the block projection: `a`, `b` lie in different blocks
(T1 `linePartner_block`), so at most one of them lies in the block's pair
`{j, linePartner M j}`, and any variable outside the pair evaluates to 0. -/
theorem blockEval_crossMonomials (M : ℕ) [NeZero M] (j : Fin (2 * M)) :
    ∀ p ∈ crossMonomials M, blockEval M j p = 0 := by
  rintro _ ⟨a, b, hab, rfl⟩
  rw [map_mul, blockEval_X, blockEval_X, mul_eq_zero]
  by_cases hblk : a = j ∨ a = linePartner M j
  · refine Or.inr ?_
    have hablk : a.val / 2 = j.val / 2 := by
      rcases hblk with h | h
      · rw [h]
      · rw [h, linePartner_block]
    have hbj : b ≠ j := by
      intro hb
      subst hb
      exact hab hablk
    have hbp : b ≠ linePartner M j := by
      intro hb
      exact hab (by rw [hb, linePartner_block]; exact hablk)
    simp [hbj, hbp]
  · refine Or.inl ?_
    push_neg at hblk
    simp [hblk.1, hblk.2]

/-- **T5** — the block projection kills the cross ideal: the `≤ ker` form.
`Ideal.span_le` + the generator lemma above (the green
`truncIdeal_le_ker_evalWorldPoly` shape,
GSTTruncatedWorldCohomologyRing.lean:141-145). -/
theorem blockEval_mem_ker (M : ℕ) [NeZero M] (j : Fin (2 * M)) :
    crossIdeal M ≤ RingHom.ker (blockEval M j).toRingHom := by
  rw [show crossIdeal M = Ideal.span (crossMonomials M) from rfl, Ideal.span_le]
  intro p hp
  exact RingHom.mem_ker.mpr (blockEval_crossMonomials M j p hp)

/-- **T5 (pointwise, ideal-level)** — every cross-ideal element evaluates to
zero on the block projection (the `hI` shape of `liftₐ`). -/
theorem blockEval_mem_crossIdeal (M : ℕ) [NeZero M] (j : Fin (2 * M))
    {p : lineRing M} (hp : p ∈ crossIdeal M) : blockEval M j p = 0 :=
  RingHom.mem_ker.mp (blockEval_mem_ker M j hp)

/-- **THE BLOCK PROJECTION'S DESCENT (T5)** — the retraction of the
cross-monomial quotient onto `ℂ[t]`: the universal property of the quotient
algebra (`Ideal.Quotient.liftₐ`, Operations.lean:471 — pointwise `hI`, no
explicit base ring; the CI-green carrier spelling,
GSTFiniteLineWorldCarrier.lean:285-288). -/
noncomputable def blockEvalQuot (M : ℕ) [NeZero M] (j : Fin (2 * M)) :
    lineQuotient M →ₐ[ℂ] MvPolynomial (Fin 1) ℂ :=
  Ideal.Quotient.liftₐ (crossIdeal M) (blockEval M j)
    (fun p hp => blockEval_mem_crossIdeal M j hp)

/-- The computation rule of the descent on quotient classes — the carrier's
`lineRotateHom_mk` pattern (GSTFiniteLineWorldCarrier.lean:291-292, `rfl`). -/
theorem blockEvalQuot_mk (M : ℕ) [NeZero M] (j : Fin (2 * M)) (t : lineRing M) :
    blockEvalQuot M j (lineQuotientMap M t) = blockEval M j t :=
  rfl

/-! ## §4 Stage 0 (T6) — constants through degree zero -/

/-- **T6** — the constants through the degree-zero piece: the doubly-embedded
constant equals the quotient's constant.  This IS the pin's
`SetLike.GradeZero.coe_algebraMap`
(Mathlib/Algebra/DirectSum/Internal.lean:414-415, `@[simp, norm_cast]`, proved
`rfl`), at `S := ℂ`, `A := lineGrading M`, `R := lineQuotient M`.  The
finite-point carrier's `finitePoint_over_base` STAGE-3 idiom
(GSTFinitePointWorldCarrier.lean:676-688). -/
theorem hzero (M : ℕ) (c : ℂ) :
    (algebraMap ℂ (lineGrading M 0) c : lineQuotient M) = algebraMap ℂ (lineQuotient M) c :=
  SetLike.GradeZero.coe_algebraMap (lineGrading M) c

/-! ## §5 Stage 2 — the chart square (the `chartRingHom` contract)

THE W67-C PLUG.  `chartRingHom M j` is EXTERNAL (W67-C owns it, route map
Stage 1); the expected final shape is

    noncomputable def chartRingHom (M : ℕ) [NeZero M] (j : Fin (2 * M)) :
        ℂ →+* HomogeneousLocalization.Away (lineGrading M)
            (lineQuotientMap M (MvPolynomial.X j)) :=
      (HomogeneousLocalization.fromZeroRingHom (lineGrading M)
          (Submonoid.powers (lineQuotientMap M (MvPolynomial.X j)))).comp
        (algebraMap ℂ (lineGrading M 0))

— the chart's ℂ-STRUCTURE ring hom (`RingHom.smooth_algebraMap` unfolds
`RingHom.Smooth (chartRingHom M j)` against it).  NOTE: the type is
`ℂ →+* Away …`, NOT `MvPolynomial (Fin 1) ℂ →+* Away …` — with the latter the
square below is ill-typed (its RHS would be a morphism into `Spec ℂ[t]`,
while `awayι ≫ finiteLineStructureMap M` lands in `Spec ℂ`).  The
`MvPolynomial (Fin 1) ℂ`-side of the chart is W67-C's `chartMap`
(`MvPolynomial.aeval (chartRatio M j)`).

ASSEMBLY.  In the assembled F3 module, where `chartRingHom M j` is the real
definition above, the assembler may either
(a) keep `chart_awayι_comp` verbatim, passing `chartRingHom := chartRingHom M j`
    and `hdef := rfl`; or
(b) delete the two binders of `chart_awayι_comp` and its proof body, and use
    `chart_awayι_comp'` (the same square, stated directly on the canonical
    composite — `chartRingHom M j` is definitionally that composite).
-/

/-- **THE CHART SQUARE (STAGE 2, standalone form)** — the away-chart of the
structure map is the `Spec` of the canonical ℂ-structure composite of the
chart.  Route: unfold `finiteLineStructureMap` (the green retype-`rw`,
GSTFiniteLineClosedImmersion.lean:205-208), regroup
(`← CategoryTheory.Category.assoc`), the pin's per-chart square
`Proj.awayι_toSpecZero` (Basic.lean:206: `awayι ≫ toSpecZero = Spec.map
(ofHom (fromZeroRingHom 𝒜 (Submonoid.powers f)))`), fuse the two `Spec.map`s
(`← Spec.map_comp`, the contravariant `Spec` — Scheme.lean:488), and close by
the `ofHom`-fusion `CommRingCat.ofHom_comp` (Ring/Basic.lean:646-651, `rfl`). -/
theorem chart_awayι_comp' (M : ℕ) [NeZero M] (j : Fin (2 * M)) :
    Proj.awayι (lineGrading M) (lineQuotientMap M (MvPolynomial.X j))
        (lineCoverHomogeneousOneQ M j) zero_lt_one ≫
      finiteLineStructureMap M =
    Spec.map (CommRingCat.ofHom
      ((HomogeneousLocalization.fromZeroRingHom (lineGrading M)
          (Submonoid.powers (lineQuotientMap M (MvPolynomial.X j)))).comp
        (algebraMap ℂ (lineGrading M 0)))) := by
  rw [show finiteLineStructureMap M =
      (Proj.toSpecZero (lineGrading M) ≫
        Spec.map (CommRingCat.ofHom (algebraMap ℂ (lineGrading M 0)))) from rfl,
    ← CategoryTheory.Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  exact congrArg Spec.map
    (CommRingCat.ofHom_comp (algebraMap ℂ (lineGrading M 0))
      (HomogeneousLocalization.fromZeroRingHom (lineGrading M)
        (Submonoid.powers (lineQuotientMap M (MvPolynomial.X j))))).symm

/-- **THE CHART SQUARE (STAGE 2, plug-facing form)** — the same square
against the NAME `chartRingHom` (the W67-C plug, §5 contract): the binder
`chartRingHom` carries the expected type and `hdef` its defining equation.
In the assembled file both are discharged definitionally (`hdef := rfl`). -/
theorem chart_awayι_comp (M : ℕ) [NeZero M] (j : Fin (2 * M))
    (chartRingHom : ℂ →+* HomogeneousLocalization.Away (lineGrading M)
      (lineQuotientMap M (MvPolynomial.X j)))
    (hdef : chartRingHom = (HomogeneousLocalization.fromZeroRingHom (lineGrading M)
        (Submonoid.powers (lineQuotientMap M (MvPolynomial.X j)))).comp
      (algebraMap ℂ (lineGrading M 0))) :
    Proj.awayι (lineGrading M) (lineQuotientMap M (MvPolynomial.X j))
        (lineCoverHomogeneousOneQ M j) zero_lt_one ≫
      finiteLineStructureMap M =
    Spec.map (CommRingCat.ofHom chartRingHom) := by
  rw [hdef]
  exact chart_awayι_comp' M j

/-! ## §6 The chart algebra structure and the chart ring hom -/

/-- The ℂ-structure ring hom of the chart: the composite of the constants
into the degree-zero piece and the pin's `fromZeroRingHom` (the fraction
`f/1`).  This is the ring map whose `Spec` is the per-chart structure map
(the §5 square) and whose smoothness is the F3 battle's target. -/
noncomputable def chartRingHom (M : ℕ) [NeZero M] (j : Fin (2 * M)) :
    ℂ →+* HomogeneousLocalization.Away (lineGrading M)
      (lineQuotientMap M (MvPolynomial.X j)) :=
  (HomogeneousLocalization.fromZeroRingHom (lineGrading M)
    (Submonoid.powers (lineQuotientMap M (MvPolynomial.X j)))).comp
    (algebraMap ℂ (lineGrading M 0))

/-- The induced ℂ-algebra structure on the chart ring (the pin's own
`RingHom.toAlgebra`, the same structure `RingHom.Smooth` unfolds against).
Registered through `@[instance] def` — the `j` binder lives inside the
`lineQuotientMap M (MvPolynomial.X j)` spine of the type, which instance
synthesis unifies first-order but the declaration lint cannot see. -/
@[instance]
noncomputable def chartAlgebra (M : ℕ) [NeZero M] (j : Fin (2 * M)) :
    Algebra ℂ (HomogeneousLocalization.Away (lineGrading M)
      (lineQuotientMap M (MvPolynomial.X j))) :=
  (chartRingHom M j).toAlgebra

/-! ## §6.5 The smul-form memberships (the Away.mk degree discipline) -/

/-- Every variable's quotient image is homogeneous of degree one (the
cover twin at every index — the per-variable form of T2'). -/
theorem lineX_mem_one (M : ℕ) [NeZero M] (a : Fin (2 * M)) :
    lineQuotientMap M (MvPolynomial.X a) ∈ lineGrading M 1 :=
  lineCoverHomogeneousOneQ M a

/-- The homogeneous membership at the smul-form `n • 1` (the degree shape
`Away.mk` demands; `n • 1 = n` by `one_nsmul`). -/
theorem lineQuotientMap_mem_lineGrading_smul (M : ℕ) (n : ℕ) (t : lineRing M)
    (ht : t ∈ MvPolynomial.homogeneousSubmodule (Fin (2 * M)) ℂ n) :
    lineQuotientMap M t ∈ lineGrading M (n • 1) := by
  have h := lineQuotientMap_mem_lineGrading M n t ht
  rwa [show n • 1 = n from one_nsmul n] at h

/-- **THE PARTNER'S SMUL-MEMBERSHIP** — the partner variable's image is
homogeneous of degree `1 • 1` (the `hx` argument of `chartRatio`'s
`Away.mk`). -/
theorem linePartner_mem_smul_one (M : ℕ) [NeZero M] (j : Fin (2 * M)) :
    lineQuotientMap M (MvPolynomial.X (linePartner M j)) ∈ lineGrading M (1 • 1) :=
  lineQuotientMap_mem_lineGrading_smul M 1 (MvPolynomial.X (linePartner M j))
    ((MvPolynomial.mem_homogeneousSubmodule 1
        (MvPolynomial.X (linePartner M j))).mpr
      (MvPolynomial.isHomogeneous_X ℂ (linePartner M j)))

/-! ## §7 THE SMOOTHNESS BATTLE — the chart ring is ℂ[T] -/

/-- **THE PARTNER RATIO** — the chart's transcendental generator: the
fraction `q (X j') / q (X j)` where `j'` is `j`'s block partner. -/
noncomputable def chartRatio (M : ℕ) [NeZero M] (j : Fin (2 * M)) :
    HomogeneousLocalization.Away (lineGrading M)
      (lineQuotientMap M (MvPolynomial.X j)) :=
  HomogeneousLocalization.Away.mk (lineGrading M)
    (lineCoverHomogeneousOneQ M j) 1
    (lineQuotientMap M (MvPolynomial.X (linePartner M j)))
    (linePartner_mem_smul_one M j)

/-- The `val` of the chart ratio is the plain localization fraction
`f' / f` (the `Away.val_mk` rfl). -/
theorem chartRatio_val (M : ℕ) [NeZero M] (j : Fin (2 * M)) :
    (chartRatio M j).val =
      IsLocalization.mk'
        (M := Submonoid.powers
          (lineQuotientMap M (MvPolynomial.X j)))
        (S := Localization.Away (lineQuotientMap M (MvPolynomial.X j)))
        (lineQuotientMap M (MvPolynomial.X (linePartner M j)))
        ⟨lineQuotientMap M (MvPolynomial.X j),
          (Submonoid.mem_powers_iff _ _).mpr ⟨1, pow_one _⟩⟩ := by
  rw [chartRatio, HomogeneousLocalization.Away.val_mk]
  rfl

/-- **THE CHART MAP** — the polynomial evaluation at the partner ratio:
`T ↦ ρ` (the constant ratio assignment on the one-variable index). -/
noncomputable def chartMap (M : ℕ) [NeZero M] (j : Fin (2 * M)) :
    MvPolynomial (Fin 1) ℂ →ₐ[ℂ]
      HomogeneousLocalization.Away (lineGrading M)
        (lineQuotientMap M (MvPolynomial.X j)) :=
  MvPolynomial.aeval (fun _ : Fin 1 => chartRatio M j)

/-! ### §7.A The away-fraction arithmetic (the val calculus)

Every fraction identity is proved through the localization embedding
`val` (`val_injective`), where it is the standard `Localization.mk`
arithmetic. -/

section AwayArithmetic

variable (M : ℕ) [NeZero M] (j : Fin (2 * M))

/-- **THE SAME-DENOMINATOR PRODUCT** — the product of the fractions
`x / f ^ n` and `y / f ^ e` is the fraction `x * y / f ^ (n + e)`. -/
private theorem away_mk_mul (n e : ℕ) (x y : lineQuotient M)
    (hx : x ∈ lineGrading M (n • 1)) (hy : y ∈ lineGrading M (e • 1)) :
    HomogeneousLocalization.Away.mk (lineGrading M)
        (lineCoverHomogeneousOneQ M j) n x hx *
      HomogeneousLocalization.Away.mk (lineGrading M)
        (lineCoverHomogeneousOneQ M j) e y hy =
    HomogeneousLocalization.Away.mk (lineGrading M)
      (lineCoverHomogeneousOneQ M j) (n + e) (x * y)
      (by
        have h := SetLike.mul_mem_graded hx hy
        rwa [show n • 1 + e • 1 = (n + e) • 1 from by rw [add_nsmul]] at h) := by
  apply HomogeneousLocalization.val_injective
    (𝒜 := lineGrading M)
    (x := Submonoid.powers (lineQuotientMap M (MvPolynomial.X j)))
  rw [HomogeneousLocalization.val_mul,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.Away.val_mk, Localization.mk_mul]
  congr 1
  · rfl
  · simp only [Submonoid.coe_mul, pow_add]

/-- **THE SAME-DENOMINATOR SUM** — the sum of two fractions with the same
denominator `f ^ n` is the fraction of the sum. -/
private theorem away_mk_add (n : ℕ) (x y : lineQuotient M)
    (hx : x ∈ lineGrading M (n • 1)) (hy : y ∈ lineGrading M (n • 1)) :
    HomogeneousLocalization.Away.mk (lineGrading M)
        (lineCoverHomogeneousOneQ M j) n x hx +
      HomogeneousLocalization.Away.mk (lineGrading M)
        (lineCoverHomogeneousOneQ M j) n y hy =
    HomogeneousLocalization.Away.mk (lineGrading M)
      (lineCoverHomogeneousOneQ M j) n (x + y)
      (by
        exact (lineGrading M (n • 1)).add_mem hx hy) := by
  apply HomogeneousLocalization.val_injective
    (𝒜 := lineGrading M)
    (x := Submonoid.powers (lineQuotientMap M (MvPolynomial.X j)))
  rw [HomogeneousLocalization.val_add,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.Away.val_mk, Localization.add_mk,
    Localization.mk_eq_mk_iff]
  refine ⟨1, Submonoid.one_mem _, ?_⟩
  simp only [Submonoid.coe_mul, Submonoid.coe_one, mul_one]
  noncomm_ring

end AwayArithmetic

/-! ### §7.B The away-fraction cast and sum discipline -/

/-- **THE DEGREE-CAST** — the fraction is invariant under the transport of
the membership proof along an equality of degrees. -/
private theorem away_mk_cast (M : ℕ) [NeZero M] (j : Fin (2 * M))
    {m n : ℕ} (hmn : m = n) (e : ↥(lineGrading M (m • 1))) :
    HomogeneousLocalization.Away.mk (lineGrading M)
        (lineCoverHomogeneousOneQ M j) m (e : lineQuotient M) e.2 =
    HomogeneousLocalization.Away.mk (lineGrading M)
      (lineCoverHomogeneousOneQ M j) n (e : lineQuotient M)
      ((hmn ▸ e : ↥(lineGrading M (n • 1))).2) := by
  subst hmn
  rfl

/-- **THE SAME-DENOMINATOR FINITE SUM** — a finite sum of fractions with
the common denominator `f ^ n` is the fraction of the sum. -/
private theorem sum_mk_eq (M : ℕ) [NeZero M] (j : Fin (2 * M)) (n : ℕ)
    {ι : Type*} (T : Finset ι) (x : ι → ↥(lineGrading M (n • 1))) :
    ∑ d ∈ T, HomogeneousLocalization.Away.mk (lineGrading M)
        (lineCoverHomogeneousOneQ M j) n (x d : lineQuotient M) (x d).2 =
    HomogeneousLocalization.Away.mk (lineGrading M)
      (lineCoverHomogeneousOneQ M j) n (∑ d ∈ T, (x d : lineQuotient M))
      (Submodule.sum_mem (lineGrading M (n • 1))
        (fun d _ => (x d).2)) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      apply HomogeneousLocalization.val_injective
        (𝒜 := lineGrading M)
        (x := Submonoid.powers (lineQuotientMap M (MvPolynomial.X j)))
      rw [HomogeneousLocalization.Away.val_mk,
        HomogeneousLocalization.val_zero, Localization.mk_zero]
  | insert d T hdT ih =>
      rw [Finset.sum_insert hdT, Finset.sum_insert hdT,
        away_mk_add M j n _ _ (x d).2
          (Submodule.sum_mem (lineGrading M (n • 1)) (fun d' _ => (x d').2)),
        ih]
      rfl

/-! ### §7.C The per-monomial evaluation (the Finsupp induction) -/

/-- The per-variable ratio assignment `a ↦ q (X a) / f` (the mk-one form). -/
private noncomputable def chartAssign (M : ℕ) [NeZero M] (j a : Fin (2 * M)) :
    HomogeneousLocalization.Away (lineGrading M)
      (lineQuotientMap M (MvPolynomial.X j)) :=
  HomogeneousLocalization.Away.mk (lineGrading M)
    (lineCoverHomogeneousOneQ M j) 1
    (lineQuotientMap M (MvPolynomial.X a))
    (lineQuotientMap_mem_lineGrading_smul M 1 (MvPolynomial.X a)
      ((MvPolynomial.mem_homogeneousSubmodule 1 (MvPolynomial.X a)).mpr
        (MvPolynomial.isHomogeneous_X ℂ a)))

/-- **THE CONSTANT CASE** — the evaluation of a constant is the chart ring
hom, which IS the fraction `constant / 1`. -/
private theorem const_eval (M : ℕ) [NeZero M] (j : Fin (2 * M)) (c : ℂ) :
    MvPolynomial.aeval (chartAssign M j) (MvPolynomial.C c) =
    HomogeneousLocalization.Away.mk (lineGrading M)
      (lineCoverHomogeneousOneQ M j) 0 (lineQuotientMap M (MvPolynomial.C c))
      (lineQuotientMap_mem_lineGrading_smul M 0 (MvPolynomial.C c)
        ((MvPolynomial.mem_homogeneousSubmodule 0 (MvPolynomial.C c)).mpr
          (MvPolynomial.isHomogeneous_C (σ := Fin (2 * M)) (R := ℂ) c))) := by
  rw [MvPolynomial.aeval_C]
  show chartRingHom M j c = _
  rw [chartRingHom]
  apply HomogeneousLocalization.val_injective
    (𝒜 := lineGrading M)
    (x := Submonoid.powers (lineQuotientMap M (MvPolynomial.X j)))
  show HomogeneousLocalization.val
      (HomogeneousLocalization.fromZeroRingHom (lineGrading M)
        (Submonoid.powers (lineQuotientMap M (MvPolynomial.X j)))
        (algebraMap ℂ (lineGrading M 0) c)) =
    HomogeneousLocalization.val _
  have hconst : (algebraMap ℂ (lineGrading M 0) c : lineQuotient M) =
      lineQuotientMap M (MvPolynomial.C c) := by
    rw [show MvPolynomial.C c = algebraMap ℂ (lineRing M) c from rfl,
      (lineQuotientMap M).commutes c]
  conv_lhs => rw [show HomogeneousLocalization.fromZeroRingHom (lineGrading M)
      (Submonoid.powers (lineQuotientMap M (MvPolynomial.X j)))
      (algebraMap ℂ (lineGrading M 0) c) =
    HomogeneousLocalization.Away.mk (lineGrading M)
      (lineCoverHomogeneousOneQ M j) 0
      (algebraMap ℂ (lineGrading M 0) c : lineQuotient M)
      (SetLike.GradeZero.algebraMap_mem (lineGrading M) c) from rfl]
  rw [HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.Away.val_mk, hconst]
  simp

/-- **THE POWER OF A FRACTION** — the `e`-th power of the fraction
`x / f` is the fraction `x ^ e / f ^ e`. -/
private theorem mk_pow (M : ℕ) [NeZero M] (j : Fin (2 * M))
    (x : lineQuotient M) (hx : x ∈ lineGrading M (1 • 1)) (e : ℕ) :
    (HomogeneousLocalization.Away.mk (lineGrading M)
        (lineCoverHomogeneousOneQ M j) 1 x hx) ^ e =
    HomogeneousLocalization.Away.mk (lineGrading M)
      (lineCoverHomogeneousOneQ M j) e (x ^ e)
      (SetLike.pow_mem_graded e (lineCoverHomogeneousOneQ M j)) := by
  induction e with
  | zero =>
      apply HomogeneousLocalization.val_injective
        (𝒜 := lineGrading M)
        (x := Submonoid.powers (lineQuotientMap M (MvPolynomial.X j)))
      rw [HomogeneousLocalization.Away.val_mk, pow_zero, pow_zero, map_one,
        HomogeneousLocalization.val_one]
      simp
  | succ e ih =>
      rw [pow_succ, ih,
        away_mk_mul M j e 1 (x ^ e) x
          (SetLike.pow_mem_graded e (lineCoverHomogeneousOneQ M j)) hx]
      rfl

/-- **THE PER-MONOMIAL EVALUATION** — evaluating a monomial at the ratio
assignment is the single fraction `q (monomial d c) / f ^ (d.sum id)`,
by the Finsupp induction: the base is the constant case, the step is
the same-denominator product. -/
private theorem monomial_eval (M : ℕ) [NeZero M] (j : Fin (2 * M))
    (d : Fin (2 * M) →₀ ℕ) (c : ℂ) :
    MvPolynomial.aeval (chartAssign M j) (MvPolynomial.monomial d c) =
    HomogeneousLocalization.Away.mk (lineGrading M)
      (lineCoverHomogeneousOneQ M j) (d.sum fun _ e => e)
      (lineQuotientMap M (MvPolynomial.monomial d c))
      (lineQuotientMap_mem_lineGrading_smul M (d.sum fun _ e => e)
        (MvPolynomial.monomial d c)
        ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr
          (MvPolynomial.isHomogeneous_monomial c
            (by
              rw [Finsupp.degree_eq_weight_one]
              exact Finsupp.ext fun _ => one_mul _)))) := by
  induction d using Finsupp.induction with
  | zero =>
      show MvPolynomial.aeval (chartAssign M j)
          (MvPolynomial.monomial (0 : Fin (2 * M) →₀ ℕ) c) = _
      rw [show MvPolynomial.monomial (0 : Fin (2 * M) →₀ ℕ) c =
          MvPolynomial.C c from rfl]
      rw [const_eval M j c, Finsupp.sum_zero]
      rfl
  | add d' a e _ ih =>
      have hsplit : MvPolynomial.monomial (d' + Finsupp.single a e) c =
          MvPolynomial.monomial d' c * MvPolynomial.X a ^ e := by
        rw [MvPolynomial.monomial_add, ← MvPolynomial.X_pow_eq_monomial]
      have hdeg : (d' + Finsupp.single a e).sum (fun _ e => e) =
          d'.sum (fun _ e => e) + e := by
        rw [Finsupp.sum_add_index (by simp) (by simp) (by simp)]
        simp
      have hmem : MvPolynomial.monomial d' c ∈
          MvPolynomial.homogeneousSubmodule (Fin (2 * M)) ℂ
            (d'.sum fun _ e => e) :=
        (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
          (MvPolynomial.isHomogeneous_monomial c
            (by
              rw [Finsupp.degree_eq_weight_one]
              exact Finsupp.ext fun _ => one_mul _))
      rw [hsplit, map_mul, map_pow, MvPolynomial.aeval_X, ih,
        mk_pow M j (lineQuotientMap M (MvPolynomial.X a))
          (lineQuotientMap_mem_lineGrading_smul M 1 (MvPolynomial.X a)
            ((MvPolynomial.mem_homogeneousSubmodule 1 (MvPolynomial.X a)).mpr
              (MvPolynomial.isHomogeneous_X ℂ a))) e,
        away_mk_mul M j (d'.sum fun _ e => e) e
          (lineQuotientMap M (MvPolynomial.monomial d' c))
          (lineQuotientMap M (MvPolynomial.X a) ^ e)
          (lineQuotientMap_mem_lineGrading_smul M _ _ hmem)
          (SetLike.pow_mem_graded e (lineCoverHomogeneousOneQ M j)),
        hdeg, ← map_mul, ← map_pow, ← hsplit]
      rfl

/-! ### §7.D The homogeneous evaluation (the battle's core) -/

/-- **THE HOMOGENEOUS EVALUATION LEMMA (the battle's core)** — for a
homogeneous polynomial `s` of degree `n`, the polynomial evaluation of
`s` at the ratio-assignment `a ↦ q (X a) / f` equals the single fraction
`q (s) / f ^ n`.  The proof: the monomial-sum decomposition, the
per-monomial evaluation with the support-degree discipline, and the
same-denominator sum. -/
private theorem homogeneous_eval (M : ℕ) [NeZero M] (j : Fin (2 * M))
    (n : ℕ) (s : MvPolynomial (Fin (2 * M)) ℂ)
    (hs : s ∈ MvPolynomial.homogeneousSubmodule (Fin (2 * M)) ℂ n) :
    (MvPolynomial.aeval (chartAssign M j) :
        MvPolynomial (Fin (2 * M)) ℂ →ₐ[ℂ]
          HomogeneousLocalization.Away (lineGrading M)
            (lineQuotientMap M (MvPolynomial.X j))) s =
      HomogeneousLocalization.Away.mk (lineGrading M)
        (lineCoverHomogeneousOneQ M j) n (lineQuotientMap M s)
        (lineQuotientMap_mem_lineGrading_smul M n s hs) := by
  have hdeg : ∀ d ∈ s.support, d.sum (fun _ e => e) = n := by
    intro d hd
    have hs' := hs
    rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported] at hs'
    have hsub : s.support ⊆ {d : Fin (2 * M) →₀ ℕ | d.degree = n} := by
      simpa [Finsupp.supported] using hs'
    have hdf : d.degree = n := hsub hd
    rw [Finsupp.degree_eq_weight_one, weight] at hdf
    simpa using hdf.symm
  -- the graded subtype family: the monomial images at degree n
  classical
  have hxmem : ∀ d : Fin (2 * M) →₀ ℕ, lineQuotientMap M
      (MvPolynomial.monomial d (MvPolynomial.coeff d s)) ∈
      lineGrading M (n • 1) := by
    intro d
    by_cases hd : d ∈ s.support
    · exact lineQuotientMap_mem_lineGrading_smul M n _
        ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr
          (MvPolynomial.isHomogeneous_monomial _ (by
            rw [Finsupp.degree_eq_weight_one, weight]
            simpa using hdeg d hd)))
    · have hc : MvPolynomial.coeff d s = 0 :=
        by
        intro hcon
        exact hd (MvPolynomial.mem_support_iff.mpr hcon)
      rw [hc]
      simpa using (lineGrading M (n • 1)).zero_mem
  set x : (Fin (2 * M) →₀ ℕ) → ↥(lineGrading M (n • 1)) := fun d =>
    ⟨lineQuotientMap M (MvPolynomial.monomial d (MvPolynomial.coeff d s)),
      hxmem d⟩ with hx
  rw [MvPolynomial.as_sum s, map_sum,
    Finset.sum_congr rfl (fun d hd =>
      by
        rw [monomial_eval M j d (MvPolynomial.coeff d s),
          away_mk_cast M j (hdeg d hd)
            ⟨lineQuotientMap M
              (MvPolynomial.monomial d (MvPolynomial.coeff d s)),
              lineQuotientMap_mem_lineGrading_smul M (d.sum fun _ e => e)
                (MvPolynomial.monomial d (MvPolynomial.coeff d s))
                ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr
                  (MvPolynomial.isHomogeneous_monomial _ (by
                    rw [Finsupp.degree_eq_weight_one]
                    exact Finsupp.ext fun _ => one_mul _)))⟩)]),
    sum_mk_eq M j n s.support x]
  congr 2
  rw [Finset.sum_congr rfl (fun d _ => rfl), map_sum,
    ← MvPolynomial.as_sum s]

/-! ### §7.E The per-variable identities (the block trichotomy) -/

/-- **THE SELF-FRACTION** — `f / f = 1` in the chart ring. -/
private theorem mk_self_frac (M : ℕ) [NeZero M] (j : Fin (2 * M)) :
    HomogeneousLocalization.Away.mk (lineGrading M)
      (lineCoverHomogeneousOneQ M j) 1
      (lineQuotientMap M (MvPolynomial.X j))
      (lineCoverHomogeneousOneQ M j) = 1 := by
  apply HomogeneousLocalization.val_injective
    (𝒜 := lineGrading M)
    (x := Submonoid.powers (lineQuotientMap M (MvPolynomial.X j)))
  rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_one]
  exact Localization.mk_self _

/-- The off-block variables annihilate `f`: `q (X a) * f = 0` whenever `a`
is outside `j`'s coordinate block. -/
private theorem offblock_mul_eq_zero (M : ℕ) [NeZero M] (j a : Fin (2 * M))
    (haj : a ≠ j) (haj' : a ≠ linePartner M j) :
    lineQuotientMap M (MvPolynomial.X a) *
      lineQuotientMap M (MvPolynomial.X j) = 0 := by
  have hblk : a.val / 2 ≠ j.val / 2 := by
    intro hcon
    by_cases hj : j.val % 2 = 0
    · have hp : (linePartner M j).val = j.val + 1 := linePartner_val_even M j hj
      have ha' : a.val = j.val ∨ a.val = j.val + 1 := by omega
      rcases ha' with h | h
      · exact haj (Fin.ext h)
      · exact haj' (Fin.ext (by rw [hp]; omega))
    · have hp : (linePartner M j).val = j.val - 1 := linePartner_val_odd M j hj
      have ha' : a.val = j.val ∨ a.val = j.val - 1 := by omega
      rcases ha' with h | h
      · exact haj (Fin.ext h)
      · exact haj' (Fin.ext (by rw [hp]; omega))
  rw [← map_mul]
  apply lineQuotientMap_eq_zero_iff.mpr
  exact Ideal.subset_span ⟨a, j, hblk, rfl⟩

/-- **THE OFF-BLOCK ZERO** — the fraction `q (X a) / f` vanishes for
off-block `a`. -/
private theorem offblock_assign_eq_zero (M : ℕ) [NeZero M] (j a : Fin (2 * M))
    (haj : a ≠ j) (haj' : a ≠ linePartner M j) :
    HomogeneousLocalization.Away.mk (lineGrading M)
      (lineCoverHomogeneousOneQ M j) 1
      (lineQuotientMap M (MvPolynomial.X a))
      (lineQuotientMap_mem_lineGrading_smul M 1 (MvPolynomial.X a)
        ((MvPolynomial.mem_homogeneousSubmodule 1 (MvPolynomial.X a)).mpr
          (MvPolynomial.isHomogeneous_X ℂ a))) = 0 := by
  apply HomogeneousLocalization.val_injective
    (𝒜 := lineGrading M)
    (x := Submonoid.powers (lineQuotientMap M (MvPolynomial.X j)))
  rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_zero,
    Localization.mk_eq_zero_iff]
  refine ⟨1, Submonoid.one_mem _, ?_⟩
  rw [one_mul]
  rw [offblock_mul_eq_zero M j a haj haj']

/-- **THE PER-VARIABLE IDENTITY** — the chart map reads the block
projection of every variable exactly as the ratio assignment does. -/
private theorem block_identity_var (M : ℕ) [NeZero M] (j a : Fin (2 * M)) :
    chartMap M j (blockEval M j (MvPolynomial.X a)) =
    HomogeneousLocalization.Away.mk (lineGrading M)
      (lineCoverHomogeneousOneQ M j) 1
      (lineQuotientMap M (MvPolynomial.X a))
      (lineQuotientMap_mem_lineGrading_smul M 1 (MvPolynomial.X a)
        ((MvPolynomial.mem_homogeneousSubmodule 1 (MvPolynomial.X a)).mpr
          (MvPolynomial.isHomogeneous_X ℂ a))) := by
  by_cases haj : a = j
  · subst haj
    rw [blockEval_X, if_pos rfl, map_one, mk_self_frac M j]
  · by_cases haj' : a = linePartner M j
    · subst haj'
      rw [blockEval_X, if_neg haj, if_pos rfl]
      show (chartMap M j) (MvPolynomial.X (0 : Fin 1)) = _
      rw [chartMap, MvPolynomial.aeval_X]
      rfl
    · rw [blockEval_X, if_neg haj, if_neg haj',
        offblock_assign_eq_zero M j a haj haj', map_zero]

/-- **THE BLOCK IDENTITY** — the chart map of the block projection is the
ratio-assignment evaluation (the polynomial induction over the per-variable
identity). -/
private theorem block_identity (M : ℕ) [NeZero M] (j : Fin (2 * M))
    (t : lineRing M) :
    chartMap M j (blockEval M j t) =
    MvPolynomial.aeval (chartAssign M j) t := by
  induction t using MvPolynomial.induction_on with
  | C c =>
      simp only [blockEval, chartMap, MvPolynomial.aeval_C]
  | add p q hp hq =>
      simp only [map_add]
      rw [hp, hq]
  | mul_X p a hp =>
      simp only [map_mul]
      rw [block_identity_var M j a, hp, MvPolynomial.aeval_X]
      rfl

/-! ### §7.F THE CHART MAP IS SURJECTIVE -/

/-- **THE CHART MAP IS SURJECTIVE** — every chart element is a polynomial
in the partner ratio: `z = mk (q s) / f ^ n` (mk-surjectivity + the
piece-level lift), and the homogeneous evaluation lemma identifies the
fraction with the ratio-assignment evaluation of `s`, which by the block
identity is the chart map of the block projection of `s`. -/
theorem chartMap_surjective (M : ℕ) [NeZero M] (j : Fin (2 * M)) :
    Function.Surjective (chartMap M j) := by
  intro z
  obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (lineGrading M) (lineCoverHomogeneousOneQ M j) z
  have han : a ∈ lineGrading M n := by
    rwa [show n • 1 = n from one_nsmul n] at ha
  obtain ⟨t, ht, rfl⟩ := (mem_lineGrading M n a).mp han
  refine ⟨blockEvalQuot M j (lineQuotientMap M t), ?_⟩
  show chartMap M j (blockEval M j t) = _
  rw [block_identity M j t, homogeneous_eval M j n t ht]

/-- **THE RESCALE** — a fraction `y / f ^ v` equals the fraction
`f ^ (N - v) * y / f ^ N` whenever `v ≤ N`. -/
private theorem away_mk_rescale (M : ℕ) [NeZero M] (j : Fin (2 * M))
    (v N : ℕ) (hvn : v ≤ N) (y : lineQuotient M)
    (hy : y ∈ lineGrading M (v • 1)) :
    HomogeneousLocalization.Away.mk (lineGrading M)
        (lineCoverHomogeneousOneQ M j) v y hy =
    HomogeneousLocalization.Away.mk (lineGrading M)
      (lineCoverHomogeneousOneQ M j) N
      (lineQuotientMap M (MvPolynomial.X j) ^ (N - v) * y)
      (by
        have h1 := SetLike.pow_mem_graded (N - v) (lineCoverHomogeneousOneQ M j)
        have h2 := SetLike.mul_mem_graded h1 hy
        rwa [show (N - v) • 1 + v • 1 = N • 1 from by
          rw [← add_nsmul, Nat.sub_add_cancel hvn]] at h2) := by
  apply HomogeneousLocalization.val_injective
    (𝒜 := lineGrading M)
    (x := Submonoid.powers (lineQuotientMap M (MvPolynomial.X j)))
  rw [HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk_iff]
  refine ⟨1, Submonoid.one_mem _, ?_⟩
  simp only [Submonoid.coe_mul, Submonoid.coe_one, mul_one]
  noncomm_ring

/-! ### §7.G The monomial chart evaluation and the retraction -/

/-- The monomial chart evaluation: the chart map of a one-variable
monomial is the fraction of the partner-power lift. -/
private theorem chartMap_monomial (M : ℕ) [NeZero M] (j : Fin (2 * M))
    (m : Fin 1 →₀ ℕ) (c : ℂ) :
    chartMap M j (MvPolynomial.monomial m c) =
    HomogeneousLocalization.Away.mk (lineGrading M)
      (lineCoverHomogeneousOneQ M j) (m.sum fun _ e => e)
      (lineQuotientMap M (MvPolynomial.C c *
        MvPolynomial.X (linePartner M j) ^ (m.sum fun _ e => e)))
      (lineQuotientMap_mem_lineGrading_smul M (m.sum fun _ e => e)
        (MvPolynomial.C c * MvPolynomial.X (linePartner M j) ^ (m.sum fun _ e => e))
        (by
          have hc : MvPolynomial.C c ∈
              MvPolynomial.homogeneousSubmodule (Fin (2 * M)) ℂ 0 :=
            (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
              (MvPolynomial.isHomogeneous_C (σ := Fin (2 * M)) (R := ℂ) c)
          have hp : MvPolynomial.X (linePartner M j) ^ (m.sum fun _ e => e) ∈
              MvPolynomial.homogeneousSubmodule (Fin (2 * M)) ℂ
                (m.sum fun _ e => e) := by
            refine (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
              (MvPolynomial.isHomogeneous_monomial 1 ?_)
            rw [show MvPolynomial.X (linePartner M j) ^ (m.sum fun _ e => e) =
                MvPolynomial.monomial (Finsupp.single (linePartner M j)
                  (m.sum fun _ e => e)) 1 from
              (MvPolynomial.X_pow_eq_monomial _ _).symm]
            rw [Finsupp.degree_eq_weight_one]
            exact Finsupp.ext fun _ => one_mul _
          have hmul := Submodule.mul_mem_mul hc hp
          have hle := MvPolynomial.homogeneousSubmodule_mul (Fin (2 * M)) ℂ 0
            (m.sum fun _ e => e) hmul
          rwa [zero_add] at hle)) := by
  induction m using Finsupp.induction with
  | zero =>
      rw [show MvPolynomial.monomial (0 : Fin 1 →₀ ℕ) c =
          MvPolynomial.C c from rfl, Finsupp.sum_zero, pow_zero, mul_one,
        MvPolynomial.aeval_C]
      have hce := const_eval M j c
      rw [MvPolynomial.aeval_C] at hce
      exact hce
  | add m' i e _ ih =>
      have hsplit : MvPolynomial.monomial (m' + Finsupp.single i e) c =
          MvPolynomial.monomial m' c * MvPolynomial.X i ^ e := by
        rw [MvPolynomial.monomial_add, ← MvPolynomial.X_pow_eq_monomial]
      have hdeg : (m' + Finsupp.single i e).sum (fun _ e => e) =
          m'.sum (fun _ e => e) + e := by
        rw [Finsupp.sum_add_index (by simp) (by simp) (by simp)]
        simp
      have hmem : MvPolynomial.C c *
          MvPolynomial.X (linePartner M j) ^ m'.sum (fun _ e => e) ∈
          MvPolynomial.homogeneousSubmodule (Fin (2 * M)) ℂ
            (m'.sum fun _ e => e) := by
        have hc : MvPolynomial.C c ∈
            MvPolynomial.homogeneousSubmodule (Fin (2 * M)) ℂ 0 :=
          (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
            (MvPolynomial.isHomogeneous_C (σ := Fin (2 * M)) (R := ℂ) c)
        have hp : MvPolynomial.X (linePartner M j) ^ m'.sum (fun _ e => e) ∈
            MvPolynomial.homogeneousSubmodule (Fin (2 * M)) ℂ
              (m'.sum fun _ e => e) := by
          refine (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
            (MvPolynomial.isHomogeneous_monomial 1 ?_)
          rw [show MvPolynomial.X (linePartner M j) ^ m'.sum (fun _ e => e) =
              MvPolynomial.monomial (Finsupp.single (linePartner M j)
                (m'.sum fun _ e => e)) 1 from
            (MvPolynomial.X_pow_eq_monomial _ _).symm]
          rw [Finsupp.degree_eq_weight_one]
          exact Finsupp.ext fun _ => one_mul _
        have hmul := Submodule.mul_mem_mul hc hp
        have hle := MvPolynomial.homogeneousSubmodule_mul (Fin (2 * M)) ℂ 0
          (m'.sum fun _ e => e) hmul
        rwa [zero_add] at hle
      have hnum : lineQuotientMap M
          (MvPolynomial.C c * MvPolynomial.X (linePartner M j) ^
            (m'.sum (fun _ e => e) + e)) =
          lineQuotientMap M
            (MvPolynomial.C c *
              MvPolynomial.X (linePartner M j) ^ m'.sum (fun _ e => e)) *
            lineQuotientMap M (MvPolynomial.X (linePartner M j)) ^ e := by
        rw [pow_add, map_mul, mul_assoc]
      rw [hsplit, map_mul, map_pow, MvPolynomial.aeval_X, ih,
        show (chartRatio M j) ^ e =
          HomogeneousLocalization.Away.mk (lineGrading M)
            (lineCoverHomogeneousOneQ M j) e
            (lineQuotientMap M (MvPolynomial.X (linePartner M j)) ^ e)
            (SetLike.pow_mem_graded e (lineCoverHomogeneousOneQ M j)) from
          mk_pow M j (lineQuotientMap M (MvPolynomial.X (linePartner M j)))
            (linePartner_mem_smul_one M j) e,
        away_mk_mul M j (m'.sum fun _ e => e) e
          (lineQuotientMap M
            (MvPolynomial.C c *
              MvPolynomial.X (linePartner M j) ^ m'.sum (fun _ e => e)))
          (lineQuotientMap M (MvPolynomial.X (linePartner M j)) ^ e)
          (lineQuotientMap_mem_lineGrading_smul M _ _ hmem)
          (SetLike.pow_mem_graded e (lineCoverHomogeneousOneQ M j)),
        hdeg, hnum]
      rfl


/-- The same-block lift: the monomial `c * T ^ v` lifts to the degree-`N`
same-block polynomial `c * X j ^ (N - v) * X j' ^ v`. -/
private def blockLift (M : ℕ) [NeZero M] (j : Fin (2 * M))
    (R : MvPolynomial (Fin 1) ℂ) (N : ℕ) : lineRing M :=
  ∑ m ∈ R.support, MvPolynomial.coeff m R *
    (MvPolynomial.X j ^ (N - m.sum fun _ e => e) *
     MvPolynomial.X (linePartner M j) ^ (m.sum fun _ e => e))

/-- **THE RETRACTION** — the block projection of the lift reads the
polynomial back. -/
private theorem blockEval_blockLift (M : ℕ) [NeZero M] (j : Fin (2 * M))
    (R : MvPolynomial (Fin 1) ℂ) (N : ℕ) :
    blockEval M j (blockLift M j R N) = R := by
  classical
  rw [blockLift, map_sum]
  rw [Finset.sum_congr rfl (fun m _ =>
    by
      have hm0 : m = Finsupp.single (0 : Fin 1) (m 0) := by
        refine Finsupp.ext fun i => ?_
        have hi : i = 0 := Subsingleton.elim _ _
        subst hi
        by_cases h : m 0 = 0
        · simp [h]
        · simp [h]
      have hmsum : m.sum (fun _ e => e) = m 0 := by
        rw [hm0, Finsupp.sum_single_index]
        simp
      have hmono : MvPolynomial.monomial m (MvPolynomial.coeff m R) =
          MvPolynomial.C (MvPolynomial.coeff m R) *
            MvPolynomial.X (0 : Fin 1) ^ m.sum (fun _ e => e) := by
        rw [hm0, MvPolynomial.monomial_single]
      simp only [map_mul, map_pow, blockEval_X]
      rw [if_pos rfl, if_neg (linePartner_ne M j), if_pos rfl, one_pow]
      rw [hmsum, ← hmono])
  exact (MvPolynomial.as_sum R).symm

/-- **THE CHART MAP IS INJECTIVE** — the clearing + retraction: rescale
every monomial evaluation to the common degree `N`, sum to the fraction of
the lift, clear the denominator through the localization zero-criterion,
and retract through the block projection. -/
theorem chartMap_injective (M : ℕ) [NeZero M] (j : Fin (2 * M)) :
    Function.Injective (chartMap M j) := by
  have hz : ∀ R : MvPolynomial (Fin 1) ℂ, chartMap M j R = 0 → R = 0 := by
    intro R hR
    classical
    set N : ℕ := R.support.sup fun m => m.sum fun _ e => e with hN
    have hle : ∀ m ∈ R.support, m.sum (fun _ e => e) ≤ N :=
      fun m hm => Finset.le_sup hm
    -- the graded family: the rescaled numerators at degree N
    set y : (Fin 1 →₀ ℕ) → lineQuotient M := fun m =>
      lineQuotientMap M (MvPolynomial.X j ^ (N - m.sum (fun _ e => e)) *
        (MvPolynomial.C (MvPolynomial.coeff m R) *
          MvPolynomial.X (linePartner M j) ^ m.sum (fun _ e => e))) with hy
    have hymem : ∀ m ∈ R.support, y m ∈ lineGrading M (N • 1) := by
      intro m hm
      apply lineQuotientMap_mem_lineGrading_smul M N _
      have hc : MvPolynomial.C (MvPolynomial.coeff m R) ∈
          MvPolynomial.homogeneousSubmodule (Fin (2 * M)) ℂ 0 :=
        (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
          (MvPolynomial.isHomogeneous_C (σ := Fin (2 * M)) (R := ℂ) _)
      have hjp : MvPolynomial.X j ^ (N - m.sum (fun _ e => e)) ∈
          MvPolynomial.homogeneousSubmodule (Fin (2 * M)) ℂ
            (N - m.sum (fun _ e => e)) := by
        refine (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
          (MvPolynomial.isHomogeneous_monomial 1 ?_)
        rw [show MvPolynomial.X j ^ (N - m.sum (fun _ e => e)) =
            MvPolynomial.monomial (Finsupp.single j
              (N - m.sum (fun _ e => e))) 1 from
          (MvPolynomial.X_pow_eq_monomial _ _).symm]
        rw [Finsupp.degree_eq_weight_one]
        exact Finsupp.ext fun _ => one_mul _
      have hpp : MvPolynomial.X (linePartner M j) ^ m.sum (fun _ e => e) ∈
          MvPolynomial.homogeneousSubmodule (Fin (2 * M)) ℂ
            (m.sum fun _ e => e) := by
        refine (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
          (MvPolynomial.isHomogeneous_monomial 1 ?_)
        rw [show MvPolynomial.X (linePartner M j) ^ m.sum (fun _ e => e) =
            MvPolynomial.monomial (Finsupp.single (linePartner M j)
              (m.sum fun _ e => e)) 1 from
          (MvPolynomial.X_pow_eq_monomial _ _).symm]
        rw [Finsupp.degree_eq_weight_one]
        exact Finsupp.ext fun _ => one_mul _
      have hstep1 := Submodule.mul_mem_mul hc hjp
      have hstep2 := Submodule.mul_mem_mul hstep1 hpp
      have hstep3 := MvPolynomial.homogeneousSubmodule_mul (Fin (2 * M)) ℂ
        (0 + (N - m.sum (fun _ e => e))) (m.sum fun _ e => e) hstep2
      rw [zero_add, ← add_nsmul, Nat.sub_add_cancel (hle m hm)] at hstep3
      exact hstep3
    -- the rescaling: every monomial evaluation is the degree-N fraction
    have hrescale : ∀ m ∈ R.support, chartMap M j
          (MvPolynomial.monomial m (MvPolynomial.coeff m R)) =
        HomogeneousLocalization.Away.mk (lineGrading M)
          (lineCoverHomogeneousOneQ M j) N (y m) (hymem m (by assumption)) := by
      intro m hm
      have hm' : m ∈ R.support := hm
      rw [chartMap_monomial M j m (MvPolynomial.coeff m R),
        away_mk_rescale M j (m.sum (fun _ e => e)) N (hle m hm)
          (lineQuotientMap M (MvPolynomial.C (MvPolynomial.coeff m R) *
            MvPolynomial.X (linePartner M j) ^ m.sum (fun _ e => e)))
          (lineQuotientMap_mem_lineGrading_smul M _ _
            (by
              have hc : MvPolynomial.C (MvPolynomial.coeff m R) ∈
                  MvPolynomial.homogeneousSubmodule (Fin (2 * M)) ℂ 0 :=
                (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
                  (MvPolynomial.isHomogeneous_C (σ := Fin (2 * M)) (R := ℂ) _)
              have hpp : MvPolynomial.X (linePartner M j) ^
                  m.sum (fun _ e => e) ∈
                  MvPolynomial.homogeneousSubmodule (Fin (2 * M)) ℂ
                    (m.sum fun _ e => e) := by
                refine (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
                  (MvPolynomial.isHomogeneous_monomial 1 ?_)
                rw [show MvPolynomial.X (linePartner M j) ^
                    m.sum (fun _ e => e) =
                    MvPolynomial.monomial (Finsupp.single (linePartner M j)
                      (m.sum fun _ e => e)) 1 from
                  (MvPolynomial.X_pow_eq_monomial _ _).symm]
                rw [Finsupp.degree_eq_weight_one]
                exact Finsupp.ext fun _ => one_mul _
              have hstep1 := Submodule.mul_mem_mul hc hpp
              have hstep2 := MvPolynomial.homogeneousSubmodule_mul
                (Fin (2 * M)) ℂ 0 (m.sum fun _ e => e) hstep1
              rwa [zero_add] at hstep2))]
      rw [hy]
      rfl
    -- the total graded family (the subtype carrier)
    set x : (Fin 1 →₀ ℕ) → ↥(lineGrading M (N • 1)) := fun m =>
      ⟨y m, by
        by_cases hm : m ∈ R.support
        · exact hymem m hm
        · have hc : MvPolynomial.coeff m R = 0 := by
            intro hcon
            exact hm (MvPolynomial.mem_support_iff.mpr hcon)
          have hy0 : y m = 0 := by
            rw [hy]
            simp [hc]
          rw [hy0]
          exact (lineGrading M (N • 1)).zero_mem⟩ with hx
    -- the rescaling in the subtype spelling (proof irrelevance identifies
    -- the membership proofs)
    have hrescale' : ∀ m ∈ R.support, chartMap M j
          (MvPolynomial.monomial m (MvPolynomial.coeff m R)) =
        HomogeneousLocalization.Away.mk (lineGrading M)
          (lineCoverHomogeneousOneQ M j) N (x m : lineQuotient M) (x m).2 :=
      fun m hm => hrescale m hm
    -- the sum: the chart map of R is the fraction of the summed family
    have hsum : HomogeneousLocalization.Away.mk (lineGrading M)
        (lineCoverHomogeneousOneQ M j) N (∑ m ∈ R.support, (x m : lineQuotient M))
        (Submodule.sum_mem (lineGrading M (N • 1))
          (fun m hm => (x m).2)) = 0 := by
      rw [← sum_mk_eq M j N R.support x,
        Finset.sum_congr rfl (fun m hm => hrescale' m hm),
        ← MvPolynomial.as_sum R, map_sum, hR]
    -- the numerator is the lift's image
    have hnum : ∑ m ∈ R.support, (x m : lineQuotient M) =
        lineQuotientMap M (blockLift M j R N) := by
      have hcoe : ∀ m : Fin 1 →₀ ℕ, (x m : lineQuotient M) = y m := fun m => rfl
      rw [Finset.sum_congr rfl (fun m _ => hcoe m), hy, blockLift, map_sum]
      rw [Finset.sum_congr rfl (fun m _ =>
        by
          simp only [map_mul]
          noncomm_ring)]
    -- the clearing: zero fraction, denominator cleared, retract
    have hv : Localization.mk (lineQuotientMap M (blockLift M j R N))
        ⟨(lineQuotientMap M (MvPolynomial.X j)) ^ N,
          (Submonoid.mem_powers_iff _ _).mpr ⟨N, rfl⟩⟩ = 0 := by
      have h0 := congrArg HomogeneousLocalization.val hsum
      rw [HomogeneousLocalization.Away.val_mk,
        HomogeneousLocalization.val_zero] at h0
      rw [show lineQuotientMap M (blockLift M j R N) =
          ∑ m ∈ R.support, (x m : lineQuotient M) from hnum.symm]
      exact h0
    rw [Localization.mk_eq_zero_iff] at hv
    obtain ⟨t, ht, htz⟩ := hv
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp ht
    -- clear: q (X j ^ k * lift) = 0
    have hmul : lineQuotientMap M
        (MvPolynomial.X j ^ k * blockLift M j R N) = 0 := by
      rw [map_mul, ← map_pow, ← hk]
      exact htz
    have hcross : MvPolynomial.X j ^ k * blockLift M j R N ∈ crossIdeal M :=
      lineQuotientMap_eq_zero_iff.mp hmul
    have hbe := blockEval_mem_crossIdeal M j hcross
    rw [map_mul, map_pow, blockEval_X, if_pos rfl, one_pow, one_mul] at hbe
    rw [blockEval_blockLift M j R N] at hbe
    exact hbe
  intro P Q hPQ
  have hP : P - Q = 0 := by
    refine hz (P - Q) ?_
    rw [map_sub, hPQ, sub_self]
  exact sub_eq_zero.mp hP

/-- **THE CHART EQUIVALENCE** — the chart ring IS the polynomial algebra. -/
noncomputable def chartEquiv (M : ℕ) [NeZero M] (j : Fin (2 * M)) :
    MvPolynomial (Fin 1) ℂ ≃ₐ[ℂ]
      HomogeneousLocalization.Away (lineGrading M)
        (lineQuotientMap M (MvPolynomial.X j)) :=
  AlgEquiv.ofBijective (chartMap M j)
    ⟨chartMap_injective M j, chartMap_surjective M j⟩

/-- The polynomial algebra is a smooth ℂ-algebra (the pin's
`FormallySmooth` MvPolynomial instance + finite presentation). -/
instance : Algebra.Smooth ℂ (MvPolynomial (Fin 1) ℂ) :=
  ⟨inferInstance, inferInstance⟩

/-- **THE CHART RING IS SMOOTH** — the F3 battle's kill: the chart ring is
the polynomial algebra (the chart equivalence), and smoothness transports
along algebra isomorphisms (the pin's `Algebra.Smooth.of_equiv`). -/
theorem chart_smooth (M : ℕ) [NeZero M] (j : Fin (2 * M)) :
    Algebra.Smooth ℂ (HomogeneousLocalization.Away (lineGrading M)
      (lineQuotientMap M (MvPolynomial.X j))) :=
  Algebra.Smooth.of_equiv (chartEquiv M j)

/-- **THE CHART RING HOM IS SMOOTH** — the consumption form (the §5
square's ring map): `RingHom.Smooth` unfolds against the induced algebra
structure, where the chart smoothness applies. -/
theorem chart_ringHom_smooth (M : ℕ) [NeZero M] (j : Fin (2 * M)) :
    RingHom.Smooth (chartRingHom M j) :=
  chart_smooth M j

/-! ## §8 THE CASCADE — the structure map is smooth -/

/-- **THE FINITE-LINE WORLD IS SMOOTH OVER ℂ** — the F3 gate: the structure
morphism is smooth.  The locality cascade: smoothness is local at the
source (`IsZariskiLocalAtSource.iff_of_iSup_eq_top`, the pin's
Morphisms/Basic.lean:272); the source is covered by the `D+(q (X j))`
charts (the quotient-side cover twins feeding `Proj.iSup_basicOpen_eq_top'`);
per chart, the composite is the away-chart of the structure map (the
`basicOpenIsoSpec_inv_ι` retype), which the §5 square identifies with the
`Spec` of the chart's ℂ-structure ring hom; the affine criterion
(`HasRingHomProperty.Spec_iff`) reduces to the chart ring hom's smoothness
— the §7 battle's kill. -/
theorem finiteLine_smoothness (M : ℕ) [NeZero M] :
    Smooth (finiteLineStructureMap M) := by
  rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := @Smooth)
    (fun j => Proj.basicOpen (lineGrading M)
      (lineQuotientMap M (MvPolynomial.X j)))
    (Proj.iSup_basicOpen_eq_top' (lineGrading M)
      (fun j => lineQuotientMap M (MvPolynomial.X j))
      (lineCoverHomogeneousQ M) (lineCoverAdjoin M))]
  intro j
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @Smooth)
    (Proj.basicOpenIsoSpec (lineGrading M)
      (lineQuotientMap M (MvPolynomial.X j))
      (lineCoverHomogeneousOneQ M j) zero_lt_one).inv,
    ← CategoryTheory.Category.assoc,
    Proj.basicOpenIsoSpec_inv_ι,
    chart_awayι_comp']
  exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
    (chart_ringHom_smooth M j)

/-! ## Receipts -/

#check linePartner
#check lineCoverHomogeneousOneQ
#check lineCoverAdjoin
#check blockEvalQuot
#check chartRingHom
#check chartRatio
#check chartMap
#check chartMap_surjective
#check chartMap_injective
#check chartEquiv
#check chart_smooth
#check chart_ringHom_smooth
#check chart_awayι_comp'
#check finiteLine_smoothness

#print axioms linePartner_involution
#print axioms lineCoverAdjoin
#print axioms chart_awayι_comp'
#print axioms chartMap_surjective
#print axioms chartMap_injective
#print axioms chart_smooth
#print axioms finiteLine_smoothness

end GSTFiniteLineSmoothness

end
