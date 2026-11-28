import Mathlib
import GSTSphereFundamentalCycle

/-
Copyright (c) 2026. The HC-PROOF campaign. All rights reserved.

# THE FENCE REALIZATION — the separator-to-class theorem (wave 12)

BOSS's order (the Y-audit round): map the theorems of the corpus, MERGE
the files, CREATE the new theorem/law, PROVE the remaining subcase.  The
remaining subcase of the X→Y audit is FENCE-Ω's final conditional seam —
the statement FROZEN at `GSTSphereFundamentalCycle.lean:454-456` (and in
the NZC design of `GSTSphereNonzeroClass.lean`'s PORT NOTES):

    theorem exists_nonzero_sphere_cohomology_two_of_fundseparator
        (hsep : FundSeparator) :
        ∃ ω : singularCohomologyOf (TopCat.of unitSphereType) 2, ω ≠ 0

THE MERGE (this module imports and combines — BOSS's own mathematics):

* `GSTSphereFundamentalCycle` — `fundCycle` (the center-radial
  fundamental 2-cycle, :400), `fundCycle_d` (THE CYCLE LAW, :408),
  `FundSeparator` (the corrected separator shape, :429),
  `no_separator_of_boundary` (:440) — all CI-green at `9261e74`
  (run 45889388303);
* `GSTSingularCohomologyMaps` — `singularCochainsOf` (the
  `linearYonedaObj` dual complex, :53), `singularCohomologyOf`
  (the homology, :62-67) — CI-green;
* the degree-0/1 dual-differential receipts of
  `GSTComponentCohomologyZero` (`cochains_d_zero_one`, `dual_eval`,
  `leftComp_apply_eq` — the CI-verified spellings of
  `ChainComplex.linearYonedaObj_d` and `Linear.leftComp`), re-pointed at
  degrees 1→2 and 2→3;
* Mathlib's `ShortComplex.ModuleCat` homology API —
  `moduleCatHomologyIso` (the homology of a short complex of modules IS
  the quotient `ker g ⧸ range (toCycles)`), `moduleCatToCycles`,
  `moduleCatLeftHomologyData` — the explicit quotient presentation.

THE REALIZATION ARGUMENT (classical, over the field ℚ):

* (NZC-2, the cocycle) a separator `φ : C₂ →ₗ ℚ` vanishing on all
  degree-3 boundaries IS a degree-2 cocycle of the dual complex: the
  dual differential is precomposition with the boundary
  (`ChainComplex.linearYonedaObj_d`), so `(δφ) w = φ (d₃ w) = 0` —
  exactly the boundary-vanishing condition of `FundSeparator`;
* (NZC-3, the class) the witness `ω` is the separator's cocycle class,
  constructed through `moduleCatHomologyIso` as the quotient class of
  the kernel element `⟨fundCochain φ, cocycle-membership⟩`;
* (NZC-4, the nonvanishing) if `ω = 0`, the quotient lemma
  (`Submodule.Quotient.mk_eq_zero`) puts the cocycle in the range of the
  degree-1 dual differential: `fundCochain φ = δψ` as cochains — then
  `1 = φ(fundCycle) = ψ(d₂ fundCycle) = ψ(0) = 0` by THE CYCLE LAW
  `fundCycle_d` — contradiction.

STRIKE LEDGER.  Strike 1 (run 46088645263): the dual-differential
receipts, both adjunction evaluations, the wrapped separator, and the
witness's type-checking ALL GREEN on first compile; red on (i) the two
sc-leg bridges (rfl defeated by the `prev 2`/`next 2` shape indices —
repaired with the `GSTComponentCohomologyZero.homologyZeroIsoKer`
unfold recipe + `CochainComplex.prev_nat_succ`/`CochainComplex.next`),
(ii) the cocycle law's tactic order (the pre-unfolding broke the
`dual_eval` pattern match — repaired by evaluating AFTER
`ModuleCat.hom_injective` + `LinearMap.ext`), (iii) the iso roundtrip
(`DFunLike.congr_fun` does not apply to `ModuleCat.Hom` — the
application goes through the `ConcreteCategory` coercion — repaired
with `CategoryTheory.congr_hom` + `comp_apply` + `id_apply`), (iv) a
calc parse break at an anonymous constructor — repaired by
parenthesization.

With this theorem the fence chain is: the separator's EXISTENCE at the
corrected cycle (FENCE-S, the `Basis.extend` extension route, the next
wave) ⟹ THIS MODULE ⟹ FENCE-Ω (`∃ ω ≠ 0`) ⟹
`GSTFiniteLineFenceDischarge` ⟹ the unconditional wave-9 package with
the independence conjunct unguarded.

HONESTY LEDGER. Every statement proved here is unconditional. No `sorry`,
no new axioms, no `native_decide`. The GitHub CI lane
`gst-sphere-fence-discharge.yml` owns the kernel check (Ladder 6/6).
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
open GSTSphereNonzeroClass
open GSTSphereFundamentalCycle

namespace GSTSphereFenceRealization

/-! ## §0 The degree-2 short complex of the dual -/

/-- The degree-2 short complex of the sphere's dual cochain complex:
`C¹ --δ--> C² --δ--> C³` in the `linearYonedaObj` dual spelling. -/
abbrev sphereDualShortComplexTwo : ShortComplex (ModuleCat ℚ) :=
  (singularCochainsOf (TopCat.of unitSphereType)).sc 2

/-- The `up ℕ` shape index at an interior degree: `prev 2 = 1`. -/
theorem upPrev_two : (ComplexShape.up ℕ).prev 2 = 1 :=
  CochainComplex.prev_nat_succ 1

/-- The `up ℕ` shape index at an interior degree: `next 2 = 3`. -/
theorem upNext_two : (ComplexShape.up ℕ).next 2 = 3 :=
  CochainComplex.next ℕ 2

/-- AUDIT: the incoming leg of the degree-2 short complex, at its own
shape-indexed differential spelling (the `up ℕ` shape's `prev` is
choice-derived — opaque to defeq — so the bridge is stated at the
`prev 2` index and fixed at `1` by the rewrite). -/
theorem sc_two_f :
    sphereDualShortComplexTwo.f =
      (singularCochainsOf (TopCat.of unitSphereType)).d
        ((ComplexShape.up ℕ).prev 2) 2 := by
  unfold sphereDualShortComplexTwo HomologicalComplex.sc
    HomologicalComplex.shortComplexFunctor
    HomologicalComplex.shortComplexFunctor'
  rw [upPrev_two]

/-- AUDIT: the outgoing leg at its own `next 2`-indexed spelling. -/
theorem sc_two_g :
    sphereDualShortComplexTwo.g =
      (singularCochainsOf (TopCat.of unitSphereType)).d
        2 ((ComplexShape.up ℕ).next 2) := by
  unfold sphereDualShortComplexTwo HomologicalComplex.sc
    HomologicalComplex.shortComplexFunctor
    HomologicalComplex.shortComplexFunctor'
  rw [upNext_two]

/-! ## §1 The dual differential presentation (the NZC-2 seam) -/

/-- AUDIT: the degree 2→3 differential of the dual cochain complex is
precomposition with the degree 3→2 chain boundary — the pinned
`ChainComplex.linearYonedaObj_d`, the degree-0/1 receipt of
`GSTComponentCohomologyZero.cochains_d_zero_one` re-pointed at 2→3. -/
theorem cochains_d_two_three :
    (singularCochainsOf (TopCat.of unitSphereType)).d 2 3 =
      ModuleCat.ofHom
        (Linear.leftComp ℚ (ModuleCat.of ℚ ℚ)
          ((singularChainsOf (TopCat.of unitSphereType)).d 3 2)) := by
  unfold singularCochainsOf
  exact ChainComplex.linearYonedaObj_d
    (singularChainsOf (TopCat.of unitSphereType)) ℚ (ModuleCat.of ℚ ℚ) 2 3

/-- AUDIT: the degree 1→2 differential, the same pinned receipt. -/
theorem cochains_d_one_two :
    (singularCochainsOf (TopCat.of unitSphereType)).d 1 2 =
      ModuleCat.ofHom
        (Linear.leftComp ℚ (ModuleCat.of ℚ ℚ)
          ((singularChainsOf (TopCat.of unitSphereType)).d 2 1)) := by
  unfold singularCochainsOf
  exact ChainComplex.linearYonedaObj_d
    (singularChainsOf (TopCat.of unitSphereType)) ℚ (ModuleCat.of ℚ ℚ) 1 2

/-- **THE ADJUNCTION-STYLE EVALUATION at 2→3.** The dual differential
applied to a degree-2 cochain is precomposition with the boundary. -/
theorem dual_eval_two_three
    (φ : (singularCochainsOf (TopCat.of unitSphereType)).X 2)
    (w : (singularChainsOf (TopCat.of unitSphereType)).X 3) :
    ((singularCochainsOf (TopCat.of unitSphereType)).d 2 3 φ).hom w =
      φ.hom ((singularChainsOf (TopCat.of unitSphereType)).d 3 2 w) := by
  rw [cochains_d_two_three]
  simp only [ModuleCat.ofHom_apply, Linear.leftComp_apply]
  rfl

/-- **THE ADJUNCTION-STYLE EVALUATION at 1→2.** -/
theorem dual_eval_one_two
    (ψ : (singularCochainsOf (TopCat.of unitSphereType)).X 1)
    (z : (singularChainsOf (TopCat.of unitSphereType)).X 2) :
    ((singularCochainsOf (TopCat.of unitSphereType)).d 1 2 ψ).hom z =
      ψ.hom ((singularChainsOf (TopCat.of unitSphereType)).d 2 1 z) := by
  rw [cochains_d_one_two]
  simp only [ModuleCat.ofHom_apply, Linear.leftComp_apply]
  rfl

/-! ## §2 The separator as a cocycle -/

/-- **THE WRAPPED SEPARATOR.** The separator's functional as a degree-2
element of the dual complex. -/
def fundCochain (φ : sphereChainsTwo →ₗ[ℚ] ℚ) :
    (singularCochainsOf (TopCat.of unitSphereType)).X 2 :=
  ModuleCat.ofHom φ

/-- The wrapped separator reads as the separator. -/
theorem fundCochain_hom (φ : sphereChainsTwo →ₗ[ℚ] ℚ) :
    (fundCochain φ).hom = φ := rfl

/-- **THE COCYCLE LAW.** The separator vanishes on every degree-3
boundary, and the dual differential is precomposition with the
boundary — so the wrapped separator IS a cocycle of the dual complex. -/
theorem fundCochain_d (φ : sphereChainsTwo →ₗ[ℚ] ℚ)
    (hvan : ∀ w : sphereChainsThree, φ (sphereBoundaryThree w) = 0) :
    (singularCochainsOf (TopCat.of unitSphereType)).d 2 3
      (fundCochain φ) = 0 := by
  apply ModuleCat.hom_injective
  refine LinearMap.ext fun w => ?_
  rw [dual_eval_two_three, fundCochain_hom]
  exact hvan w

/-- **THE COCYCLE LAW at the shape-indexed differential** — the
`next 2`-indexed form, transported from `fundCochain_d` by the
index rewrite in a standalone statement (where the motive is
type-correct). -/
theorem fundCochain_d_indexed (φ : sphereChainsTwo →ₗ[ℚ] ℚ)
    (hvan : ∀ w : sphereChainsThree, φ (sphereBoundaryThree w) = 0) :
    (singularCochainsOf (TopCat.of unitSphereType)).d 2
      ((ComplexShape.up ℕ).next 2) (fundCochain φ) = 0 := by
  rw [upNext_two]
  exact fundCochain_d φ hvan

/-- The kernel-membership spelling of the cocycle law, at the short
complex's outgoing leg. -/
theorem fundCochain_mem_ker (φ : sphereChainsTwo →ₗ[ℚ] ℚ)
    (hvan : ∀ w : sphereChainsThree, φ (sphereBoundaryThree w) = 0) :
    fundCochain φ ∈ LinearMap.ker
      (sphereDualShortComplexTwo.g).hom := by
  have h1 : (sphereDualShortComplexTwo.g).hom (fundCochain φ) = 0 := by
    rw [sc_two_g]
    exact fundCochain_d_indexed φ hvan
  exact LinearMap.mem_ker.mp h1

/-- AUDIT: the degree `prev 2`→2 differential, the pinned receipt at the
shape-indexed degrees. -/
theorem cochains_d_prev_two :
    (singularCochainsOf (TopCat.of unitSphereType)).d
        ((ComplexShape.up ℕ).prev 2) 2 =
      ModuleCat.ofHom
        (Linear.leftComp ℚ (ModuleCat.of ℚ ℚ)
          ((singularChainsOf (TopCat.of unitSphereType)).d 2
            ((ComplexShape.up ℕ).prev 2))) := by
  unfold singularCochainsOf
  exact ChainComplex.linearYonedaObj_d
    (singularChainsOf (TopCat.of unitSphereType)) ℚ (ModuleCat.of ℚ ℚ)
    ((ComplexShape.up ℕ).prev 2) 2

/-- **THE ADJUNCTION-STYLE EVALUATION at `prev 2`→2** — the indexed
form, for the coboundary equation's own world. -/
theorem dual_eval_one_two_indexed
    (ψ : (singularCochainsOf (TopCat.of unitSphereType)).X
      ((ComplexShape.up ℕ).prev 2))
    (z : (singularChainsOf (TopCat.of unitSphereType)).X 2) :
    ((singularCochainsOf (TopCat.of unitSphereType)).d
        ((ComplexShape.up ℕ).prev 2) 2 ψ).hom z =
      ψ.hom ((singularChainsOf (TopCat.of unitSphereType)).d 2
        ((ComplexShape.up ℕ).prev 2) z) := by
  rw [cochains_d_prev_two]
  simp only [ModuleCat.ofHom_apply, Linear.leftComp_apply]
  rfl

/-! ## §3 The realization (the NZC-3/NZC-4 seams) -/

/-- **THE SEPARATOR REALIZES TO A NONZERO CLASS** — the frozen statement
of `GSTSphereFundamentalCycle.lean:454-456`, proved: every separator is
a cocycle of the honest sphere's rational singular cochain complex, and
its cohomology class is NONZERO (a coboundary vanishes on every cycle,
so it cannot read `1` on `fundCycle`). -/
theorem exists_nonzero_sphere_cohomology_two_of_fundseparator
    (hsep : FundSeparator) :
    ∃ ω : singularCohomologyOf (TopCat.of unitSphereType) 2, ω ≠ 0 := by
  obtain ⟨φ, hvan, hone⟩ := hsep
  -- (NZC-3) the witness: the separator's class, through the explicit
  -- quotient presentation of the degree-2 homology (the LinearMap-level
  -- spelling — every application below is a core linear-map lemma)
  refine ⟨(sphereDualShortComplexTwo.moduleCatHomologyIso.inv).hom
    (Submodule.mkQ
      (LinearMap.range sphereDualShortComplexTwo.moduleCatToCycles)
      ⟨fundCochain φ, fundCochain_mem_ker φ hvan⟩), ?_⟩
  intro hzero
  -- the roundtrip: the iso's underlying linear maps compose to the
  -- identity (the `inv_hom_id` homology transported to LinearMap-land)
  have hcomp :
      (sphereDualShortComplexTwo.moduleCatHomologyIso.hom).hom.comp
        (sphereDualShortComplexTwo.moduleCatHomologyIso.inv).hom
        = LinearMap.id :=
    congrArg ModuleCat.Hom.hom
      (sphereDualShortComplexTwo.moduleCatHomologyIso.inv_hom_id)
  -- the roundtrip at the quotient element (the congrArg-lambda's domain
  -- spelled explicitly — no instance synthesis against metavariables)
  have hgen : ∀ Q : ↥(LinearMap.ker (sphereDualShortComplexTwo.g).hom) ⧸
      LinearMap.range sphereDualShortComplexTwo.moduleCatToCycles,
      (sphereDualShortComplexTwo.moduleCatHomologyIso.hom).hom
        ((sphereDualShortComplexTwo.moduleCatHomologyIso.inv).hom Q) = Q := by
    intro Q
    exact congrArg (fun L : ↥(LinearMap.ker (sphereDualShortComplexTwo.g).hom) ⧸
        LinearMap.range sphereDualShortComplexTwo.moduleCatToCycles →ₗ[ℚ]
        ↥(LinearMap.ker (sphereDualShortComplexTwo.g).hom) ⧸
        LinearMap.range sphereDualShortComplexTwo.moduleCatToCycles => L Q) hcomp
  have hround :
      (sphereDualShortComplexTwo.moduleCatHomologyIso.hom).hom
        ((sphereDualShortComplexTwo.moduleCatHomologyIso.inv).hom
          (Submodule.mkQ
            (LinearMap.range sphereDualShortComplexTwo.moduleCatToCycles)
            ⟨fundCochain φ, fundCochain_mem_ker φ hvan⟩)) =
        Submodule.mkQ
          (LinearMap.range sphereDualShortComplexTwo.moduleCatToCycles)
          ⟨fundCochain φ, fundCochain_mem_ker φ hvan⟩ :=
    hgen _
  have hzero' :
      Submodule.mkQ
        (LinearMap.range sphereDualShortComplexTwo.moduleCatToCycles)
        ⟨fundCochain φ, fundCochain_mem_ker φ hvan⟩ = 0 := by
    have h2 :
        (sphereDualShortComplexTwo.moduleCatHomologyIso.hom).hom
          ((sphereDualShortComplexTwo.moduleCatHomologyIso.inv).hom
            (Submodule.mkQ
              (LinearMap.range sphereDualShortComplexTwo.moduleCatToCycles)
              ⟨fundCochain φ, fundCochain_mem_ker φ hvan⟩)) =
        (sphereDualShortComplexTwo.moduleCatHomologyIso.hom).hom 0 :=
      congrArg _ hzero
    exact (hround.symm.trans h2).trans (LinearMap.map_zero _)
  -- (NZC-4) the quotient-zero is the boundary-membership (the mkQ/mk
  -- defeq is rfl — Submodule.mkQ_apply; the memberships extracted by
  -- direct iff-application, no keyed rewrites)
  obtain ⟨ψ, hψ⟩ := LinearMap.mem_range.mp
    ((Submodule.Quotient.mk_eq_zero _).mp hzero')
  -- the coboundary equation at the shape-indexed differential spelling
  have hval : (sphereDualShortComplexTwo.f).hom ψ = fundCochain φ :=
    congrArg Subtype.val hψ
  have hval' : (singularCochainsOf (TopCat.of unitSphereType)).d
      ((ComplexShape.up ℕ).prev 2) 2 ψ = fundCochain φ := by
    rw [← sc_two_f]
    exact hval
  -- the separator reads 1 on the fundamental cycle
  have hone' : (fundCochain φ).hom fundCycle = 1 := by
    rw [fundCochain_hom]
    exact hone
  -- but a coboundary reads 0 on every cycle (THE CYCLE LAW — the
  -- indexed evaluation applied directly, the cycle law transported)
  have hcy : (singularChainsOf (TopCat.of unitSphereType)).d 2
      ((ComplexShape.up ℕ).prev 2) fundCycle = 0 := by
    rw [upPrev_two]
    exact fundCycle_d
  have hzero'' : (fundCochain φ).hom fundCycle = 0 := by
    rw [← hval']
    exact (dual_eval_one_two_indexed ψ fundCycle).trans (by
      rw [hcy]; exact map_zero _ _)
  exact zero_ne_one (hzero''.symm.trans hone')

end GSTSphereFenceRealization

end -- noncomputable section
