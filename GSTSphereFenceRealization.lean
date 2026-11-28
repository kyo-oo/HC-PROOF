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

With this theorem the fence chain is: the separator's EXISTENCE at the
corrected cycle (FENCE-S, the `Basis.extend` extension route) ⟹ THIS
MODULE ⟹ FENCE-Ω (`∃ ω ≠ 0`) ⟹ `GSTFiniteLineFenceDischarge` ⟹ the
unconditional wave-9 package with the independence conjunct unguarded.

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

/-- AUDIT: the incoming leg of the degree-2 short complex IS the
degree 1→2 dual differential (the `up ℕ` shape at an interior degree). -/
theorem sc_two_f :
    sphereDualShortComplexTwo.f =
      (singularCochainsOf (TopCat.of unitSphereType)).d 1 2 := rfl

/-- AUDIT: the outgoing leg IS the degree 2→3 dual differential. -/
theorem sc_two_g :
    sphereDualShortComplexTwo.g =
      (singularCochainsOf (TopCat.of unitSphereType)).d 2 3 := rfl

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
  rw [cochains_d_two_three]
  simp only [ModuleCat.ofHom_apply, Linear.leftComp_apply]
  apply ModuleCat.hom_injective
  rw [fundCochain_hom]
  refine LinearMap.ext fun w => ?_
  exact hvan w

/-! ## §3 The realization (the NZC-3/NZC-4 seams) -/

/-- The kernel-membership spelling of the cocycle law, at the short
complex's outgoing leg. -/
theorem fundCochain_mem_ker (φ : sphereChainsTwo →ₗ[ℚ] ℚ)
    (hvan : ∀ w : sphereChainsThree, φ (sphereBoundaryThree w) = 0) :
    fundCochain φ ∈ LinearMap.ker
      (sphereDualShortComplexTwo.g).hom := by
  rw [sc_two_g, LinearMap.mem_ker]
  exact fundCochain_d φ hvan

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
  -- quotient presentation of the degree-2 homology
  refine ⟨sphereDualShortComplexTwo.moduleCatHomologyIso.inv
    (Submodule.mkQ
      (LinearMap.range sphereDualShortComplexTwo.moduleCatToCycles)
      ⟨fundCochain φ, fundCochain_mem_ker φ hvan⟩), ?_⟩
  intro hzero
  -- the roundtrip: the iso's inverse followed by the iso is the
  -- identity on the quotient, so the quotient class itself is zero
  have hround :
      (sphereDualShortComplexTwo.moduleCatHomologyIso.hom)
        (sphereDualShortComplexTwo.moduleCatHomologyIso.inv
          (Submodule.mkQ
            (LinearMap.range sphereDualShortComplexTwo.moduleCatToCycles)
            ⟨fundCochain φ, fundCochain_mem_ker φ hvan⟩)) =
        Submodule.mkQ
          (LinearMap.range sphereDualShortComplexTwo.moduleCatToCycles)
          ⟨fundCochain φ, fundCochain_mem_ker φ hvan⟩ := by
    simpa using DFunLike.congr_fun
      (sphereDualShortComplexTwo.moduleCatHomologyIso.inv_hom_id) _
  have hzero' :
      Submodule.mkQ
        (LinearMap.range sphereDualShortComplexTwo.moduleCatToCycles)
        ⟨fundCochain φ, fundCochain_mem_ker φ hvan⟩ = 0 := by
    calc Submodule.mkQ
        (LinearMap.range sphereDualShortComplexTwo.moduleCatToCycles)
        ⟨fundCochain φ, fundCochain_mem_ker φ hvan⟩ =
        (sphereDualShortComplexTwo.moduleCatHomologyIso.hom)
          (sphereDualShortComplexTwo.moduleCatHomologyIso.inv
            (Submodule.mkQ
              (LinearMap.range sphereDualShortComplexTwo.moduleCatToCycles)
              ⟨fundCochain φ, fundCochain_mem_ker φ hvan⟩)) := hround.symm
      _ = (sphereDualShortComplexTwo.moduleCatHomologyIso.hom) 0 := by
          rw [hzero]
      _ = 0 := map_zero _ _
  -- (NZC-4) the quotient-zero is the boundary-membership
  rw [Submodule.Quotient.mk_eq_zero] at hzero'
  obtain ⟨ψ, hψ⟩ := LinearMap.mem_range.mp hzero'
  -- the coboundary equation at the differential spelling
  have hval : (sphereDualShortComplexTwo.f).hom ψ = fundCochain φ :=
    congrArg Subtype.val hψ
  have hval' : (singularCochainsOf (TopCat.of unitSphereType)).d 1 2 ψ
      = fundCochain φ := by
    rw [← sc_two_f]
    exact hval
  -- the separator reads 1 on the fundamental cycle
  have hone' : (fundCochain φ).hom fundCycle = 1 := by
    rw [fundCochain_hom]
    exact hone
  -- but a coboundary reads 0 on every cycle (THE CYCLE LAW)
  have hzero'' : (fundCochain φ).hom fundCycle = 0 := by
    rw [← hval', dual_eval_one_two]
    have hcy : (singularChainsOf (TopCat.of unitSphereType)).d 2 1
        fundCycle = 0 := fundCycle_d
    rw [hcy, map_zero]
  exact zero_ne_one (hzero''.symm.trans hone')

end GSTSphereFenceRealization

end -- noncomputable section
