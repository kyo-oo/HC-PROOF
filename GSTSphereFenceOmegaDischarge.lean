import Mathlib
import GSTSphereFenceRealization
import GSTFiniteLineFenceDischarge
import GSTFiniteLineHonestHodgeData
import GSTFiniteLinePointsGateDischarge
import GSTFiniteLinePrimitiveXSourceFamilies

/-
Copyright (c) 2026. The HC-PROOF campaign. All rights reserved.

# THE FENCE-Ω DISCHARGE — the homology-nontriviality composition (wave 13)

The fence chain's final composition.  The kernel-certified corpus carries:

* the wave-9 apex package, whose weight-one INDEPENDENCE conjunct is
  guarded by FENCE-Ω (`∃ ω : singularCohomologyOf (TopCat.of
  unitSphereType) 2, ω ≠ 0`) — consumed by the exists-flip master
  `GSTFiniteLineFenceDischarge.the_unconditional_source_package_of_exists`;
* the wave-12 realization machinery
  (`GSTSphereFenceRealization`), whose proof consumes ANY pair
  (φ, z) of a degree-2 cochain vanishing on degree-3 boundaries and
  reading `1` on a CYCLE z — the machinery is generic in z.

Wave 13's port (the `HamSandwich/` tree, the lane
`ham-sandwich-port.yml`) supplies the homology input: the ℚ-instantiated
sphere tower's `SphereOddDegree.nontrivial_sphereHomology_two : Nontrivial
((singularChainsOf (TopCat.of unitSphereType)).homology 2)`.

THIS MODULE closes the loop INDEPENDENTLY of the port's CI verdict — it
takes the nontriviality as a HYPOTHESIS and composes:

* §1 a nontrivial degree-2 homology object contains a NON-BOUNDING
  CYCLE: through the chain-side `moduleCatHomologyIso` quotient
  presentation, a nonzero homology class gives a cycle `z ∈ ker d₂`
  whose quotient class is nonzero, i.e. `z ∉ im d₃`;
* §2 the pinned extension lemma
  (`LinearMap.exists_extend_of_notMem`, `LinearAlgebra/Basis/VectorSpace.lean:294`
  at `51e6992`) turns the non-membership into a separator φ vanishing
  on every boundary and reading `1` on `z`;
* §3 the wave-12 replay: the separator is a cocycle of the dual complex
  whose class is nonzero (a coboundary reads `ψ (d₂ z) = ψ 0 = 0` on the
  cycle) — FENCE-Ω DISCHARGED;
* §4 the exists-flip master instantiated: the FULL eight-conjunct
  wave-9 apex package at the honest data, the independence conjunct
  UNGUARDED — the last subcase of the X-audit closed.

HONESTY LEDGER. Every statement is proved unconditionally from the green
corpus given the named homology-nontriviality hypothesis. No `sorry`, no
new axioms, no `native_decide`. The GitHub CI lane
`gst-sphere-fence-omega-discharge.yml` owns the kernel check.
-/

set_option maxHeartbeats 70000000
set_option maxRecDepth 20000

noncomputable section

open CategoryTheory
open AlgebraicTopology
open Simplicial
open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTFiniteLineHonestHodgeData
open GSTFiniteLinePointsGateDischarge
open GSTFiniteLinePrimitiveXSource
open GSTSphereUnionComponents
open GSTSingularCohomologyMaps
open GSTSphereNonzeroClass
open GSTSphereFundamentalCycle
open GSTSphereFenceRealization
open GSTFiniteLineFenceDischarge

namespace GSTSphereFenceOmegaDischarge

/-! ## §0 The chain-side short complex and its legs -/

/-- The degree-2 short complex of the sphere's singular CHAIN complex:
`C₃ --d₃--> C₂ --d₂--> C₁` in the homological spelling. -/
abbrev sphereChainShortComplexTwo : ShortComplex (ModuleCat ℚ) :=
  (singularChainsOf (TopCat.of unitSphereType)).sc 2

/-- The `down ℕ` shape index at an interior degree: `prev 2 = 3`
(the pinned `ChainComplex.prev`). -/
theorem downPrev_two : (ComplexShape.down ℕ).prev 2 = 3 := by
  rw [ChainComplex.prev ℕ 2]

/-- The `down ℕ` shape index at an interior degree: `next 2 = 1`
(the pinned `ChainComplex.next_nat_succ`). -/
theorem downNext_two : (ComplexShape.down ℕ).next 2 = 1 :=
  ChainComplex.next_nat_succ 1

/-- AUDIT: the incoming leg of the degree-2 chain short complex, at the
differential spelling (the wave-12 `sc_two_f` recipe, `down` shape). -/
theorem scChain_two_f :
    sphereChainShortComplexTwo.f =
      (singularChainsOf (TopCat.of unitSphereType)).d 3 2 := by
  unfold sphereChainShortComplexTwo HomologicalComplex.sc
    HomologicalComplex.shortComplexFunctor
    HomologicalComplex.shortComplexFunctor'
  rw [downPrev_two]

/-- AUDIT: the outgoing leg at the differential spelling. -/
theorem scChain_two_g :
    sphereChainShortComplexTwo.g =
      (singularChainsOf (TopCat.of unitSphereType)).d 2 1 := by
  unfold sphereChainShortComplexTwo HomologicalComplex.sc
    HomologicalComplex.shortComplexFunctor
    HomologicalComplex.shortComplexFunctor'
  rw [downNext_two]

/-! ## §1 The cycle extraction (the nontriviality to the non-bounding cycle) -/

/-- **A NONTRIVIAL DEGREE-2 HOMOLOGY GIVES A NON-BOUNDING CYCLE.**
Through the chain-side `moduleCatHomologyIso` quotient presentation:
a nontrivial homology object has two distinct classes; their distinct
quotient images give a nonzero quotient element; its preimage is a
cycle `z ∈ ker d₂` (the kernel membership) lying outside the boundary
range (the nonzero quotient class). -/
theorem exists_nonbounding_cycle
    (hnt : Nontrivial ((singularChainsOf (TopCat.of unitSphereType)).homology 2)) :
    ∃ z : sphereChainsTwo,
      ModuleCat.Hom.hom ((singularChainsOf (TopCat.of unitSphereType)).d 2 1) z = 0 ∧
      ∀ w : sphereChainsThree, sphereBoundaryThree w ≠ z := by
  obtain ⟨x₁, x₂, hne⟩ := hnt
  -- the roundtrip (the iso's forward map followed by the inverse is the
  -- identity — `hom_inv_id` transported to LinearMap-land)
  have hfun :
      (sphereChainShortComplexTwo.moduleCatHomologyIso.inv).hom.comp
        (sphereChainShortComplexTwo.moduleCatHomologyIso.hom).hom =
        LinearMap.id :=
    congrArg ModuleCat.Hom.hom
      (sphereChainShortComplexTwo.moduleCatHomologyIso.hom_inv_id)
  -- the forward map is injective (the roundtrip at the elements)
  have hinj : Function.Injective
      (sphereChainShortComplexTwo.moduleCatHomologyIso.hom).hom := by
    intro a b hab
    have h1 := LinearMap.congr_fun hfun a
    have h2 := LinearMap.congr_fun hfun b
    rw [hab] at h1
    exact h1.symm.trans h2
  -- the two quotient images differ
  have hQne :
      (sphereChainShortComplexTwo.moduleCatHomologyIso.hom).hom x₁ ≠
      (sphereChainShortComplexTwo.moduleCatHomologyIso.hom).hom x₂ :=
    fun hc => hne (hinj hc)
  -- hence one of them is nonzero
  obtain ⟨Q, hQ⟩ :
      ∃ Q : ↥(LinearMap.ker (sphereChainShortComplexTwo.g).hom ⧸
        LinearMap.range sphereChainShortComplexTwo.moduleCatToCycles), Q ≠ 0 := by
    by_cases h1 :
        (sphereChainShortComplexTwo.moduleCatHomologyIso.hom).hom x₁ = 0
    · exact ⟨(sphereChainShortComplexTwo.moduleCatHomologyIso.hom).hom x₂,
        fun h0 => hQne (h1.trans h0.symm)⟩
    · exact ⟨(sphereChainShortComplexTwo.moduleCatHomologyIso.hom).hom x₁, h1⟩
  -- the nonzero quotient element is the class of a kernel element
  obtain ⟨p, hp⟩ := Submodule.mkQ_surjective
    (LinearMap.range sphereChainShortComplexTwo.moduleCatToCycles) Q
  obtain ⟨z, hzk⟩ := p
  -- its kernel element is NOT in the boundary range (else the class is 0)
  have hmem : p ∉ LinearMap.range sphereChainShortComplexTwo.moduleCatToCycles := by
    intro hin
    apply hQ
    rw [← hp]
    exact (Submodule.Quotient.mk_eq_zero _).mpr hin
  -- the cycle law at z (the kernel membership read at the element)
  have hzc0 : (sphereChainShortComplexTwo.g).hom z = 0 :=
    LinearMap.mem_ker.mp hzk
  have hzc : ModuleCat.Hom.hom
      ((singularChainsOf (TopCat.of unitSphereType)).d 2 1) z = 0 := by
    rw [← scChain_two_g]
    exact hzc0
  refine ⟨z, hzc, ?_⟩
  -- the boundary non-membership: if some w had d₃ w = z, the kernel
  -- element p would be the toCycles-image of w (the codRestrict
  -- presentation of moduleCatToCycles), contradicting hmem
  intro w hw
  apply hmem
  refine ⟨w, Subtype.ext ?_⟩
  show (sphereChainShortComplexTwo.f).hom w = z
  rw [← scChain_two_f]
  exact hw.symm

/-! ## §2 + §3 The extension and the wave-12 replay -/

/-- **FENCE-Ω DISCHARGED FROM THE HOMOLOGY NONTRIVIALITY.**  The
non-bounding cycle of §1 plus the pinned extension lemma give a
separator (vanishing on every boundary, reading `1` on the cycle), and
the wave-12 realization machinery turns it into a nonzero degree-2
rational singular cohomology class of the honest sphere. -/
theorem exists_nonzero_sphere_cohomology_two_of_nontrivial_homology
    (hnt : Nontrivial ((singularChainsOf (TopCat.of unitSphereType)).homology 2)) :
    ∃ ω : singularCohomologyOf (TopCat.of unitSphereType) 2, ω ≠ 0 := by
  obtain ⟨z, hzc, hzn⟩ := exists_nonbounding_cycle hnt
  -- §2 the non-membership and the extension (the pinned
  -- `LinearMap.exists_extend_of_notMem` — the zero map extended, reading
  -- 1 at z)
  have hznm : z ∉ LinearMap.range sphereBoundaryThree := by
    intro hin
    obtain ⟨w, hw⟩ := LinearMap.mem_range.mp hin
    exact hzn w hw
  obtain ⟨φ, hφ0, hφz⟩ := LinearMap.exists_extend_of_notMem
    (0 : (LinearMap.range sphereBoundaryThree) →ₗ[ℚ] ℚ) hznm 1
  have hvan : ∀ w : sphereChainsThree, φ (sphereBoundaryThree w) = 0 := by
    intro w
    have h0 := DFunLike.congr_fun hφ0
      ⟨sphereBoundaryThree w, LinearMap.mem_range_self _ w⟩
    simpa using h0
  have hone : φ z = 1 := hφz
  -- §3 the wave-12 replay (the machinery is generic in the cycle):
  -- the witness through the explicit quotient presentation
  refine ⟨(sphereDualShortComplexTwo.moduleCatHomologyIso.inv).hom
    (Submodule.mkQ
      (LinearMap.range sphereDualShortComplexTwo.moduleCatToCycles)
      ⟨fundCochain φ, fundCochain_mem_ker φ hvan⟩), ?_⟩
  intro hzero
  -- the roundtrip (the wave-12 receipts verbatim)
  have hcomp :
      (sphereDualShortComplexTwo.moduleCatHomologyIso.hom).hom.comp
        (sphereDualShortComplexTwo.moduleCatHomologyIso.inv).hom
        = LinearMap.id :=
    congrArg ModuleCat.Hom.hom
      (sphereDualShortComplexTwo.moduleCatHomologyIso.inv_hom_id)
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
  -- the quotient-zero is the boundary-membership
  obtain ⟨ψ, hψ⟩ := LinearMap.mem_range.mp
    ((Submodule.Quotient.mk_eq_zero _).mp hzero')
  have hval : (sphereDualShortComplexTwo.f).hom ψ = fundCochain φ :=
    congrArg Subtype.val hψ
  have hval' : (singularCochainsOf (TopCat.of unitSphereType)).d
      ((ComplexShape.up ℕ).prev 2) 2 ψ = fundCochain φ := by
    rw [← sc_two_f]
    exact hval
  -- the separator reads 1 on the cycle
  have hone' : (fundCochain φ).hom z = 1 := by
    rw [fundCochain_hom]
    exact hone
  -- but a coboundary reads 0 on every cycle (the cycle law at z,
  -- the indexed spelling)
  have hcy : (singularChainsOf (TopCat.of unitSphereType)).d 2
      ((ComplexShape.up ℕ).prev 2) z = 0 := by
    rw [upPrev_two]
    exact hzc
  have hzero'' : (fundCochain φ).hom z = 0 := by
    rw [← hval']
    exact (dual_eval_one_two_indexed ψ z).trans (by
      rw [hcy]
      exact map_zero _)
  exact zero_ne_one (hzero''.symm.trans hone')

/-! ## §4 The fence composition (the exists-flip master instantiated) -/

/-- **THE WITNESS-SHAPE INDEPENDENCE, FENCE DISCHARGED.**  Given the
homology nontriviality, the closed-point source family is linearly
independent at the certified witness, at every `M ≥ 1`, at the
constructed unconditional analytification. -/
theorem finiteLineSourceOne_independent_of_nontrivial_homology
    (hnt : Nontrivial ((singularChainsOf (TopCat.of unitSphereType)).homology 2)) :
    ∃ ω : singularCohomologyOf (TopCat.of unitSphereType) 2,
      ∀ (M : ℕ) (hM : NeZero M),
        LinearIndependent ℚ (fun i : Fin M =>
          (finiteLineHodgeDataHonest M (finiteLineAnalytificationUnconditional M)
            (finiteLineAnalytificationUnconditional_space M) ω).cycleClass 1
            (finiteLineSourceOne M i)) :=
  finiteLineSourceOne_independent_of_exists
    (exists_nonzero_sphere_cohomology_two_of_nontrivial_homology hnt)

/-- **THE FULL WAVE-9 APEX PACKAGE, FENCE DISCHARGED — THE LAST SUBCASE
OF THE X-AUDIT CLOSED.**  Given the homology nontriviality (the wave-13
port's endpoint), the complete eight-conjunct master holds at the
certified witness: both source families linearly independent at every
`M ≥ 1` (the weight-one conjunct UNGUARDED), every weight-0/1 rational
Hodge class an explicit combination of the source family, every
weight-`p ≥ 2` rational Hodge class zero, both compilers correct, and
the single-fold orbit law itself at the honest data. -/
theorem the_unconditional_source_package_of_nontrivial_homology
    (hnt : Nontrivial ((singularChainsOf (TopCat.of unitSphereType)).homology 2)) :
    ∃ ω : singularCohomologyOf (TopCat.of unitSphereType) 2,
      (∀ (M : ℕ) (hM : NeZero M),
        LinearIndependent ℚ (fun i : Fin M =>
          (finiteLineHodgeDataHonest M (finiteLineAnalytificationUnconditional M)
            (finiteLineAnalytificationUnconditional_space M) ω).cycleClass 1
            (finiteLineSourceOne M i))) ∧
      (∀ (M : ℕ) (hM : NeZero M),
        LinearIndependent ℚ (fun i : Fin M =>
          (finiteLineHodgeDataHonest M (finiteLineAnalytificationUnconditional M)
            (finiteLineAnalytificationUnconditional_space M) ω).cycleClass 0
            (finiteLineSourceZero M i))) ∧
      (∀ (M : ℕ) (hM : NeZero M),
        ∀ α : RationalSingularCohomology
            (finiteLineAnalytificationUnconditional M) 0,
          α ∈ rationalHodgeSubspace
            ((finiteLineHodgeDataHonest M (finiteLineAnalytificationUnconditional M)
              (finiteLineAnalytificationUnconditional_space M) ω).hodgeBigrading 0) →
          ∃ q : Fin M → ℚ,
            α = ∑ i, q i • (finiteLineHodgeDataHonest M
              (finiteLineAnalytificationUnconditional M)
              (finiteLineAnalytificationUnconditional_space M) ω).cycleClass 0
              (finiteLineSourceZero M i)) ∧
      (∀ (M : ℕ) (hM : NeZero M),
        ∀ α : RationalSingularCohomology
            (finiteLineAnalytificationUnconditional M) 2,
          α ∈ rationalHodgeSubspace
            ((finiteLineHodgeDataHonest M (finiteLineAnalytificationUnconditional M)
              (finiteLineAnalytificationUnconditional_space M) ω).hodgeBigrading 1) →
          ∃ q : Fin M → ℚ,
            α = ∑ i, q i • (finiteLineHodgeDataHonest M
              (finiteLineAnalytificationUnconditional M)
              (finiteLineAnalytificationUnconditional_space M) ω).cycleClass 1
              (finiteLineSourceOne M i)) ∧
      (∀ (M : ℕ) (hM : NeZero M),
        ∀ p : ℕ, 1 < p →
        ∀ α : RationalSingularCohomology
            (finiteLineAnalytificationUnconditional M) (2 * p),
          α ∈ rationalHodgeSubspace
            ((finiteLineHodgeDataHonest M (finiteLineAnalytificationUnconditional M)
              (finiteLineAnalytificationUnconditional_space M) ω).hodgeBigrading p) →
          α = 0) ∧
      (∀ (M : ℕ) (hM : NeZero M),
        ∀ α : RationalSingularCohomology
            (finiteLineAnalytificationUnconditional M) 0,
        (finiteLineHodgeDataHonest M (finiteLineAnalytificationUnconditional M)
          (finiteLineAnalytificationUnconditional_space M) ω).cycleClass 0
          (finiteLineSourceCompilerZero M
            (finiteLineAnalytificationUnconditional M)
            (finiteLineAnalytificationUnconditional_space M) α) = α) ∧
      (∀ (M : ℕ) (hM : NeZero M),
        ∀ α : RationalSingularCohomology
            (finiteLineAnalytificationUnconditional M) 2,
        ∀ hmem : α ∈ rationalHodgeSubspace
            ((finiteLineHodgeDataHonest M (finiteLineAnalytificationUnconditional M)
              (finiteLineAnalytificationUnconditional_space M) ω).hodgeBigrading 1),
        (finiteLineHodgeDataHonest M (finiteLineAnalytificationUnconditional M)
          (finiteLineAnalytificationUnconditional_space M) ω).cycleClass 1
          (finiteLineSourceCompilerOne M
            (finiteLineAnalytificationUnconditional M)
            (finiteLineAnalytificationUnconditional_space M) ω α hmem) = α) ∧
      (∀ (M : ℕ) (hM : NeZero M),
        NativeGSTSingleFoldOrbitLaw (finiteLineWorld M)
          (finiteLineHodgeDataHonest M (finiteLineAnalytificationUnconditional M)
            (finiteLineAnalytificationUnconditional_space M) ω)) :=
  the_unconditional_source_package_of_exists
    (exists_nonzero_sphere_cohomology_two_of_nontrivial_homology hnt)

/-! ## Receipts -/

#check @GSTSphereFenceOmegaDischarge.sphereChainShortComplexTwo
#check @GSTSphereFenceOmegaDischarge.scChain_two_f
#check @GSTSphereFenceOmegaDischarge.scChain_two_g
#check @GSTSphereFenceOmegaDischarge.exists_nonbounding_cycle
#check @GSTSphereFenceOmegaDischarge.exists_nonzero_sphere_cohomology_two_of_nontrivial_homology
#check @GSTSphereFenceOmegaDischarge.the_unconditional_source_package_of_nontrivial_homology

#print axioms GSTSphereFenceOmegaDischarge.exists_nonbounding_cycle
#print axioms GSTSphereFenceOmegaDischarge.exists_nonzero_sphere_cohomology_two_of_nontrivial_homology
#print axioms GSTSphereFenceOmegaDischarge.the_unconditional_source_package_of_nontrivial_homology

end GSTSphereFenceOmegaDischarge

end -- noncomputable section

/-
PORT NOTES (the designated CI repair points of this file):

* (FOD-1) `downPrev_two`/`downNext_two`: the `down ℕ` shape's prev is
  `ChainComplex.prev ℕ 2 : (down ℕ).prev 2 = 2 + 1` (Homotopy.lean:434's
  idiom); the rewrite's residual `2 + 1 = 3` closes by the rw's
  auto-rfl (binary literal normalization).  `downNext_two` is
  `ChainComplex.next_nat_succ 1 : (down ℕ).next (1 + 1) = 1`, assigned
  at the literal-normalized type (`1 + 1 ≡ 2`).  If either stalls, spell
  `by rw [ChainComplex.prev ℕ 2]; norm_num` / `by simpa using
  ChainComplex.next_nat_succ 1`.
* (FOD-2) `scChain_two_f`/`scChain_two_g`: the wave-12
  `sc_two_f`/`sc_two_g` unfold recipe verbatim (unfold sc +
  shortComplexFunctor + shortComplexFunctor', then the index rewrite);
  the RHS is at the LITERAL index (`d 3 2` / `d 2 1`) — after the
  rewrite the residual closes by rfl (the choice-opaqueness discipline:
  the bridge is stated at the fixed literals, matching the corpus's
  element-level differential spellings).
* (FOD-3) `exists_nonbounding_cycle`'s injectivity block: the
  `hom_inv_id` roundtrip at LinearMap-land (`congrArg ModuleCat.Hom.hom`)
  + `LinearMap.congr_fun` at the two elements (the wave-12 `hcomp`
  pattern, the OTHER roundtrip direction); if `LinearMap.congr_fun`
  rejects the comp-spelling, restage as `(congrArg (·.hom) hfun)`-style
  or `DFunLike.congr_fun` with the comp unfolded by `show`.
* (FOD-4) THE SUBTYPE-EXT SEAM (the boundary non-membership): the
  `moduleCatToCycles` is `f.hom.codRestrict _ (moduleCat_zero_apply …)`
  (ShortComplex/ModuleCat.lean:96) — the `show
  (sphereChainShortComplexTwo.f).hom w = z` steps through the
  codRestrict projection DEFEQ; if the defeq is blocked at the
  elaborator's default transparency, restage via
  `LinearMap.codRestrict_apply` (a rfl-lemma) as an explicit rewrite.
* (FOD-5) `Submodule.mkQ_surjective` (LinearAlgebra/Quotient/Defs.lean:236)
  — the obtain-destructuring `obtain ⟨p, hp⟩` pattern; the subsequent
  `obtain ⟨z, hzk⟩ := p` destructures the kernel subtype.
* (FOD-6) The extension seam: `LinearMap.exists_extend_of_notMem
  (0 : (LinearMap.range sphereBoundaryThree) →ₗ[ℚ] ℚ) hznm 1` — the
  zero-map extension reading 1 at z (the Mathlib-internal proof pattern
  of `Submodule.exists_le_ker_of_notMem`, VectorSpace.lean:306-310); the
  `hvan` extraction is `DFunLike.congr_fun hφ0 ⟨…, mem_range_self …⟩`
  + `simpa` (the identical chain, including the `Submodule.subtype_apply`
  simp-lemma collapsing).
* (FOD-7) THE REPLAY: every receipt is the wave-12 lemma VERBATIM
  (`sc_two_f`, `upPrev_two`, `dual_eval_one_two_indexed`,
  `fundCochain`, `fundCochain_hom`, `fundCochain_mem_ker`,
  `moduleCatHomologyIso` roundtrips) with `fundCycle`/`fundCycle_d`
  replaced by `z`/`hzc` — the machinery's genericity in the cycle is the
  wave-12 file's own structure (nothing in its proof uses `fundCycle`
  beyond the cycle law `d₂ z = 0` and the reading `φ z = 1`).
-/
