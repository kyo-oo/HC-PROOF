import HamSandwich.SphereOddDegree.AlgebraicTopology.SingularH0
import HamSandwich.SphereOddDegree.AlgebraicTopology.SingularH0PathConnected
import HamSandwich.SphereOddDegree.AlgebraicTopology.SubChainSubspaceBridgeQ
import Mathlib

/-!
# Rational zeroth homology of path-connected spaces, via the augmentation

The ℚ duplication of the vendored augmentation layer
(`SingularH0.lean` + `SingularH0PathConnected.lean`), which is ℤ-hardwired:
it builds the augmentation `ε : C₀(X; ℤ) → ℤ` (sum of coefficients) and proves
`H₀(X; ℤ) ≅ ℤ` for nonempty path-connected spaces, plus the subspace variant
`subH0aug` and its naturality — the ingredients of the Mayer–Vietoris base case
`H₁(S¹) ≅ ℤ`.

This file mirrors every ingredient at rational coefficients:

* `augQ` / `augQ_generator` / `augQ_boundary` — the augmentation at `ℚ`;
* `boundary_pathSimplexQ`, `chainGenerator_sub_mem_range_of_pathQ`,
  `chainGenerator_sub_mem_rangeQ`, `sub_augQ_smul_basept_mem_range` — the
  geometric input (points joined by a path differ by a boundary);
* `H0augQ`, `H0augQ_natural`, `isIso_H0augQ`, `surjective_H0augQ` — the
  descended augmentation on `H₀(–; ℚ)` and its isomorphism property;
* `subH0augQ`, `isIso_subH0augQ`, `subChainCorestrict_inclusion_squareQ`,
  `subH0augQ_natural_inclusion` — the subspace variant and its naturality.

The carrier-level ingredients (`pointSimplex`, `pathSimplex`, `prev_zero`,
`setInclusionTopCat`) are coefficient-free and are *reused* from the vendored
files.  The ℤ proofs carry over verbatim with `ℤ → ℚ`, with one genuine
simplification: the `AddSubgroup`-closure detour of
`sub_aug_smul_basept_mem_range` (dodging the ℤ-module instance diamond
`Submodule.module` vs `AddCommGroup.toIntModule` on `↥(ker _)`) is unnecessary
at the field `ℚ` — a plain `Submodule.span ℚ` induction works.
-/

set_option maxHeartbeats 4000000

open CategoryTheory AlgebraicTopology Limits
open SphereOddDegree.AffineBarycentricSubdivision

noncomputable section
namespace SphereOddDegree

variable {X : TopCat.{0}}

/-! ## The boundary of a path simplex at ℚ -/

/-- The boundary of the path `1`-simplex is the difference of its endpoint
`0`-simplices, at rational coefficients.  (Mirror of `boundary_pathSimplex`.) -/
theorem boundary_pathSimplexQ {a b : X} (p : Path a b) :
    (singularBoundary ℚ X 0).hom (chainGenerator ℚ X 1 (pathSimplex p))
      = chainGenerator ℚ X 0 (pointSimplex X b) - chainGenerator ℚ X 0 (pointSimplex X a) := by
  simp +decide [ singularBoundary_chainGenerator_formula ];
  rw [ show AlexanderWhitney.faceSimplex X 0 0 ( pathSimplex p ) = pointSimplex X b from ?_, show AlexanderWhitney.faceSimplex X 0 1 ( pathSimplex p ) = pointSimplex X a from ?_ ] ; abel1;
  · apply singularSimplices_ext;
    ext x;
    convert congr_arg ( fun x => ( p.toContinuousMap.comp ( stdSimplexHomeomorphUnitInterval ) ) x ) ( show ( cofaceTop 0 1 x ) = ( ⟨ _, single_mem_stdSimplex ℝ 0 ⟩ : Delta 1 ) from ?_ ) using 1;
    · convert p.source.symm using 1;
    · convert delta0_subsingleton x ( stdSimplex.vertex 0 );
      constructor <;> intro h <;> simp_all +decide [ cofaceTop ];
      convert delta0_subsingleton x ( stdSimplex.vertex 0 );
  · apply singularSimplices_ext;
    ext x;
    convert congr_arg p ( stdSimplexHomeomorphUnitInterval_one ) using 1;
    · convert congr_arg p ( show stdSimplexHomeomorphUnitInterval ( cofaceTop 0 0 x ) = 1 from ?_ ) using 1;
      convert stdSimplexHomeomorphUnitInterval_one using 1;
      congr;
      ext i; fin_cases i ; simp +decide [ cofaceTop ] ;
      · simp +decide [ FunOnFinite.linearMap ];
        simp +decide [ Finsupp.mapDomain ];
      · simp +decide [ cofaceTop ];
        simp +decide [ FunOnFinite.linearMap ];
        simp +decide [ Finsupp.mapDomain, Finsupp.linearEquivFunOnFinite ];
        simp +decide [ Finsupp.sum_fintype, Finsupp.single_apply ];
    · convert p.target.symm using 1

/-- For points joined by a path, the difference of the corresponding `0`-simplex
generators is a boundary, at rational coefficients. -/
theorem chainGenerator_sub_mem_range_of_pathQ {a b : X} (p : Path a b) :
    chainGenerator ℚ X 0 (pointSimplex X b) - chainGenerator ℚ X 0 (pointSimplex X a)
      ∈ LinearMap.range (singularBoundary ℚ X 0).hom :=
  ⟨chainGenerator ℚ X 1 (pathSimplex p), boundary_pathSimplexQ p⟩

/-- For points in the same (path-)connected space, the difference of their
`0`-simplex generators is a boundary, at rational coefficients. -/
theorem chainGenerator_sub_mem_rangeQ [PathConnectedSpace X] (σ τ : singularSimplices X 0) :
    chainGenerator ℚ X 0 σ - chainGenerator ℚ X 0 τ
      ∈ LinearMap.range (singularBoundary ℚ X 0).hom := by
        have h_simplices : ∃ a b : X, σ = pointSimplex X a ∧ τ = pointSimplex X b := by
          refine' ⟨ _, _, _, _ ⟩;
          exact ( singularSimplexAsContinuousMap X 0 σ ) ( stdSimplex.vertex 0 );
          exact ( singularSimplexAsContinuousMap X 0 τ ) ( stdSimplex.vertex 0 );
          · apply singularSimplices_ext;
            ext x;
            convert congr_arg ( fun y => ( singularSimplexAsContinuousMap X 0 σ ) y ) ( delta0_subsingleton x ( stdSimplex.vertex 0 ) ) using 1;
          · apply singularSimplices_ext;
            exact ContinuousMap.ext fun x => by rw [ show x = stdSimplex.vertex 0 from delta0_subsingleton _ _ ] ; rfl;
        obtain ⟨ a, b, rfl, rfl ⟩ := h_simplices;
        have := chainGenerator_sub_mem_range_of_pathQ ( PathConnectedSpace.somePath b a ) ; aesop;

/-! ## The rational augmentation -/

/-- The augmentation `ε : C₀(X; ℚ) → ℚ` summing the coefficients (each `0`-simplex
generator maps to `1`).  (Mirror of `aug`.) -/
noncomputable def augQ (X : TopCat.{0}) : singularChainGroup ℚ X 0 ⟶ ModuleCat.of ℚ ℚ :=
  Limits.Sigma.desc (fun _ => 𝟙 (ModuleCat.of ℚ ℚ))

/-- The rational augmentation reads `1` on each `0`-simplex generator. -/
@[simp] theorem augQ_generator (σ : singularSimplices X 0) :
    (augQ X).hom (chainGenerator ℚ X 0 σ) = 1 := by
      convert congr_arg ( fun f : ModuleCat.of ℚ ℚ ⟶ ModuleCat.of ℚ ℚ => ( ModuleCat.Hom.hom f ) 1 ) ( show ( Limits.Sigma.ι ( fun _ => ModuleCat.of ℚ ℚ ) σ ≫ Limits.Sigma.desc ( fun _ => 𝟙 ( ModuleCat.of ℚ ℚ ) ) : ModuleCat.of ℚ ℚ ⟶ ModuleCat.of ℚ ℚ ) = 𝟙 ( ModuleCat.of ℚ ℚ ) from ?_ ) using 1;
      simp +decide [ CategoryTheory.Limits.colimit.ι_desc ]

/-- The rational augmentation vanishes on boundaries. -/
theorem augQ_boundary (c : singularChainGroup ℚ X 1) :
    (augQ X).hom ((singularBoundary ℚ X 0).hom c) = 0 := by
      refine' Submodule.span_induction _ _ _ _ ( show c ∈ Submodule.span ℚ ( Set.range ( fun τ : singularSimplices X 1 => chainGenerator ℚ X 1 τ ) ) from _ );
      · exact Submodule.mem_sInf.mpr (by
        intro p hp;
        convert p.span_le.mpr hp ( show c ∈ Submodule.span ℚ ( Set.range fun τ : singularSimplices X 1 => chainGenerator ℚ X 1 τ ) from ?_ ) using 1;
        convert Submodule.mem_top;
        grind +suggestions);
      · intro x hx
        obtain ⟨τ, rfl⟩ := hx
        have h_sum : (augQ X).hom ((singularBoundary ℚ X 0).hom (chainGenerator ℚ X 1 τ)) = 0 := by
          rw [ singularBoundary_chainGenerator_formula ] ; simp +decide [ Fin.sum_univ_two ] ;
          rw [ augQ_generator, augQ_generator ] ; norm_num
        exact h_sum;
      · aesop;
      · aesop;
      · simp +contextual [ map_smul ]

/-- Every rational `0`-chain is, modulo boundaries, `ε(c)` copies of a fixed
basepoint `0`-simplex.  (At the field `ℚ` a plain `Submodule.span ℚ` induction
suffices — the ℤ original had to detour through `AddSubgroup.closure` because of
the ℤ-module instance diamond, which does not exist over `ℚ`.) -/
theorem sub_augQ_smul_basept_mem_range [PathConnectedSpace X] (b : X)
    (c : singularChainGroup ℚ X 0) :
    c - (augQ X).hom c • chainGenerator ℚ X 0 (pointSimplex X b)
      ∈ LinearMap.range (singularBoundary ℚ X 0).hom := by
  have hc : c ∈ Submodule.span ℚ (Set.range (chainGenerator ℚ X 0)) := by
    rw [chainGenerator_span_top]; exact Submodule.mem_top
  induction hc using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨σ, rfl⟩ := hy
      rw [augQ_generator, one_smul]
      exact chainGenerator_sub_mem_rangeQ σ (pointSimplex X b)
  | zero => simp
  | add x y _ _ hx hy =>
      have h : x + y - (augQ X).hom (x + y) • chainGenerator ℚ X 0 (pointSimplex X b)
          = (x - (augQ X).hom x • chainGenerator ℚ X 0 (pointSimplex X b))
            + (y - (augQ X).hom y • chainGenerator ℚ X 0 (pointSimplex X b)) := by
        rw [map_add, add_smul]; abel
      rw [h]; exact Submodule.add_mem _ hx hy
  | smul r a _ ha =>
      have h : r • a - (augQ X).hom (r • a) • chainGenerator ℚ X 0 (pointSimplex X b)
          = r • (a - (augQ X).hom a • chainGenerator ℚ X 0 (pointSimplex X b)) := by
        rw [map_smul, smul_smul, smul_sub]
      rw [h]; exact Submodule.smul_mem _ _ ha

/-! ## The augmentation on rational homology -/

/-- The rational chain-level augmentation kills the differential `∂₁`. -/
theorem augQ_comp_boundary_eq_zero (Y : TopCat.{0}) :
    (singularChainComplex ℚ Y).d 1 0 ≫ augQ Y = 0 := by
  ext c; simp [augQ_boundary];
  convert augQ_boundary c using 1

/-- The augmentation descends to degree-0 rational homology
`H₀(Y; ℚ) → ℚ`.  (Mirror of `H0aug`.) -/
def H0augQ (Y : TopCat.{0}) : (singularChainComplex ℚ Y).homology 0 ⟶ ModuleCat.of ℚ ℚ :=
  (singularChainComplex ℚ Y).homologyι 0 ≫
    (singularChainComplex ℚ Y).descOpcycles (augQ Y) 1 prev_zero (augQ_comp_boundary_eq_zero Y)

/-- **Naturality of the rational augmentation.** For a continuous map
`f : Y ⟶ Z`, the augmentation commutes with the induced map on `H₀(–; ℚ)`. -/
theorem H0augQ_natural {Y Z : TopCat.{0}} (f : Y ⟶ Z) :
    (singularHomologyQ 0).map f ≫ H0augQ Z = H0augQ Y := by
  unfold H0augQ;
  have h_comm : (singularChainQ.map f).f 0 ≫ augQ Z = augQ Y := by
    simp +decide [ CategoryTheory.Category.assoc, singularChainQ, singularChainComplexFunctor, augQ ];
    simp +decide [ CategoryTheory.Functor.map, SSet.singularChainComplexFunctor ];
    ext; simp +decide [ CategoryTheory.Functor.map, SSet.singularChainComplexFunctor ] ;
  simp +decide [ ← h_comm, ← CategoryTheory.Category.assoc, HomologicalComplex.homologyι, HomologicalComplex.descOpcycles ];
  simp +decide [ HomologicalComplex.sc, HomologicalComplex.homologyι ];
  erw [ CategoryTheory.ShortComplex.homologyι_naturality_assoc ];
  simp +decide [ HomologicalComplex.shortComplexFunctor, HomologicalComplex.descOpcycles ]

/-- `homologyι` at degree `0` of a rational singular chain complex is an
isomorphism (no outgoing differential at the bottom). -/
instance isIso_homologyι_zeroQ (Y : TopCat.{0}) :
    IsIso ((singularChainComplex ℚ Y).homologyι 0) :=
  HomologicalComplex.isIso_homologyι (singularChainComplex ℚ Y) 0 ((ComplexShape.down ℕ).next 0)
    rfl ((singularChainComplex ℚ Y).shape _ _ (by simp [ComplexShape.next]))

/-- The augmentation factored through the opcycles is an isomorphism, for a
nonempty path-connected space, at rational coefficients. -/
theorem isIso_descOpcycles_augQ (Y : TopCat.{0}) [Nonempty Y] [PathConnectedSpace Y] :
    IsIso ((singularChainComplex ℚ Y).descOpcycles (augQ Y) 1 prev_zero
      (augQ_comp_boundary_eq_zero Y)) := by
  have h_bijective : Function.Bijective (HomologicalComplex.descOpcycles (singularChainComplex ℚ Y) (augQ Y) 1 prev_zero (by simp [augQ_comp_boundary_eq_zero])).hom := by
    constructor;
    · intro x y hxy
      obtain ⟨c, hc⟩ : ∃ c : singularChainGroup ℚ Y 0, (singularChainComplex ℚ Y).pOpcycles 0 c = x := by
        exact ( ModuleCat.epi_iff_surjective _ ).mp ( by infer_instance ) x
      obtain ⟨d, hd⟩ : ∃ d : singularChainGroup ℚ Y 0, (singularChainComplex ℚ Y).pOpcycles 0 d = y := by
        have := ( ModuleCat.epi_iff_surjective ( HomologicalComplex.pOpcycles ( singularChainComplex ℚ Y ) 0 ) );
        exact this.mp ( by infer_instance ) y
      have h_eq : (augQ Y).hom c = (augQ Y).hom d := by
        have h_eq : (HomologicalComplex.descOpcycles (singularChainComplex ℚ Y) (augQ Y) 1 prev_zero (by simp [augQ_comp_boundary_eq_zero])).hom ((singularChainComplex ℚ Y).pOpcycles 0 c) = (augQ Y).hom c ∧ (HomologicalComplex.descOpcycles (singularChainComplex ℚ Y) (augQ Y) 1 prev_zero (by simp [augQ_comp_boundary_eq_zero])).hom ((singularChainComplex ℚ Y).pOpcycles 0 d) = (augQ Y).hom d := by
          exact ⟨ by exact congr_arg ( fun f => f c ) ( HomologicalComplex.p_descOpcycles ( singularChainComplex ℚ Y ) ( augQ Y ) 1 prev_zero ( by simp [ augQ_comp_boundary_eq_zero ] ) ), by exact congr_arg ( fun f => f d ) ( HomologicalComplex.p_descOpcycles ( singularChainComplex ℚ Y ) ( augQ Y ) 1 prev_zero ( by simp [ augQ_comp_boundary_eq_zero ] ) ) ⟩;
        grind +splitIndPred
      have h_diff : c - d ∈ LinearMap.range (singularBoundary ℚ Y 0).hom := by
        convert sub_augQ_smul_basept_mem_range ( Classical.arbitrary Y ) ( c - d ) using 1 ; simp +decide [ h_eq ]
      have h_zero : (singularChainComplex ℚ Y).pOpcycles 0 c = (singularChainComplex ℚ Y).pOpcycles 0 d := by
        obtain ⟨ e, he ⟩ := h_diff;
        have h_zero : (singularChainComplex ℚ Y).pOpcycles 0 c - (singularChainComplex ℚ Y).pOpcycles 0 d = 0 := by
          convert congr_arg ( fun x => ( singularChainComplex ℚ Y ).pOpcycles 0 x ) he.symm using 1;
          · grind;
          · simp +decide [ ← CategoryTheory.comp_apply, singularBoundary ];
        exact eq_of_sub_eq_zero h_zero
      simp_all +decide [ Function.Injective ];
    · intro n
      obtain ⟨b⟩ : ∃ b : Y, True := by
        exact ⟨ Classical.arbitrary _, trivial ⟩
      use (singularChainComplex ℚ Y).pOpcycles 0 (n • chainGenerator ℚ Y 0 (pointSimplex Y b));
      have := HomologicalComplex.p_descOpcycles ( singularChainComplex ℚ Y ) ( augQ Y ) 1 prev_zero ( by simp +decide [ augQ_comp_boundary_eq_zero ] );
      convert congr_arg ( fun f => f ( n • chainGenerator ℚ Y 0 ( pointSimplex Y b ) ) ) this using 1 ; simp +decide [ augQ_generator ];
      erw [ augQ_generator ] ; aesop;
  convert ( ConcreteCategory.isIso_iff_bijective _ ).mpr h_bijective

/-- **The rational augmentation is an isomorphism on `H₀` of a nonempty
path-connected space.** -/
instance isIso_H0augQ (Y : TopCat.{0}) [Nonempty Y] [PathConnectedSpace Y] :
    IsIso (H0augQ Y) := by
  have := isIso_descOpcycles_augQ Y
  unfold H0augQ
  infer_instance

/-- The augmentation on rational `H₀` is surjective for any nonempty space. -/
theorem surjective_H0augQ (Y : TopCat.{0}) [Nonempty Y] :
    Function.Surjective (H0augQ Y).hom := by
  have h_surjective : Function.Surjective (⇑(ModuleCat.Hom.hom ((singularChainComplex ℚ Y).descOpcycles (augQ Y) 1 prev_zero (augQ_comp_boundary_eq_zero Y)))) := by
    intro n
    obtain ⟨b⟩ := ‹Nonempty Y›
    use (singularChainComplex ℚ Y).pOpcycles 0 (n • chainGenerator ℚ Y 0 (pointSimplex Y b));
    convert congr_arg ( fun f => f ( n • chainGenerator ℚ Y 0 ( pointSimplex Y b ) ) ) ( HomologicalComplex.p_descOpcycles ( singularChainComplex ℚ Y ) ( augQ Y ) 1 prev_zero ( by simp +decide [ augQ_comp_boundary_eq_zero ] ) ) using 1 ; simp +decide [ augQ_generator ];
    erw [ augQ_generator ] ; aesop;
  convert h_surjective.comp ( show Function.Surjective ⇑ ( ModuleCat.Hom.hom ( ( singularChainComplex ℚ Y ).homologyι 0 ) ) from ?_ ) using 1;
  exact Function.Surjective.of_comp ( show Function.Surjective ⇑ ( ModuleCat.Hom.hom ( ( singularChainComplex ℚ Y ).homologyι 0 ) ) from by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact by simpa using ( ConcreteCategory.isIso_iff_bijective _ ) |>.1 ( by exact inferInstance ) |>.2 ) ) ) ) ) ) ) ) ) ) ) ) )

/-! ## The subspace augmentation at ℚ -/

/-- The augmentation on the degree-0 rational homology of the subordinate-chain
complex of a subspace `S ⊆ X`, transported via the rational subspace bridge.
(Mirror of `subH0aug`.) -/
def subH0augQ (X : TopCat.{0}) (S : Set X) :
    (subChainComplex ℚ X S).homology 0 ⟶ ModuleCat.of ℚ ℚ :=
  (subspaceHomologyIsoQ X S 0).hom ≫ H0augQ (TopCat.of S)

/-- `subH0augQ` is an isomorphism for a nonempty path-connected subspace. -/
theorem isIso_subH0augQ (X : TopCat.{0}) (S : Set X) [Nonempty S] [PathConnectedSpace S] :
    IsIso (subH0augQ X S) := by
  -- Apply the fact that the composition of isomorphisms is an isomorphism.
  apply CategoryTheory.IsIso.comp_isIso

/-- **Chain-level naturality square for the corestriction bridge under
inclusion, at ℚ.**  (Mirror of `subChainCorestrict_inclusion_square`.) -/
theorem subChainCorestrict_inclusion_squareQ (X : TopCat.{0}) (S T : Set X) (h : S ⊆ T) :
    subChainCorestrict ℚ X S ≫ subChainInclusion S T h
      = singularChainQ.map (setInclusionTopCat X S T h) ≫ subChainCorestrict ℚ X T := by
  ext n;
  convert Subtype.ext ?_;
  convert congr_arg ( fun f => f ‹_› ) ( singularChainMap_comp ℚ ( setInclusionTopCat X S T h ) ( sInclusion T ) n ) using 1

/-- **Naturality of the rational subspace augmentation under inclusion
`S ⊆ T`.**  (Mirror of `subH0aug_natural_inclusion`.) -/
theorem subH0augQ_natural_inclusion (X : TopCat.{0}) (S T : Set X) (h : S ⊆ T) :
    HomologicalComplex.homologyMap (subChainInclusion S T h) 0 ≫ subH0augQ X T
      = subH0augQ X S := by
  convert congr_arg _ ( H0augQ_natural ( setInclusionTopCat X S T h ) ) using 1;
  unfold subH0augQ;
  simp +decide [ subspaceHomologyIsoQ, singularHomologyQ ];
  simp +decide [ subspaceHomologyIso, singularHomologyFunctor ];
  simp +decide [ ← CategoryTheory.Category.assoc, ← HomologicalComplex.homologyMap_comp, subChainCorestrict_inclusion_squareQ ];
  rw [ show subChainInclusion S T h ≫ inv ( subChainCorestrict ℚ X T ) = inv ( subChainCorestrict ℚ X S ) ≫ ( ( singularChainComplexFunctor ( ModuleCat ℚ ) ).obj ( ModuleCat.of ℚ ℚ ) ).map ( setInclusionTopCat X S T h ) from ?_ ];
  rw [ ← CategoryTheory.cancel_epi ( subChainCorestrict ℚ X S ), ← CategoryTheory.cancel_mono ( subChainCorestrict ℚ X T ) ];
  simp +decide [ CategoryTheory.Category.assoc, subChainCorestrict_inclusion_squareQ ]

end SphereOddDegree

/-! ## PORT NOTES (the commander's CI-repair map)

Seams adapted in this file (ℚ duplication of the augmentation layer):

1. **Declaration order.** The vendored `SingularH0PathConnected.lean` defines
   `aug_comp_boundary_eq_zero` *before* `H0aug` (which consumes it); the same
   order is kept here (`augQ_comp_boundary_eq_zero` before `H0augQ`).
2. `aug`/`H0aug`/`subH0aug` → `augQ`/`H0augQ`/`subH0augQ` with
   `singularChainComplex ℚ`, `singularBoundary ℚ`, `chainGenerator ℚ`,
   `ModuleCat.of ℚ ℚ`, `Submodule.span ℚ`; the proofs are verbatim mirrors.
3. `sub_augQ_smul_basept_mem_range` is **not** a verbatim mirror: the ℤ original
   detours through `AddSubgroup.closure` to dodge the ℤ-module instance diamond
   (`Submodule.module` vs `AddCommGroup.toIntModule`), which is ℤ-specific.  Over
   the field `ℚ` the diamond does not exist, so a plain
   `Submodule.span ℚ` induction (`map_add`/`add_smul`/`map_smul`/`smul_smul`/
   `smul_sub`) is used.  Repair point if the `smul` case's `rw [map_smul,
   smul_smul, smul_sub]` misses: replace the `have h :=` derivation by
   `rw [map_smul]; module`.
4. `subspaceHomologyIsoℤ` → `subspaceHomologyIsoQ` (SubChainSubspaceBridgeQ);
   `singularChainℤ.map` → `singularChainQ.map` in
   `subChainCorestrict_inclusion_squareQ`; `singularChainMap_comp` is
   `[CommRing R]`-generic in the vendored
   `BarycentricSubdivisionHomotopyFormula.lean` and is instantiated at `ℚ`.
5. Reused (coefficient-free) vendored carriers: `pointSimplex`, `pathSimplex`,
   `prev_zero`, `setInclusionTopCat`, `chainGenerator_span_top`,
   `singularSimplices_ext`, `AlexanderWhitney.faceSimplex`,
   `singularBoundary_chainGenerator_formula` (the latter two `[CommRing R]`-
   generic), `HomologicalComplex.descOpcycles`/`p_descOpcycles` (Mathlib).
6. `grind +splitIndPred`, `grind +suggestions`, `aesop`, `simp +decide` calls
   are copied verbatim from the CI-green ℤ file; `DecidableEq ℚ` is available at
   the pin, so the `+decide` fragments evaluate as they do at `ℤ`.
-/
