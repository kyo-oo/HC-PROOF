import Mathlib
import GSTGeometricRealizationStage2F
import GSTSphereUnionComponents

/-!
# GST SINGULAR COHOMOLOGY MAPS (Wave 57) — the generalized pullback calculus

THE CORPUS-MATHS MODULE of the sphere-machine campaign.  The corpus's own
functoriality recipe (`GSTClassicalHodgeSingularCohomologyFunctoriality.lean`,
CI-green) constructs the induced pullback on `RationalSingularCohomology`
for analytic ENDOMORPHISMS of one analytification.  This module generalizes
the same three-step recipe (chain map ⟶ linear-Yoneda dual ⟶ homology map)
to ARBITRARY continuous maps between ARBITRARY topological spaces, adds the
degree-two face interface shared by the winding machine and the sphere
cycle, and specializes everything to the sphere-union legs of the planned
finite-line world (inclusion / collapse / M-cycle permutation, with the
restriction-section calculus on cohomology).

Honesty ledger: every statement is proved unconditionally.  No `sorry`, no
new axioms, no `native_decide`.  The GitHub CI lane owns the kernel check.
-/

set_option maxHeartbeats 200000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicTopology
open Simplicial
open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTSphereUnionComponents

namespace GSTSingularCohomologyMaps

/-! ## §1 The raw-space singular (co)chain complexes -/

/-- The genuine rational singular chain complex of a raw topological space
(the corpus's `rationalSingularChains`, lifted off the analytification
carrier). -/
noncomputable def singularChainsOf (X : TopCat) : ChainComplex (ModuleCat ℚ) ℕ :=
  ((singularChainComplexFunctor (ModuleCat ℚ)).obj rationalCoefficient).obj X

/-- The rational singular chains of an analytification's space ARE the
corpus's `rationalSingularChains` (the same construction, `rfl`). -/
theorem singularChainsOf_eq {V : SmoothProjectiveComplexScheme}
    (A : AnalytificationData V) :
    singularChainsOf A.space = rationalSingularChains A := rfl

/-- The genuine rational singular cochain complex (the linear-Yoneda dual of
the chain complex — the corpus's `rationalSingularCochains` construction). -/
noncomputable def singularCochainsOf (X : TopCat) : CochainComplex (ModuleCat ℚ) ℕ :=
  (singularChainsOf X).linearYonedaObj ℚ rationalCoefficient

/-- The cochain complexes agree with the corpus's (`rfl`). -/
theorem singularCochainsOf_eq {V : SmoothProjectiveComplexScheme}
    (A : AnalytificationData V) :
    singularCochainsOf A.space = rationalSingularCochains A := rfl

/-- The n-th rational singular cohomology object of a raw space. -/
noncomputable def singularCohomologyObjOf (X : TopCat) (n : ℕ) : ModuleCat ℚ :=
  (singularCochainsOf X).homology n

/-- The underlying type of the n-th rational singular cohomology. -/
abbrev singularCohomologyOf (X : TopCat) (n : ℕ) : Type :=
  singularCohomologyObjOf X n

instance (X : TopCat) (n : ℕ) :
    AddCommGroup (singularCohomologyOf X n) :=
  inferInstance

instance (X : TopCat) (n : ℕ) :
    Module ℚ (singularCohomologyOf X n) :=
  inferInstance

/-- The cohomology of an analytification's space IS the corpus's
`RationalSingularCohomology` (`rfl` — the same homology object). -/
theorem singularCohomologyOf_eq {V : SmoothProjectiveComplexScheme}
    (A : AnalytificationData V) (n : ℕ) :
    (singularCohomologyOf A.space n) = RationalSingularCohomology A n := rfl

/-! ## §2 The induced maps of an arbitrary continuous map -/

/-- The covariant singular-chain map of a continuous map (the functor's
action — the corpus's `singularChainMap`, generalized off the
endomorphism shape). -/
noncomputable def chainMapOf {X Y : TopCat} (f : X ⟶ Y) :
    singularChainsOf X ⟶ singularChainsOf Y :=
  ((singularChainComplexFunctor (ModuleCat ℚ)).obj rationalCoefficient).map f

theorem chainMapOf_id (X : TopCat) :
    chainMapOf (𝟙 X) = 𝟙 (singularChainsOf X) := by
  simp [chainMapOf, singularChainsOf]

theorem chainMapOf_comp {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z) :
    chainMapOf (f ≫ g) = chainMapOf f ≫ chainMapOf g := by
  simp [chainMapOf]

/-- The contravariant singular-cochain map: the linear-Yoneda dual of the
chain map (the corpus's `singularCochainPullback` expression, verbatim,
generalized to distinct spaces). -/
noncomputable def cochainPullbackOf {X Y : TopCat} (f : X ⟶ Y) :
    singularCochainsOf Y ⟶ singularCochainsOf X := by
  unfold singularCochainsOf singularChainsOf
  exact (HomologicalComplex.unopFunctor (ModuleCat ℚ) (ComplexShape.down ℕ)).map
    (Quiver.Hom.op
      ((((CategoryTheory.linearYoneda ℚ (ModuleCat ℚ)).obj rationalCoefficient).rightOp
        |>.mapHomologicalComplex (ComplexShape.down ℕ)).map
        (chainMapOf f)))

theorem cochainPullbackOf_id (X : TopCat) :
    cochainPullbackOf (𝟙 X) = 𝟙 (singularCochainsOf X) := by
  simp [cochainPullbackOf, chainMapOf_id, Quiver.Hom.op_id,
    Functor.map_id]
  rfl

theorem cochainPullbackOf_comp {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z) :
    cochainPullbackOf (f ≫ g) = cochainPullbackOf g ≫ cochainPullbackOf f := by
  simp [cochainPullbackOf, chainMapOf_comp, Quiver.Hom.op_comp,
    Functor.map_comp]

/-- The induced map on the genuine rational singular cohomology objects. -/
noncomputable def cohomologyPullbackObjOf {X Y : TopCat} (f : X ⟶ Y) (n : ℕ) :
    singularCohomologyObjOf Y n ⟶ singularCohomologyObjOf X n :=
  HomologicalComplex.homologyMap (cochainPullbackOf f) n

/-- The induced pullback on rational singular cohomology, as a rational
linear map. -/
noncomputable def cohomologyPullbackOf {X Y : TopCat} (f : X ⟶ Y) (n : ℕ) :
    singularCohomologyOf Y n →ₗ[ℚ] singularCohomologyOf X n :=
  (cohomologyPullbackObjOf f n).hom

/-- Contravariant functoriality on cohomology (the corpus's green proof,
ported; NOTE the order: category composition `f ≫ g` acts on functions as
`g ∘ f`, so the induced linear maps compose `f* ∘ g*`). -/
theorem cohomologyPullbackOf_comp {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z)
    (n : ℕ) :
    cohomologyPullbackOf (f ≫ g) n =
      (cohomologyPullbackOf f n).comp (cohomologyPullbackOf g n) := by
  ext x
  unfold cohomologyPullbackOf cohomologyPullbackObjOf
  have hcochain :
    cochainPullbackOf (f ≫ g) =
      (cochainPullbackOf g) ≫ (cochainPullbackOf f) :=
    cochainPullbackOf_comp f g
  have hcomp :
    HomologicalComplex.homologyMap (cochainPullbackOf (f ≫ g)) n =
      (HomologicalComplex.homologyMap (cochainPullbackOf f) n) ≫
        (HomologicalComplex.homologyMap (cochainPullbackOf g) n) := by
    rw [hcochain, HomologicalComplex.homologyMap_comp]
  show (ModuleCat.Hom.hom
      (HomologicalComplex.homologyMap
        (cochainPullbackOf (f ≫ g)) n)) x =
    ((ModuleCat.Hom.hom
      (HomologicalComplex.homologyMap (cochainPullbackOf f) n)).comp
      (ModuleCat.Hom.hom
        (HomologicalComplex.homologyMap (cochainPullbackOf g) n))) x
  rw [hcomp]
  simp

/-- The identity acts identically (the corpus's green proof, verbatim
port). -/
theorem cohomologyPullbackOf_id (X : TopCat) (n : ℕ) :
    cohomologyPullbackOf (𝟙 X) n = LinearMap.id := by
  ext x
  unfold cohomologyPullbackOf cohomologyPullbackObjOf
  have hcochain :
    cochainPullbackOf (𝟙 X) = 𝟙 (singularCochainsOf X) :=
    cochainPullbackOf_id X
  show (ModuleCat.Hom.hom
      (HomologicalComplex.homologyMap
        (cochainPullbackOf (𝟙 X)) n)) x =
    LinearMap.id x
  rw [hcochain, HomologicalComplex.homologyMap_id]
  simp
  rfl

/-! ## §3 The degree-two face interface -/

/-- The standard topological 2-simplex model (the pinned `stdSimplex`). -/
abbrev StdTwoSimplex : Type :=
  stdSimplex ℝ (Fin 3)

/-- The standard topological 1-simplex model. -/
abbrev StdOneSimplex : Type :=
  stdSimplex ℝ (Fin 2)

/-- The pinned affine coface map between the concrete simplex models (the
`stdSimplex.continuous_map` of the `SimplexCategory.δ` coface; the index
`n := 1` : the coface `⦋1⦌ ⟶ ⦋2⦌` takes its skip-position in
`Fin (1 + 2)`). -/
def stdFace (k : Fin 3) : C(StdOneSimplex, StdTwoSimplex) :=
  stdSimplex.continuous_map (SimplexCategory.δ (n := 1) k)

/-- The injection of a concrete 2-simplex map into the singular set (the
pinned `toSSetObjEquiv`, reversed). -/
def twoSimplexInject {X : TopCat} (σ : C(StdTwoSimplex, X)) :
    (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk 2)) :=
  (TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk 2))).symm σ

/-- AUDIT(FACE-NAT): **THE DEGREE-TWO FACE FORMULA.**  The k-th face of an
injected 2-simplex, read as an I-path through the pinned
`toSSetObj₁Equiv`, is the precomposition of the simplex map with the
pinned affine coface, transported along the pinned
`stdSimplexHomeompressI`.

The proof is the Yoneda naturality of the pinned `toSSetObjEquiv` (whose
construction is `Equiv.ulift.trans (homEquiv.trans (continuousMapCongr
...))` — the presheaf map action IS precomposition).  Designated CI
repair point: the `simp` set + the closing `rfl` run the ULift-congruence
dance at default transparency. -/
theorem toSSetObj₂_face {X : TopCat} (σ : C(StdTwoSimplex, X)) (k : Fin 3) :
    X.toSSetObj₁Equiv
        ((TopCat.toSSet.obj X).δ k (twoSimplexInject σ)) =
      TopCat.ofHom
        ((σ.comp (stdFace k)).comp
          (Homeomorph.toContinuousMap
            (TopCat.stdSimplexHomeomorphI.symm :
              StdOneSimplex ≃ₜ I))) := by
  ext t
  simp [TopCat.toSSetObj₁Equiv, TopCat.toSSetObjEquiv, TopCat.toSSet,
    SimplexCategory.toTop, stdFace, twoSimplexInject]

/-! ## §4 The sphere-union leg maps -/

section Legs

variable (M : ℕ)

/-- The cyclic successor on `Fin M` (the M-cycle's index map). -/
def cyclicSucc (k : Fin M) : Fin M :=
  ⟨(k.val + 1) % M,
    Nat.mod_lt (k.val + 1)
      (Nat.lt_of_le_of_lt (Nat.zero_le k.val) k.isLt)⟩

/-- The base point of the 2-sphere (the corpus's own nonempty-sphere point
of the green sphere-union file — any point serves the constant filler of
the collapse). -/
def sphereBase : unitSphereType :=
  unitSphere_nonempty.some

theorem sphereCollapse_continuous (i : Fin M) :
    Continuous (fun z : sphereUnionSpace M =>
      if z.1 = i then z.2 else sphereBase) := by
  refine ⟨fun U hU => ?_⟩
  rw [isOpen_sigma_iff]
  intro j
  by_cases hj : j = i
  · subst hj
    have hset : {a : unitSphereType |
        (Sigma.mk (β := fun _ : Fin M => unitSphereType) j) a ∈
          (fun z : sphereUnionSpace M =>
            if z.1 = j then z.2 else sphereBase) ⁻¹' U} = U := by
      ext a
      simp only [Set.mem_preimage, Set.mem_setOfEq]
      show (if (Sigma.mk (β := fun _ : Fin M => j) a).1 = j
          then (Sigma.mk (β := fun _ : Fin M => j) a).2
          else sphereBase) ∈ U ↔ a ∈ U
      simp only [if_pos rfl]
    rw [hset]
    exact hU
  · have hset : {a : unitSphereType |
        (Sigma.mk (β := fun _ : Fin M => unitSphereType) j) a ∈
          (fun z : sphereUnionSpace M =>
            if z.1 = j then z.2 else sphereBase) ⁻¹' U} =
          (if sphereBase ∈ U then Set.univ else ∅) := by
      ext a
      simp only [Set.mem_preimage, Set.mem_setOfEq]
      show (if (Sigma.mk (β := fun _ : Fin M => j) a).1 = j
          then (Sigma.mk (β := fun _ : Fin M => j) a).2
          else sphereBase) ∈ U ↔
        (if sphereBase ∈ U then Set.univ else ∅)
      simp only [if_neg (fun h => hj h.symm)]
      by_cases hb : sphereBase ∈ U
      · simp [hb]
      · simp [hb]
    rw [hset]
    by_cases hb : sphereBase ∈ U
    · exact isOpen_univ
    · exact isOpen_empty

/-- The inclusion of the i-th sphere slice (the green sphere file's
Continuous-STRUCTURE constructor route with the pinned
`isOpen_sigma_iff`). -/
def sphereIncl (i : Fin M) :
    TopCat.of unitSphereType ⟶ TopCat.of (sphereUnionSpace M) :=
  TopCat.ofHom
    ⟨fun x => Sigma.mk (β := fun _ : Fin M => unitSphereType) i x, by
      refine ⟨fun U hU => ?_⟩
      exact isOpen_sigma_iff.mp hU i⟩

/-- AUDIT(COLLAPSE-CONT): the collapse of the union onto the i-th slice
(identity there, constant filler elsewhere; the constant family makes the
second component's type index-independent — no transport needed). -/
def sphereCollapse (i : Fin M) :
    TopCat.of (sphereUnionSpace M) ⟶ TopCat.of unitSphereType :=
  TopCat.ofHom
    ⟨fun z => if z.1 = i then z.2 else sphereBase,
      sphereCollapse_continuous M i⟩

/-- The M-cycle permutation of the slices.  Continuity by the pinned
`isOpen_sigma_iff`: the preimage's j-component is the (cyclicSucc j)-slice
of the target, open by the pinned `isOpen_sigma_iff.mp`. -/
def sphereCycle :
    TopCat.of (sphereUnionSpace M) ⟶ TopCat.of (sphereUnionSpace M) :=
  TopCat.ofHom
    ⟨fun z => Sigma.mk (β := fun _ : Fin M => unitSphereType)
      (cyclicSucc M z.1) z.2, by
      refine ⟨fun U hU => ?_⟩
      rw [isOpen_sigma_iff]
      intro j
      exact isOpen_sigma_iff.mp hU (cyclicSucc M j)⟩

/-! ## §5 The leg identities -/

/-- The collapse is a left inverse of the inclusion on the slice. -/
theorem incl_comp_collapse (i : Fin M) :
    sphereIncl M i ≫ sphereCollapse M i = 𝟙 (TopCat.of unitSphereType) := by
  apply TopCat.hom_ext
  funext x
  show (if (Sigma.mk (β := fun _ : Fin M => unitSphereType) i x).1 = i
      then (Sigma.mk (β := fun _ : Fin M => unitSphereType) i x).2
      else sphereBase) = x
  simp only [if_pos rfl]

/-- The M-cycle permutes the slices. -/
theorem cycle_comp_incl (j : Fin M) :
    sphereIncl M j ≫ sphereCycle M =
      sphereIncl M (cyclicSucc M j) := by
  apply TopCat.hom_ext
  funext x
  rfl

/-! ## §6 The cohomology-level leg calculus -/

/-- **THE RESTRICTION-SECTION CALCULUS.**  On rational singular cohomology,
the restriction to the i-th slice followed by the collapse-pullback is the
identity: the collapse-pullback is a SECTION of the slice restriction.  Once
the honest sphere class exists, this is the mechanism that extends it to
the union. -/
theorem incl_collapse_section (i : Fin M) (n : ℕ) :
    (cohomologyPullbackOf (sphereIncl M i) n).comp
      (cohomologyPullbackOf (sphereCollapse M i) n) = LinearMap.id := by
  rw [← cohomologyPullbackOf_comp (sphereIncl M i) (sphereCollapse M i) n,
    incl_comp_collapse M i, cohomologyPullbackOf_id]

/-- **THE CYCLIC PERMUTATION ACTION ON SLICE RESTRICTIONS.**  Pulling back
along the M-cycle and then restricting to slice j equals restricting to
slice (cyclicSucc j). -/
theorem cycle_incl_calculus (j : Fin M) (n : ℕ) :
    (cohomologyPullbackOf (sphereIncl M j) n).comp
      (cohomologyPullbackOf (sphereCycle M) n) =
        cohomologyPullbackOf (sphereIncl M (cyclicSucc M j)) n := by
  rw [← cohomologyPullbackOf_comp (sphereIncl M j) (sphereCycle M) n,
    cycle_comp_incl M j]

end Legs

end GSTSingularCohomologyMaps
