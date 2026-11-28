import HamSandwich.SphereOddDegree.AlgebraicTopology.Backports.PrismSimplicialHomotopy
import Mathlib

/-!
# Rational singular homology: the ℚ specialization layer

The vendored HamSandwich machine (`SphereOddDegree`) computes the top singular
homology of spheres at **integer** coefficients: every homotopy-invariance,
augmentation and tower ingredient is phrased through `singularChainℤ` /
`singularHomologyℤ` (`ModuleCat.{0} ℤ`, coefficient object `ModuleCat.of ℤ ℤ`).
The FENCE-Ω discharge of the GST campaign instead needs the **rational**
statement, in the corpus spelling `singularChainsOf` — i.e. the chain complex
`((singularChainComplexFunctor (ModuleCat ℚ)).obj rationalCoefficient).obj X`
with `rationalCoefficient = ModuleCat.of ℚ ℚ`.

This file is the first step of the ℚ *duplication route* (no vendored file is
modified): it re-derives, at `ℚ`, the small specialization layer that the
integral files hardwire:

* the chain/homology functor abbreviations `singularChainQ` / `singularHomologyQ`
  (mirroring `singularChainℤ` / `singularHomologyℤ` of
  `HomotopyToChainHomotopy.lean`);
* their functoriality wrappers (`singularHomologyQ_map_id`, `_map_comp`);
* the chain-homotopy consumer `singularHomologyQ_map_eq_of_singularChainHomotopy`
  (mirroring `singularHomologyMap_eq_of_singularChainHomotopy`);
* unconditional homotopy invariance at ℚ in all three interfaces, via the
  **coefficient-generic prism operator** `singularChainHomotopyOfHomotopyModule`
  (the vendored `Backports/PrismSimplicialHomotopy.lean` already provides the
  `[CommRing R]`-general version — only the ℤ wrapper
  `singularChainHomotopyOfHomotopy` was used downstream);
* the homotopy-equivalence homology isomorphism
  `singularHomologyQ_isoOfHomotopyEquivSpace` (mirroring
  `singularHomologyℤ_isoOfHomotopyEquivSpace` of `BallBoundaryLES.lean`);
* contractible vanishing `isZero_singularHomologyQ_of_contractibleSpace`
  (mirroring `isZero_singularHomologyℤ_of_contractibleSpace`), which rests on
  Mathlib's coefficient-category-generic
  `isZero_singularHomologyFunctor_of_totallyDisconnectedSpace`.

Everything is Type-0 (`TopCat.{0}`, `ModuleCat.{0}`), as in the vendored files.
-/

open CategoryTheory AlgebraicTopology

noncomputable section

namespace SphereOddDegree

/-! ## The rational chain / homology functors -/

/-- The rational singular chain complex functor `TopCat ⥤ ChainComplex
(ModuleCat ℚ) ℕ`, i.e. `singularChainComplexFunctor` specialised to coefficients
`ℚ` — the ℚ mirror of `singularChainℤ`.  Definitionally the same construction
as the corpus's `GSTSingularCohomologyMaps.singularChainsOf`. -/
noncomputable abbrev singularChainQ :
    TopCat.{0} ⥤ ChainComplex (ModuleCat.{0} ℚ) ℕ :=
  (singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)

/-- The `n`-th rational singular homology functor `TopCat ⥤ ModuleCat ℚ`, i.e.
`singularHomologyFunctor` specialised to coefficients `ℚ` — the ℚ mirror of
`singularHomologyℤ`. -/
noncomputable abbrev singularHomologyQ (n : ℕ) :
    TopCat.{0} ⥤ ModuleCat.{0} ℚ :=
  (singularHomologyFunctor (ModuleCat.{0} ℚ) n).obj (ModuleCat.of ℚ ℚ)

/-! ## Functoriality wrappers (mirroring `SingularHomologyFunctorAPI.lean`) -/

/-- Functoriality: the rational singular homology functor preserves identities. -/
@[simp]
theorem singularHomologyQ_map_id (X : TopCat.{0}) (n : ℕ) :
    (singularHomologyQ n).map (𝟙 X) = 𝟙 _ :=
  (singularHomologyQ n).map_id X

/-- Functoriality: the rational singular homology functor preserves
composition. -/
theorem singularHomologyQ_map_comp {X Y Z : TopCat.{0}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    (singularHomologyQ n).map (f ≫ g)
      = (singularHomologyQ n).map f ≫ (singularHomologyQ n).map g :=
  (singularHomologyQ n).map_comp f g

/-! ## The chain-homotopy consumer (mirroring `HomotopyToChainHomotopy.lean`) -/

/-- **Reduction lemma at ℚ.** If the rational singular chain maps induced by two
continuous maps `f, g : X ⟶ Y` are chain-homotopic, then the induced maps on the
`n`-th rational singular homology are equal.  (Mirror of
`singularHomologyMap_eq_of_singularChainHomotopy`.) -/
theorem singularHomologyQ_map_eq_of_singularChainHomotopy
    {X Y : TopCat.{0}} {f g : X ⟶ Y}
    (H : Homotopy
      (((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)).map f)
      (((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)).map g))
    (n : ℕ) :
    (singularHomologyQ n).map f = (singularHomologyQ n).map g := by
  have h := H.homologyMap_eq n
  simpa [singularHomologyQ, singularHomologyFunctor,
    HomologicalComplex.homologyFunctor_map] using h

/-! ## Homotopy invariance at ℚ (unconditional) -/

/-- **Homotopy invariance of rational singular homology (`TopCat` form).**
A topological homotopy between `f, g : X ⟶ Y` induces equal maps on the `n`-th
rational singular homology.  Proved via the coefficient-generic prism operator
`singularChainHomotopyOfHomotopyModule` instantiated at `ℚ`. -/
theorem singularHomologyQ_map_eq_of_homotopy
    {X Y : TopCat.{0}} {f g : X ⟶ Y}
    (H : ContinuousMap.Homotopy f.hom g.hom) (n : ℕ) :
    (singularHomologyQ n).map f = (singularHomologyQ n).map g :=
  singularHomologyQ_map_eq_of_singularChainHomotopy
    (singularChainHomotopyOfHomotopyModule ℚ (ModuleCat.of ℚ ℚ) H) n

/-- **Homotopy invariance of rational singular homology (`Homotopic` form).**
Homotopic `TopCat` maps induce equal maps on rational singular homology. -/
theorem singularHomologyQ_map_eq_of_homotopic
    {X Y : TopCat.{0}} {f g : X ⟶ Y}
    (h : ContinuousMap.Homotopic f.hom g.hom) (n : ℕ) :
    (singularHomologyQ n).map f = (singularHomologyQ n).map g := by
  obtain ⟨H⟩ := h
  exact singularHomologyQ_map_eq_of_homotopy H n

/-- **Homotopy invariance of rational singular homology (`C(X, Y)` form).**
Homotopic continuous maps induce equal maps on rational singular homology
(after the canonical `TopCat.ofHom`). -/
theorem singularHomologyQ_map_eq_of_homotopic_continuousMap
    {X Y : TopCat.{0}} {f g : C(X, Y)} (h : ContinuousMap.Homotopic f g) (n : ℕ) :
    (singularHomologyQ n).map (TopCat.ofHom f)
      = (singularHomologyQ n).map (TopCat.ofHom g) :=
  singularHomologyQ_map_eq_of_homotopic h n

/-! ## Homotopy equivalences -/

/-- **Rational homology iso from a homotopy equivalence.** A homotopy
equivalence `e : X ≃ₕ Y` of topological spaces induces an isomorphism on the
`k`-th rational singular homology.  (Mirror of
`singularHomologyℤ_isoOfHomotopyEquivSpace` of `BallBoundaryLES.lean`.) -/
noncomputable def singularHomologyQ_isoOfHomotopyEquivSpace (k : ℕ)
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) :
    (singularHomologyQ k).obj (TopCat.of X) ≅ (singularHomologyQ k).obj (TopCat.of Y) where
  hom := (singularHomologyQ k).map (TopCat.ofHom e.toFun)
  inv := (singularHomologyQ k).map (TopCat.ofHom e.invFun)
  hom_inv_id := by
    rw [← singularHomologyQ_map_comp]
    have key := singularHomologyQ_map_eq_of_homotopic_continuousMap
      (X := TopCat.of X) (Y := TopCat.of X)
      (f := e.invFun.comp e.toFun) (g := ContinuousMap.id X) e.left_inv k
    have h : TopCat.ofHom e.toFun ≫ TopCat.ofHom e.invFun
        = TopCat.ofHom (e.invFun.comp e.toFun) := rfl
    rw [h, key]
    simp
  inv_hom_id := by
    rw [← singularHomologyQ_map_comp]
    have key := singularHomologyQ_map_eq_of_homotopic_continuousMap
      (X := TopCat.of Y) (Y := TopCat.of Y)
      (f := e.toFun.comp e.invFun) (g := ContinuousMap.id Y) e.right_inv k
    have h : TopCat.ofHom e.invFun ≫ TopCat.ofHom e.toFun
        = TopCat.ofHom (e.toFun.comp e.invFun) := rfl
    rw [h, key]
    simp

/-! ## Contractible spaces have vanishing positive rational homology -/

/-- **Vanishing of positive rational homology for contractible spaces.** If `X`
is contractible and `k ≥ 1`, then `Hₖ(X; ℚ) = 0`: `X` is homotopy equivalent to
a point, whose higher homology vanishes (the point is totally disconnected, via
Mathlib's coefficient-generic
`isZero_singularHomologyFunctor_of_totallyDisconnectedSpace`).  (Mirror of
`isZero_singularHomologyℤ_of_contractibleSpace`.) -/
theorem isZero_singularHomologyQ_of_contractibleSpace (k : ℕ) (hk : 1 ≤ k)
    (X : Type) [TopologicalSpace X] [ContractibleSpace X] :
    IsZero ((singularHomologyQ k).obj (TopCat.of X)) := by
  obtain ⟨e⟩ := ContractibleSpace.hequiv_unit X
  apply IsZero.of_iso _ (singularHomologyQ_isoOfHomotopyEquivSpace k e)
  exact isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
    (ModuleCat.{0} ℚ) k (ModuleCat.of ℚ ℚ) (TopCat.of Unit) (by omega)

end SphereOddDegree

/-! ## PORT NOTES (the commander's CI-repair map)

Seams adapted in this file (ℚ duplication of the ℤ specialization layer):

1. `singularChainℤ` / `singularHomologyℤ` (HomotopyToChainHomotopy.lean) →
   `singularChainQ` / `singularHomologyQ` at `ModuleCat.{0} ℚ` with coefficient
   object `ModuleCat.of ℚ ℚ`.
2. Homotopy invariance: the vendored ℤ chain routes through
   `SingularPrismOperator` → `singularChainHomotopyOfHomotopy` (ℤ-only).  The
   vendored backport file already provides the `[CommRing R]`-generic
   `singularChainHomotopyOfHomotopyModule R Mod`; we instantiate it at
   `ℚ / ModuleCat.of ℚ ℚ` and feed it to the ℚ consumer
   `singularHomologyQ_map_eq_of_singularChainHomotopy` (verbatim mirror of the
   ℤ consumer's `simpa` proof, with the hypothesis stated in the raw
   `singularChainComplexFunctor` form so the backport's output applies by
   `rfl`-defeq).
3. `isZero_singularHomologyFunctor_of_totallyDisconnectedSpace`
   (Mathlib.AlgebraicTopology.SingularHomology.Basic) is coefficient-category
   generic at the pin `(C) (n) (R) (X) (hn)`; instantiated at
   `ModuleCat ℚ / ModuleCat.of ℚ ℚ` exactly as the ℤ file does at ℤ.
4. `Functor.map_comp` at the pin is the structure projection, applied via
   dot-notation `(singularHomologyQ n).map_comp f g` — same shape as the
   vendored `singularHomologyℤ_map_comp` wrapper.
-/
