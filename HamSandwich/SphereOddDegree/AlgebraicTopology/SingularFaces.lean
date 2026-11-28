import Mathlib

/-
Copyright (c) 2026. The HC-PROOF campaign. All rights reserved.
Ported from akopjan/HamSandwich @ 76202db (Apache-2.0) — the cup-product
incision of the wave-13 trim: the four declarations the subdivision
machine actually consumes, extracted from the deleted cup-product /
Alexander-Whitney files (CupProduct.lean: `singularSimplices`;
AlexanderWhitneyChainMap.lean: `singularChainSimplicialModule` and its
generator lemma; AlexanderWhitneyFaceMaps.lean: `faceSimplex`), verbatim,
under their original namespaces so every downstream reference resolves
unchanged.  The deleted files' remaining content (the cup product, the
Alexander-Whitney chain maps, the tensor signs) is dead weight for the
sphere-homology spine and carried two v4.28→v4.33 migration breaks
(the `Multiplicative ℕ` `TensorSigns.ε'` field; the `MonoidHom.mk'`
index monoid).
-/

open CategoryTheory MonoidalCategory AlgebraicTopology Simplicial SimplexCategory

namespace SphereOddDegree

/-! ## 0. Singular simplices and the simplicial module of chains -/

/-- The set of singular `n`-simplices of a space `Z` (an element of the singular
simplicial set in degree `n`). -/
abbrev singularSimplices (Z : TopCat.{0}) (n : ℕ) :=
  (TopCat.toSSet.obj Z).obj (Opposite.op (SimplexCategory.mk n))

/-! ## 1. The underlying simplicial module of the singular chain complex -/

/-- The free `R`-module simplicial object whose alternating face map complex is
the singular chain complex `C_•(Z; R)`. Its value in degree `n` is the coproduct
`∐_{σ : n-simplex} R`. -/
noncomputable def singularChainSimplicialModule (R : Type) [CommRing R] (Z : TopCat.{0}) :
    SimplicialObject (ModuleCat.{0} R) :=
  ((Limits.sigmaConst ⋙ SimplicialObject.whiskering (Type 0) (ModuleCat.{0} R)).obj
    (ModuleCat.of R R)).obj (TopCat.toSSet.obj Z)

/-- A morphism in `SimplexCategoryᵒᵖ` acts on the singular chain simplicial module
by sending a basis generator to the basis generator at the restricted simplex. -/
theorem singularChainSimplicialModule_map_generator (R : Type) [CommRing R] (X : TopCat.{0})
    (m m' : ℕ) (g : (Opposite.op (⦋m'⦌ : SimplexCategory)) ⟶ Opposite.op ⦋m⦌)
    (σ : singularSimplices X m') :
    ((singularChainSimplicialModule R X).map g).hom
      ((Limits.Sigma.ι (fun (_ : singularSimplices X m') => ModuleCat.of R R) σ).hom (1 : R))
    = (Limits.Sigma.ι (fun (_ : singularSimplices X m) => ModuleCat.of R R)
        ((TopCat.toSSet.obj X).map g σ)).hom (1 : R) := by
  have key : (Limits.Sigma.ι (fun (_ : singularSimplices X m') => ModuleCat.of R R) σ)
      ≫ (singularChainSimplicialModule R X).map g
      = Limits.Sigma.ι (fun (_ : singularSimplices X m) => ModuleCat.of R R)
        ((TopCat.toSSet.obj X).map g σ) := by
    simp [singularChainSimplicialModule, SimplicialObject.whiskering, Limits.sigmaConst]
  have := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom key) (1 : R)
  simpa [ModuleCat.hom_comp, LinearMap.comp_apply] using this

/-! ## 2. The boundary-face extraction (the Alexander-Whitney namespace) -/

namespace AlexanderWhitney

/-- The **`k`-th boundary face** of a singular `(n+1)`-simplex `σ`, obtained by
restricting `σ` along `SimplexCategory.δ k`. -/
noncomputable def faceSimplex (X : TopCat.{0}) (n : ℕ) (k : Fin (n + 2))
    (σ : (TopCat.toSSet.obj X).obj (Opposite.op (⦋n + 1⦌ : SimplexCategory))) :
    (TopCat.toSSet.obj X).obj (Opposite.op (⦋n⦌ : SimplexCategory)) :=
  (TopCat.toSSet.obj X).map (SimplexCategory.δ k).op σ

end AlexanderWhitney

end SphereOddDegree
