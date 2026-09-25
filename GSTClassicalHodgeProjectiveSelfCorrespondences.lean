import GSTClassicalHodgeAnalytificationFunctoriality
import GSTProjectiveOverC
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-!
# GST CLASSICAL HODGE — GENUINE PROJECTIVE SELF-CORRESPONDENCES

The multiplicity operators used by the internal GST universe must eventually
be realized by genuine algebraic geometry, not by arbitrary basis read/write
maps.  The correct geometric carrier is the self-product

  X ×_{Spec C} X.

Every smooth projective complex carrier in this repository already comes with
a closed immersion into an actual Mathlib `Proj`.  Hence it is separated over
`Spec C`.  Its diagonal and the graph of every C-scheme endomorphism are
therefore genuine closed immersions into the self-product.

This module constructs those objects and proves their projection identities.
No Hodge class, cycle-class surjectivity, or coordinate-basis assumption occurs
here.
-/

set_option maxHeartbeats 20000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open GSTProjectiveOverC
open GSTClassicalHodgeAnalytificationFunctoriality

namespace GSTClassicalHodgeProjectiveSelfCorrespondences

attribute [local instance] MvPolynomial.gradedAlgebra

variable (V : SmoothProjectiveComplexScheme)

/-- Actual algebraic self-product over the complex base. -/
abbrev selfProduct : Scheme :=
  pullback V.structureMap V.structureMap

/-- First projection of the self-product. -/
abbrev fst : selfProduct V ⟶ V.X :=
  pullback.fst V.structureMap V.structureMap

/-- Second projection of the self-product. -/
abbrev snd : selfProduct V ⟶ V.X :=
  pullback.snd V.structureMap V.structureMap

/-- The two projections agree after composition to `Spec C`. -/
theorem fst_toBase_eq_snd_toBase :
    fst V ≫ V.structureMap = snd V ≫ V.structureMap :=
  pullback.condition

/-- Algebraic diagonal of the projective carrier. -/
noncomputable def diagonal : V.X ⟶ selfProduct V :=
  pullback.lift (𝟙 V.X) (𝟙 V.X) (by simp)

@[simp, reassoc]
theorem diagonal_fst :
    diagonal V ≫ fst V = 𝟙 V.X := by
  simp [diagonal, fst]

@[simp, reassoc]
theorem diagonal_snd :
    diagonal V ≫ snd V = 𝟙 V.X := by
  simp [diagonal, snd]

/-- Graph of a genuine C-scheme endomorphism inside the self-product. -/
noncomputable def graph
    (f : ComplexSchemeEndomorphism V) :
    V.X ⟶ selfProduct V :=
  pullback.lift (𝟙 V.X) f.hom (by
    rw [Category.id_comp, f.over_base])

@[simp, reassoc]
theorem graph_fst
    (f : ComplexSchemeEndomorphism V) :
    graph V f ≫ fst V = 𝟙 V.X := by
  simp [graph, fst]

@[simp, reassoc]
theorem graph_snd
    (f : ComplexSchemeEndomorphism V) :
    graph V f ≫ snd V = f.hom := by
  simp [graph, snd]

/-- The diagonal is the graph of the identity endomorphism. -/
theorem graph_id :
    graph V (ComplexSchemeEndomorphism.id V) = diagonal V := by
  apply pullback.hom_ext <;> simp [graph, diagonal]

/-- Projective space over C is separated. -/
local instance projectiveSpace_separated (n : Nat) :
    IsSeparated (projectiveSpaceToBase n) := by
  unfold projectiveSpaceToBase
  infer_instance

/-- Every smooth projective complex carrier in the repository is separated
over the complex base, derived from its closed projective embedding. -/
instance smoothProjective_isSeparated : IsSeparated V.structureMap := by
  rw [← V.projective.over_base]
  infer_instance

/-- The algebraic diagonal is a genuine closed immersion. -/
instance diagonal_isClosedImmersion : IsClosedImmersion (diagonal V) := by
  dsimp [diagonal]
  infer_instance

/-- Every algebraic graph over C is a genuine closed immersion into the
projective self-product. -/
instance graph_isClosedImmersion
    (f : ComplexSchemeEndomorphism V) :
    IsClosedImmersion (graph V f) := by
  dsimp [graph]
  infer_instance

/-- Universal characterization of the graph by its two projections. -/
theorem graph_unique
    (f : ComplexSchemeEndomorphism V)
    (g : V.X ⟶ selfProduct V)
    (hfst : g ≫ fst V = 𝟙 V.X)
    (hsnd : g ≫ snd V = f.hom) :
    g = graph V f := by
  apply pullback.hom_ext
  · simpa [hfst] using hfst
  · simpa [hsnd] using hsnd

/-- Self-correspondence geometry crown. -/
theorem projective_self_correspondence_crown :
    IsClosedImmersion (diagonal V)
    ∧ (∀ f : ComplexSchemeEndomorphism V,
      IsClosedImmersion (graph V f))
    ∧ (∀ f : ComplexSchemeEndomorphism V,
      graph V f ≫ fst V = 𝟙 V.X
      ∧ graph V f ≫ snd V = f.hom) := by
  refine ⟨inferInstance, fun f => inferInstance, ?_⟩
  intro f
  exact ⟨graph_fst V f, graph_snd V f⟩

#check selfProduct
#check fst
#check snd
#check diagonal
#check graph
#check graph_fst
#check graph_snd
#check graph_id
#check graph_isClosedImmersion
#check projective_self_correspondence_crown

#print axioms graph_fst
#print axioms graph_snd
#print axioms graph_id
#print axioms projective_self_correspondence_crown

end GSTClassicalHodgeProjectiveSelfCorrespondences
