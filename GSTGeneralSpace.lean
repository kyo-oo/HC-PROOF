import Mathlib

/-!
# GST GENERAL SPACE — carrier-independent ontology

Coordinates do not define a General Space.  The primitive data are an
arbitrary universe-polymorphic carrier of points and typed paths between
points.  Dimension, metric, topology, arithmetic coordinates, Hodge labels,
and every other geometry live in independent capability/realization layers.
-/

universe u v w

namespace GSTGeneralSpace

/-- Primitive General Space ontology.  No dimension, coordinate system,
metric, Euclidean law, finiteness, or arithmetic carrier is built in. -/
structure GeneralSpace where
  Point : Type u
  Path : Point → Point → Type v
  idPath : (x : Point) → Path x x
  compPath : {x y z : Point} → Path x y → Path y z → Path x z

/-- Optional categorical laws for a General Space path calculus.  Keeping this
separate from `GeneralSpace` allows raw syntax/path programs to be General
Spaces even when associativity only holds after semantic interpretation. -/
structure LawfulPaths (G : GeneralSpace.{u,v}) : Prop where
  id_comp : ∀ {x y : G.Point} (γ : G.Path x y),
    G.compPath (G.idPath x) γ = γ
  comp_id : ∀ {x y : G.Point} (γ : G.Path x y),
    G.compPath γ (G.idPath y) = γ
  assoc : ∀ {w x y z : G.Point}
      (γ₁ : G.Path w x) (γ₂ : G.Path x y) (γ₃ : G.Path y z),
    G.compPath (G.compPath γ₁ γ₂) γ₃ =
      G.compPath γ₁ (G.compPath γ₂ γ₃)

/-- A coordinate presentation/observation of one General Space. -/
structure Chart (G : GeneralSpace.{u,v}) where
  Coord : Type w
  observe : G.Point → Coord

namespace Chart

/-- A chart is globally faithful when its coordinate observation is injective.
Faithfulness is optional; most GST charts are deliberately partial/coarse. -/
def Faithful {G : GeneralSpace.{u,v}} (C : Chart.{w} G) : Prop :=
  Function.Injective C.observe

end Chart

/-- Incidence is an optional geometry capability, not part of the ontology. -/
structure IncidenceGeometry (G : GeneralSpace.{u,v}) where
  Incidence : G.Point → G.Point → Prop

/-- A completely generic grading capability.  The grade carrier itself need
not be numeric, finite, ordered, or dimensional. -/
structure GradedGeometry (G : GeneralSpace.{u,v}) where
  Grade : Type w
  grade : G.Point → Grade

/-- Causal/admissibility relation independent of coordinates and metric. -/
structure CausalGeometry (G : GeneralSpace.{u,v}) where
  Causal : G.Point → G.Point → Prop

/-- Spectral/observable capability.  The observable value type is arbitrary. -/
structure SpectralGeometry (G : GeneralSpace.{u,v}) where
  Spectrum : Type w
  spectrum : G.Point → Spectrum

/-- Every ordinary type is a discrete General Space. -/
def discrete (α : Type u) : GeneralSpace.{u,u} where
  Point := α
  Path := fun x y => x = y
  idPath := fun _ => rfl
  compPath := fun h₁ h₂ => h₁.trans h₂

/-- Discrete paths satisfy the categorical laws exactly. -/
theorem discrete_lawful (α : Type u) : LawfulPaths (discrete α) := by
  constructor
  · intro x y γ
    cases γ
    rfl
  · intro x y γ
    cases γ
    rfl
  · intro w x y z γ₁ γ₂ γ₃
    cases γ₁
    cases γ₂
    cases γ₃
    rfl

/-- Any preorder is one concrete path realization: a path is a reachability
proof `x ≤ y`.  This is an adapter, not a restriction on General Space. -/
def ofPreorder (α : Type u) [Preorder α] : GeneralSpace.{u,u} where
  Point := α
  Path := fun x y => x ≤ y
  idPath := fun _ => le_rfl
  compPath := fun h₁ h₂ => h₁.trans h₂

/-- Preorder-path realizations are lawful by proof irrelevance. -/
theorem ofPreorder_lawful (α : Type u) [Preorder α] :
    LawfulPaths (ofPreorder α) := by
  constructor <;> intros <;> apply Subsingleton.elim

/-- Dimensionless means exactly that the ontology can be instantiated on an
arbitrary carrier without manufacturing any dimension datum. -/
theorem carrier_is_unconstrained (α : Type u) :
    (discrete α).Point = α := rfl

#check GeneralSpace
#check LawfulPaths
#check Chart
#check IncidenceGeometry
#check GradedGeometry
#check CausalGeometry
#check SpectralGeometry
#check discrete
#check ofPreorder

#print axioms discrete_lawful
#print axioms ofPreorder_lawful

end GSTGeneralSpace
