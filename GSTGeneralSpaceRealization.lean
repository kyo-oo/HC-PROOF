import GSTGeneralSpaceRecoordination

/-!
# GST GENERAL SPACE — realizations

A realization is one face of a General Space.  Coordinates, graph packets,
cohomology states, native cycles, and Hodge data are all realizations; none of
them is identified with the ontology itself.
-/

universe u v w z

namespace GSTGeneralSpaceRealization

open GSTGeneralSpace
open GSTGeneralSpaceTransport

/-- A possibly lossy face/observation of General Space points. -/
structure Realization (G : GeneralSpace.{u,v}) where
  State : Type w
  realize : G.Point → State

namespace Realization

/-- A chart is a realization whose state type is its coordinate type. -/
def ofChart {G : GeneralSpace.{u,v}} (C : Chart.{w} G) : Realization.{w} G where
  State := C.Coord
  realize := C.observe

/-- Faithfulness of a realization means no two General Space points collapse
under this face.  It is never required globally. -/
def Faithful {G : GeneralSpace.{u,v}} (R : Realization.{w} G) : Prop :=
  Function.Injective R.realize

end Realization

/-- A natural map between two transported realizations over the same General
Space.  This is the abstract synchronization square used later by native and
Betti faces. -/
structure TransportMorphism {G : GeneralSpace.{u,v}}
    (A : TransportSystem.{w} G) (B : TransportSystem.{z} G) where
  map : (x : G.Point) → A.Fiber x → B.Fiber x
  naturality : ∀ {x y : G.Point} (γ : G.Path x y) (a : A.Fiber x),
    map y (A.transport γ a) = B.transport γ (map x a)

namespace TransportMorphism

/-- Identity transport morphism. -/
def id {G : GeneralSpace.{u,v}} (A : TransportSystem.{w} G) :
    TransportMorphism A A where
  map := fun _ a => a
  naturality := by intros; rfl

/-- Natural transport maps compose. -/
def comp {G : GeneralSpace.{u,v}}
    {A : TransportSystem.{w} G}
    {B : TransportSystem.{z} G}
    {C : TransportSystem.{u} G}
    (f : TransportMorphism A B) (g : TransportMorphism B C) :
    TransportMorphism A C where
  map := fun x a => g.map x (f.map x a)
  naturality := by
    intro x y γ a
    rw [f.naturality γ a, g.naturality γ (f.map x a)]

end TransportMorphism

#check Realization
#check Realization.ofChart
#check TransportMorphism
#check TransportMorphism.id
#check TransportMorphism.comp

#print axioms TransportMorphism.id
#print axioms TransportMorphism.comp

end GSTGeneralSpaceRealization
