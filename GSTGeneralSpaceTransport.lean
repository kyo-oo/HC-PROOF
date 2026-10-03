import GSTGeneralSpace

/-!
# GST GENERAL SPACE — transport geometry

A General Space path becomes geometric only after a state system says how the
path transports states.  Fibers may vary with the point, so this covers graph
states, graded cycle groups, cohomology groups in different degrees, and other
non-coordinate geometries.
-/

universe u v w

namespace GSTGeneralSpaceTransport

open GSTGeneralSpace

/-- Functorial transport of a dependent family of states along General Space
paths.  The semantic action is required to respect identity and composition
even when the raw path syntax itself is not definitionally associative. -/
structure TransportSystem (G : GeneralSpace.{u,v}) where
  Fiber : G.Point → Type w
  transport : {x y : G.Point} → G.Path x y → Fiber x → Fiber y
  transport_id : ∀ (x : G.Point) (a : Fiber x),
    transport (G.idPath x) a = a
  transport_comp : ∀ {x y z : G.Point}
      (γ₁ : G.Path x y) (γ₂ : G.Path y z) (a : Fiber x),
    transport (G.compPath γ₁ γ₂) a =
      transport γ₂ (transport γ₁ a)

namespace TransportSystem

/-- One state reaches another when an actual General Space path transports it
there. -/
def Reachable {G : GeneralSpace.{u,v}} (T : TransportSystem G)
    {x y : G.Point} (a : T.Fiber x) (b : T.Fiber y) : Prop :=
  ∃ γ : G.Path x y, T.transport γ a = b

/-- Every state reaches itself along the identity path. -/
theorem reachable_refl {G : GeneralSpace.{u,v}} (T : TransportSystem G)
    {x : G.Point} (a : T.Fiber x) : T.Reachable a a := by
  refine ⟨G.idPath x, ?_⟩
  exact T.transport_id x a

/-- Reachability composes through actual path composition. -/
theorem reachable_trans {G : GeneralSpace.{u,v}} (T : TransportSystem G)
    {x y z : G.Point}
    {a : T.Fiber x} {b : T.Fiber y} {c : T.Fiber z}
    (hab : T.Reachable a b) (hbc : T.Reachable b c) :
    T.Reachable a c := by
  rcases hab with ⟨γ₁, h₁⟩
  rcases hbc with ⟨γ₂, h₂⟩
  refine ⟨G.compPath γ₁ γ₂, ?_⟩
  rw [T.transport_comp γ₁ γ₂ a, h₁, h₂]

end TransportSystem

#check TransportSystem
#check TransportSystem.Reachable
#check TransportSystem.reachable_refl
#check TransportSystem.reachable_trans

#print axioms TransportSystem.reachable_refl
#print axioms TransportSystem.reachable_trans

end GSTGeneralSpaceTransport
