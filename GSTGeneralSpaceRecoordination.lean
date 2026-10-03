import GSTGeneralSpaceTransport

/-!
# GST GENERAL SPACE — recoordination geometry

A recoordination is a reversible path presentation of one General Space
sector.  Intrinsic observables and predicates are transported by the semantic
transport system, so chart labels never become ontology.
-/

universe u v w z

namespace GSTGeneralSpaceRecoordination

open GSTGeneralSpace
open GSTGeneralSpaceTransport

/-- Reversible General Space path data. -/
structure Recoordination (G : GeneralSpace.{u,v}) (x y : G.Point) where
  forward : G.Path x y
  backward : G.Path y x
  forward_backward : G.compPath forward backward = G.idPath x
  backward_forward : G.compPath backward forward = G.idPath y

/-- An intrinsic observable of a transported state system. -/
structure InvariantObservable {G : GeneralSpace.{u,v}}
    (T : TransportSystem G) where
  Value : Type z
  eval : (x : G.Point) → T.Fiber x → Value
  invariant : ∀ {x y : G.Point} (γ : G.Path x y) (a : T.Fiber x),
    eval y (T.transport γ a) = eval x a

/-- An intrinsic predicate of a transported state system. -/
structure InvariantPredicate {G : GeneralSpace.{u,v}}
    (T : TransportSystem G) where
  holds : (x : G.Point) → T.Fiber x → Prop
  invariant : ∀ {x y : G.Point} (γ : G.Path x y) (a : T.Fiber x),
    holds y (T.transport γ a) ↔ holds x a

/-- Forward transport followed by backward transport is the identity on every
state, by semantic functoriality and the recoordination witness. -/
theorem transport_forward_backward
    {G : GeneralSpace.{u,v}} (T : TransportSystem G)
    {x y : G.Point} (R : Recoordination G x y) (a : T.Fiber x) :
    T.transport R.backward (T.transport R.forward a) = a := by
  calc
    T.transport R.backward (T.transport R.forward a) =
        T.transport (G.compPath R.forward R.backward) a := by
          symm
          exact T.transport_comp R.forward R.backward a
    _ = T.transport (G.idPath x) a := by rw [R.forward_backward]
    _ = a := T.transport_id x a

/-- Backward then forward is likewise the identity. -/
theorem transport_backward_forward
    {G : GeneralSpace.{u,v}} (T : TransportSystem G)
    {x y : G.Point} (R : Recoordination G x y) (b : T.Fiber y) :
    T.transport R.forward (T.transport R.backward b) = b := by
  calc
    T.transport R.forward (T.transport R.backward b) =
        T.transport (G.compPath R.backward R.forward) b := by
          symm
          exact T.transport_comp R.backward R.forward b
    _ = T.transport (G.idPath y) b := by rw [R.backward_forward]
    _ = b := T.transport_id y b

/-- Every invariant observable has identical value before and after an exact
recoordination. -/
theorem observable_recoordination
    {G : GeneralSpace.{u,v}} (T : TransportSystem G)
    (F : InvariantObservable T)
    {x y : G.Point} (R : Recoordination G x y) (a : T.Fiber x) :
    F.eval y (T.transport R.forward a) = F.eval x a :=
  F.invariant R.forward a

/-- Every intrinsic proposition is preserved by exact recoordination. -/
theorem predicate_recoordination
    {G : GeneralSpace.{u,v}} (T : TransportSystem G)
    (P : InvariantPredicate T)
    {x y : G.Point} (R : Recoordination G x y) (a : T.Fiber x) :
    P.holds y (T.transport R.forward a) ↔ P.holds x a :=
  P.invariant R.forward a

#check Recoordination
#check InvariantObservable
#check InvariantPredicate
#check transport_forward_backward
#check transport_backward_forward
#check observable_recoordination
#check predicate_recoordination

#print axioms transport_forward_backward
#print axioms observable_recoordination

end GSTGeneralSpaceRecoordination
