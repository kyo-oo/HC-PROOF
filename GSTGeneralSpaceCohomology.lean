import GSTGeneralSpaceDuality

/-!
# GST GENERAL SPACE — cohomological geometry

Cohomology is an optional graded realization of General Space.  The core knows
nothing about dimension.  A cohomological realization supplies its own degree
carrier (`Nat` here for compatibility with the repository), additive/scalar
operations, cup product, and path transport laws.
-/

universe u v w r

namespace GSTGeneralSpaceCohomology

open GSTGeneralSpace

/-- Graded cohomological capability over an arbitrary scalar type.  Algebraic
laws of the concrete scalar/module are inherited from concrete realizations;
this interface records the operations and the geometric transport laws needed
by GST. -/
structure CohomologyGeometry (G : GeneralSpace.{u,v}) (R : Type r) where
  Coh : G.Point → Nat → Type w
  zero : (x : G.Point) → (n : Nat) → Coh x n
  add : (x : G.Point) → (n : Nat) → Coh x n → Coh x n → Coh x n
  smul : (x : G.Point) → (n : Nat) → R → Coh x n → Coh x n
  cup : (x : G.Point) → (p q : Nat) →
    Coh x p → Coh x q → Coh x (p + q)
  transport : {x y : G.Point} → G.Path x y →
    (n : Nat) → Coh x n → Coh y n
  transport_id : ∀ (x : G.Point) (n : Nat) (a : Coh x n),
    transport (G.idPath x) n a = a
  transport_comp : ∀ {x y z : G.Point}
      (γ₁ : G.Path x y) (γ₂ : G.Path y z)
      (n : Nat) (a : Coh x n),
    transport (G.compPath γ₁ γ₂) n a =
      transport γ₂ n (transport γ₁ n a)
  transport_zero : ∀ {x y : G.Point} (γ : G.Path x y) (n : Nat),
    transport γ n (zero x n) = zero y n
  transport_add : ∀ {x y : G.Point} (γ : G.Path x y)
      (n : Nat) (a b : Coh x n),
    transport γ n (add x n a b) =
      add y n (transport γ n a) (transport γ n b)
  transport_smul : ∀ {x y : G.Point} (γ : G.Path x y)
      (n : Nat) (r : R) (a : Coh x n),
    transport γ n (smul x n r a) =
      smul y n r (transport γ n a)
  transport_cup : ∀ {x y : G.Point} (γ : G.Path x y)
      (p q : Nat) (a : Coh x p) (b : Coh x q),
    transport γ (p + q) (cup x p q a b) =
      cup y p q (transport γ p a) (transport γ q b)

/-- Cup products are intrinsic under every admissible General Space path. -/
theorem cup_transport_exact
    {G : GeneralSpace.{u,v}} {R : Type r}
    (C : CohomologyGeometry.{w} G R)
    {x y : G.Point} (γ : G.Path x y)
    (p q : Nat) (a : C.Coh x p) (b : C.Coh x q) :
    C.transport γ (p + q) (C.cup x p q a b) =
      C.cup y p q (C.transport γ p a) (C.transport γ q b) :=
  C.transport_cup γ p q a b

#check CohomologyGeometry
#check cup_transport_exact

#print axioms cup_transport_exact

end GSTGeneralSpaceCohomology
