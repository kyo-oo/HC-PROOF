import GSTGeneralSpaceRealization

/-!
# GST GENERAL SPACE — duality geometry

Duality is a capability of a transported state system, never a consequence of
a chosen coordinate dimension.  The pairing scalar and the state fibers are
arbitrary types; nondegeneracy is expressed through intrinsic probes.
-/

universe u v w z

namespace GSTGeneralSpaceDuality

open GSTGeneralSpace
open GSTGeneralSpaceTransport

/-- A transported state system with a distinguished zero state in every
fiber. -/
structure PointedTransportSystem (G : GeneralSpace.{u,v})
    extends TransportSystem.{w} G where
  zero : (x : G.Point) → Fiber x
  transport_zero : ∀ {x y : G.Point} (γ : G.Path x y),
    transport γ (zero x) = zero y

/-- Dimension-free nondegenerate pairing/probe system. -/
structure NondegenerateDuality {G : GeneralSpace.{u,v}}
    (T : PointedTransportSystem.{w} G) where
  Scalar : Type z
  zeroScalar : Scalar
  pair : (x : G.Point) → T.Fiber x → T.Fiber x → Scalar
  transport_invariant : ∀ {x y : G.Point} (γ : G.Path x y)
      (a b : T.Fiber x),
    pair y (T.transport γ a) (T.transport γ b) = pair x a b
  left_nondegenerate : ∀ (x : G.Point) (a : T.Fiber x),
    (∀ b : T.Fiber x, pair x a b = zeroScalar) → a = T.zero x

/-- A nonzero state must be detected by at least one dual probe. -/
theorem exists_detecting_probe
    {G : GeneralSpace.{u,v}}
    {T : PointedTransportSystem.{w} G}
    (D : NondegenerateDuality.{z} T)
    (x : G.Point) (a : T.Fiber x)
    (ha : a ≠ T.zero x) :
    ∃ b : T.Fiber x, D.pair x a b ≠ D.zeroScalar := by
  by_contra h
  push_neg at h
  exact ha (D.left_nondegenerate x a h)

/-- Pairing values are intrinsic under any transported path. -/
theorem pair_transport_exact
    {G : GeneralSpace.{u,v}}
    {T : PointedTransportSystem.{w} G}
    (D : NondegenerateDuality.{z} T)
    {x y : G.Point} (γ : G.Path x y) (a b : T.Fiber x) :
    D.pair y (T.transport γ a) (T.transport γ b) = D.pair x a b :=
  D.transport_invariant γ a b

#check PointedTransportSystem
#check NondegenerateDuality
#check exists_detecting_probe
#check pair_transport_exact

#print axioms exists_detecting_probe
#print axioms pair_transport_exact

end GSTGeneralSpaceDuality
