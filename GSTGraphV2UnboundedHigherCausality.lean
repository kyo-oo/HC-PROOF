import GSTGraphV2SelfExpandingCosmology

/-!
# GST GRAPH V2 — UNBOUNDED HIGHER CAUSALITY

Branching worlds are only half of the intended evolution.  Geometry also has
relations between constructions: two paths may commute, two correspondences
may be identified by a higher law, two identifications may themselves satisfy
coherence, and so on.

This file therefore adds an optional globular causal tower over a
`SelfExpandingCosmos`.

* 0-cells contain worlds;
* 1-cells may encode events/constructions;
* 2-cells may encode relations between constructions;
* 3-cells may encode relations between those relations;
* the tower continues for every natural dimension.

There is no maximum geometric dimension in the interface.  Identity lifting
also guarantees that every world has a canonical cell at every higher level,
so the tower is not merely syntactically indexed by all naturals.
-/

universe u v w z q

namespace GSTGraphV2UnboundedHigherCausality

open GSTGraphV2OmniversalCore
open GSTGraphV2SelfExpandingCosmology

variable (C : SelfExpandingCosmos.{u,v,w,z})

/-- An unbounded globular causal extension of a recursively generated cosmos. -/
structure HigherCausalCosmos where
  Cell : Nat → Type q
  worldCell : C.World → Cell 0
  source : {n : Nat} → Cell (n+1) → Cell n
  target : {n : Nat} → Cell (n+1) → Cell n
  identity : {n : Nat} → Cell n → Cell (n+1)
  source_identity : ∀ {n : Nat} (x : Cell n), source (identity x) = x
  target_identity : ∀ {n : Nat} (x : Cell n), target (identity x) = x
  source_source : ∀ {n : Nat} (x : Cell (n+2)),
    source (source x) = source (target x)
  target_source : ∀ {n : Nat} (x : Cell (n+2)),
    target (source x) = target (target x)

namespace HigherCausalCosmos

variable (H : HigherCausalCosmos C)

/-- Two positive-dimensional cells are parallel when they have the same source
and target. -/
def Parallel {n : Nat} (a b : H.Cell (n+1)) : Prop :=
  H.source a = H.source b ∧ H.target a = H.target b

/-- A higher cell witnesses a directed coherence from `a` to `b`. -/
def Coheres {n : Nat} (a b : H.Cell n) : Prop :=
  ∃ c : H.Cell (n+1), H.source c = a ∧ H.target c = b

/-- Identity higher cells give reflexive coherence at every dimension. -/
theorem coheres_refl {n : Nat} (a : H.Cell n) :
    Coheres C H a a := by
  refine ⟨H.identity a, ?_, ?_⟩
  · exact H.source_identity a
  · exact H.target_identity a

/-- A world canonically lifts through identity coherence to every dimension. -/
def identityTower (W : C.World) : (n : Nat) → H.Cell n
  | 0 => H.worldCell W
  | n+1 => H.identity (identityTower W n)

/-- Every world therefore has a cell in every finite dimension.  There is no
hard-coded top dimension in the GST higher-causal ontology. -/
theorem world_has_cell_at_every_dimension
    (W : C.World) :
    ∀ n : Nat, ∃ x : H.Cell n, True := by
  intro n
  exact ⟨identityTower C H W n, trivial⟩

/-- Successive levels of the identity tower have the previous level as both
source and target. -/
theorem identityTower_boundary
    (W : C.World) (n : Nat) :
    H.source (identityTower C H W (n+1)) = identityTower C H W n ∧
    H.target (identityTower C H W (n+1)) = identityTower C H W n := by
  constructor
  · exact H.source_identity (identityTower C H W n)
  · exact H.target_identity (identityTower C H W n)

/-- Every 2-or-higher cell satisfies the two globular boundary equations. -/
theorem globular_boundary_crown
    {n : Nat} (x : H.Cell (n+2)) :
    H.source (H.source x) = H.source (H.target x) ∧
    H.target (H.source x) = H.target (H.target x) := by
  exact ⟨H.source_source x, H.target_source x⟩

/-- A property family is stable under higher identity when it survives one
coherence lift at every dimension. -/
def IdentityStable (P : ∀ n, H.Cell n → Prop) : Prop :=
  ∀ {n : Nat} (x : H.Cell n), P n x → P (n+1) (H.identity x)

/-- Any identity-stable property possessed by a world-cell propagates through
its entire unbounded coherence tower. -/
theorem identityTower_preserves
    (P : ∀ n, H.Cell n → Prop)
    (hStable : IdentityStable C H P)
    (W : C.World)
    (h0 : P 0 (H.worldCell W)) :
    ∀ n : Nat, P n (identityTower C H W n) := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih =>
      exact hStable (identityTower C H W n) ih

#check HigherCausalCosmos
#check HigherCausalCosmos.Parallel
#check HigherCausalCosmos.Coheres
#check HigherCausalCosmos.identityTower
#check HigherCausalCosmos.world_has_cell_at_every_dimension
#check HigherCausalCosmos.globular_boundary_crown
#check HigherCausalCosmos.identityTower_preserves

end HigherCausalCosmos
end GSTGraphV2UnboundedHigherCausality
