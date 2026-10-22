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


/-- GST signed two-level causal boundary, as a genuine rational free-cell relation. -/
noncomputable def causalTwoBoundary {n : Nat} (x : H.Cell (n+2)) :
    H.Cell n →₀ ℚ := by
  classical
  exact Finsupp.single (H.source (H.source x)) 1 -
    Finsupp.single (H.target (H.source x)) 1 -
    Finsupp.single (H.source (H.target x)) 1 +
    Finsupp.single (H.target (H.target x)) 1

/-- The two globular face laws force the signed double boundary to vanish. -/
theorem causalTwoBoundary_zero {n : Nat} (x : H.Cell (n+2)) :
    causalTwoBoundary C H x = 0 := by
  classical
  simp only [causalTwoBoundary, H.source_source x, H.target_source x]
  abel


#check HigherCausalCosmos
#check HigherCausalCosmos.Parallel
#check HigherCausalCosmos.Coheres
#check HigherCausalCosmos.identityTower
#check HigherCausalCosmos.world_has_cell_at_every_dimension
#check HigherCausalCosmos.globular_boundary_crown
#check HigherCausalCosmos.identityTower_preserves


/-! ## GST CAUSAL INCIDENCE AND INDEPENDENT LOOP GENESIS

An actual higher-causal 1-cell must be supplied, rather than treating the
identity tower as a family of fresh geometric dimensions. A finite independent
family of genuine closed 1-cells has an exact zero incidence coboundary and
genuinely independent rational loop readouts. This is the causal input to
N-cohomology and the emergent Hodge-source construction.

The geometric identification of these higher cells with a realized nodal
incidence graph is a further certified source-to-geometry step, not built into
the abstract higher-causal ontology.
-/

/-- An independent collection of closed causal 1-cells rooted at world W.
The injectivity and nonidentity laws exclude counting one identity cell
repeated g times as g independently born causal loops. -/
structure AnchoredCausalLoops (W : C.World) (g : ℕ) where
  edge : Fin g → H.Cell 1
  source_root : ∀ i : Fin g, H.source (edge i) = H.worldCell W
  target_root : ∀ i : Fin g, H.target (edge i) = H.worldCell W
  distinct_edges : Function.Injective edge
  genuine_edges : ∀ i : Fin g, edge i ≠ H.identity (H.worldCell W)

/-- A causal potential has one scalar value on each zero-cell.
The incidence gradient measures the difference between its endpoints
across one actual causal 1-cell. -/
def AnchoredCausalLoops.incidenceGradient
    {W : C.World} {g : ℕ} (L : AnchoredCausalLoops C H W g)
    (potential : H.Cell 0 → ℚ) : Fin g → ℚ :=
  fun i => potential (H.target (L.edge i)) -
    potential (H.source (L.edge i))

/-- Every genuine closed-loop edge has exact zero incidence gradient.
This derives the cochain equation from the existing globular causal
source/target structure, not from an invented Hodge-class map. -/
theorem AnchoredCausalLoops.incidenceGradient_zero
    {W : C.World} {g : ℕ} (L : AnchoredCausalLoops C H W g)
    (potential : H.Cell 0 → ℚ) :
    AnchoredCausalLoops.incidenceGradient C H L potential = 0 := by
  funext i
  simp [AnchoredCausalLoops.incidenceGradient, L.target_root i,
    L.source_root i]

/-- Actual independent rational readouts of the certified causal loops. -/
abbrev AnchoredCausalLoops.loopReadouts
    {W : C.World} {g : ℕ} (L : AnchoredCausalLoops C H W g) :=
  Fin g → ℚ

/-- One basis cochain for each certified, nonidentity causal loop. -/
def AnchoredCausalLoops.loopBasis
    {W : C.World} {g : ℕ} (L : AnchoredCausalLoops C H W g)
    (i : Fin g) : L.loopReadouts :=
  fun j => if i = j then 1 else 0

/-- All certified independent loop coordinates are exactly reconstructible.
This is the finite constructive rank input for causal N-cohomology. -/
theorem AnchoredCausalLoops.loopBasis_reconstruct
    {W : C.World} {g : ℕ} (L : AnchoredCausalLoops C H W g)
    (c : L.loopReadouts) (j : Fin g) :
    (∑ i : Fin g, c i * AnchoredCausalLoops.loopBasis C H L i j) = c j := by
  classical
  simp [AnchoredCausalLoops.loopBasis]

/-- There is no hidden loss of independently born causal channels. -/
theorem AnchoredCausalLoops.loopBasis_coefficients_unique
    {W : C.World} {g : ℕ} (L : AnchoredCausalLoops C H W g)
    (c : L.loopReadouts)
    (hzero : ∀ j : Fin g, (∑ i : Fin g,
      c i * AnchoredCausalLoops.loopBasis C H L i j) = 0) :
    ∀ i : Fin g, c i = 0 := by
  intro i
  simpa [AnchoredCausalLoops.loopBasis_reconstruct C H L c i] using hzero i


/-! ## HIGHER CAUSAL 2-FACE DEATH / SURVIVAL LAW

A nonidentity closed causal 1-cell is NOT automatically an independent
cohomology direction. A genuine 2-cell can identify that loop with the
identity world path, making all homotopy-invariant additive readouts
vanish on it. This upgrades first-skeleton loop counting to an honest
two-dimensional causal relation before any Hodge realization.

The geometric all-N counterpart is H_1 = ker boundary1 / image boundary2;
the exact finite incidence/weight law is derived in
research/derivations/GST_causal_graph_double_fold_weight_emergence_2026-10-22.tex.
-/

/-- An actual finite family of higher-causal 2-cells filling specified
closed 1-cells from a previously certified loop family. None of the
fillers are asserted to exist without supplying the Cell 2 witness. -/
structure AnchoredCausalTwoFillings
    {W : C.World} {g : ℕ}
    (L : AnchoredCausalLoops C H W g) (f : ℕ) where
  face : Fin f → H.Cell 2
  edgeIndex : Fin f → Fin g
  source_face : ∀ i : Fin f, H.source (face i) = L.edge (edgeIndex i)
  target_face : ∀ i : Fin f,
    H.target (face i) = H.identity (H.worldCell W)

/-- A true 2-homotopy-invariant causal readout annihilates every
filled graph loop. This is a source-to-target implication FROM
ACTUAL higher cells, not a declared dimension or chosen Hodge basis. -/
theorem AnchoredCausalTwoFillings.filled_loop_readout_zero
    {W : C.World} {g f : ℕ}
    {L : AnchoredCausalLoops C H W g}
    (F : AnchoredCausalTwoFillings C H L f)
    (readout : H.Cell 1 → ℚ)
    (hhomotopy : ∀ x : H.Cell 2,
      readout (H.source x) = readout (H.target x))
    (hidentity : readout (H.identity (H.worldCell W)) = 0)
    (i : Fin f) :
    readout (L.edge (F.edgeIndex i)) = 0 := by
  calc
    readout (L.edge (F.edgeIndex i)) =
        readout (H.source (F.face i)) := by rw [F.source_face i]
    _ = readout (H.target (F.face i)) := hhomotopy _
    _ = readout (H.identity (H.worldCell W)) := by rw [F.target_face i]
    _ = 0 := hidentity

/-- Kill precisely those finite loop-coordinate channels proven
homotopic to the identity by a SUPPLIED higher-causal 2-cell.
This is the incidence-level realization of the 2-face quotient. -/
def AnchoredCausalTwoFillings.survivor
    {W : C.World} {g f : ℕ}
    {L : AnchoredCausalLoops C H W g}
    (F : AnchoredCausalTwoFillings C H L f)
    (c : L.loopReadouts) : L.loopReadouts :=
  fun i => if ∃ j : Fin f, F.edgeIndex j = i then 0 else c i

/-- Each genuinely filled higher-causal loop has ZERO residual
N-cohomology coordinate after projection. -/
theorem AnchoredCausalTwoFillings.survivor_filled_zero
    {W : C.World} {g f : ℕ}
    {L : AnchoredCausalLoops C H W g}
    (F : AnchoredCausalTwoFillings C H L f)
    (c : L.loopReadouts) (j : Fin f) :
    AnchoredCausalTwoFillings.survivor C H F c (F.edgeIndex j) = 0 := by
  classical
  simp [AnchoredCausalTwoFillings.survivor,
    show ∃ k : Fin f, F.edgeIndex k = F.edgeIndex j from ⟨j, rfl⟩]

/-- Actual causal 2-face elimination is an IDEMPOTENT operation:
the same certified geometric filling cannot keep creating or
destroying further Hodge channels by being replayed. -/
theorem AnchoredCausalTwoFillings.survivor_idempotent
    {W : C.World} {g f : ℕ}
    {L : AnchoredCausalLoops C H W g}
    (F : AnchoredCausalTwoFillings C H L f)
    (c : L.loopReadouts) :
    AnchoredCausalTwoFillings.survivor C H F
      (AnchoredCausalTwoFillings.survivor C H F c) =
        AnchoredCausalTwoFillings.survivor C H F c := by
  classical
  funext i
  by_cases h : ∃ j : Fin f, F.edgeIndex j = i
  · simp [AnchoredCausalTwoFillings.survivor, h]
  · simp [AnchoredCausalTwoFillings.survivor, h]

#check AnchoredCausalTwoFillings.filled_loop_readout_zero
#check AnchoredCausalTwoFillings.survivor_filled_zero
#check AnchoredCausalTwoFillings.survivor_idempotent
#print axioms AnchoredCausalTwoFillings.filled_loop_readout_zero
#print axioms AnchoredCausalTwoFillings.survivor_idempotent

#check AnchoredCausalLoops.incidenceGradient_zero
#check AnchoredCausalLoops.loopBasis_reconstruct
#check AnchoredCausalLoops.loopBasis_coefficients_unique
#print axioms AnchoredCausalLoops.incidenceGradient_zero
#print axioms AnchoredCausalLoops.loopBasis_coefficients_unique


end HigherCausalCosmos
end GSTGraphV2UnboundedHigherCausality
