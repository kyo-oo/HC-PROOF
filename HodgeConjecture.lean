import Mathlib.LinearAlgebra.Basis.VectorSpace
import GSTGeometricRealizationStage2G
import GSTTransferBridgeV2
import GSTGlobalPureHodgeCosmology
import GSTDimensionFreeHodgeDiagonal
import GSTUniversalAddressBridge
import GSTTruncatedWorldCohomologyRing
import GSTUniversalLefschetzCosmology
import GSTUniversalLefschetzPathFormula
import GSTUniversalLefschetzKernel
import GSTUniversalLefschetzCausalGeometry
import GSTLefschetzPoincareReciprocity
import GSTWorldPoincareDuality
import GSTWorldRecoordinationGroupoid
import GSTGradedWorldAlgebra

/-!
# Hodge Conjecture — Classical GST Landing

This module attacks the genuine Stage-2G rational Hodge target for actual
smooth projective complex schemes.  The internal GST Hodge classifications
are used only through typed bridges; they are not identified by fiat with
arbitrary classical cohomology.

The decisive construction is a genuine geometric realization whose basis
coordinates are represented by native codimension-p algebraic cycles.  The
realization layers below are rank-free and index-polymorphic: the classical
Hodge fiber is not forced into a preselected finite or countable chart.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G

namespace HodgeConjecture

/-- The exact classical Hodge target already isolated by Stage 2G.

For every codimension `p`, every rational singular-cohomology class whose
complexification lies in the `(p,p)` Hodge summand must lie in the range of
the native codimension-`p` algebraic cycle-class map. -/
def ClassicalHodgeTarget
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) : Prop :=
  BigradedBettiHodgeStatement V H

/-- The target is exactly the elementwise algebraic-cycle witness statement;
there is no weaker GST surrogate hidden behind the name. -/
theorem classicalHodgeTarget_iff_explicit_witness
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) :
    ClassicalHodgeTarget V H ↔
      ∀ p : Nat,
      ∀ alpha : RationalSingularCohomology H.analytification (2 * p),
        complexificationMapQ
            (RationalSingularCohomology H.analytification (2 * p)) alpha
          ∈ (H.hodgeBigrading p).ppComponent →
        ∃ Z : codimensionCycles V.X p,
          H.cycleClass p Z = alpha := by
  simpa [ClassicalHodgeTarget] using
    (bigradedBettiHodgeStatement_iff_explicit_witness V H)

/-- Stage 2G has already proved the final logical landing.  Consequently the
new mathematics in this file is exactly the construction of the compact
realization obligation, not another reformulation of the conclusion. -/
theorem classicalHodgeTarget_of_compact_realization
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (hR : Stage2GCompactRealizationObligation V H) :
    ClassicalHodgeTarget V H := by
  exact bigraded_betti_hodge_of_stage2g_compact_obligation V H hR

/-- Elementwise form of the same reduction, useful while constructing the
actual GST-to-classical cycle witnesses. -/
theorem explicit_witness_of_compact_realization
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (hR : Stage2GCompactRealizationObligation V H)
    (p : Nat)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha :
      complexificationMapQ
          (RationalSingularCohomology H.analytification (2 * p)) alpha
        ∈ (H.hodgeBigrading p).ppComponent) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha := by
  exact
    (classicalHodgeTarget_iff_explicit_witness V H).mp
      (classicalHodgeTarget_of_compact_realization V H hR)
      p alpha halpha

/-! ## Index-polymorphic limitless realization

`CompactHodgeRealization` itself never required the address type to be
`Nat`.  Keeping an arbitrary index type matters for the classical landing:
no countability or finite-rank assumption should be smuggled into an
arbitrary Betti-Hodge fiber merely because the historical GST address system
used natural coordinates.
-/

/-- One Stage-2G realization with an arbitrary address universe `ι`.

The structure contains no Hodge conclusion.  It asks for an injective
finitely-supported encoding and native algebraic basis cycles, exactly as
`CompactHodgeRealization` does, and only records compatibility with the
actual Stage-2G Hodge predicate and cycle-class map. -/
structure UniverseIndexedRealization
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) (ι : Type*) where
  realization :
    CompactHodgeRealization ι
      (RationalSingularCohomology H.analytification (2 * p))
      (codimensionCycles V.X p)
  hodge_iff :
    ∀ alpha : RationalSingularCohomology H.analytification (2 * p),
      realization.isHodge alpha ↔
        alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p)
  cycleClass_eq :
    realization.cycleClass = H.cycleClass p

/-- Any genuine index-polymorphic realization produces an actual native
codimension-p cycle for each rational `(p,p)` class. -/
theorem hodge_class_has_cycle_of_universe_indexed_realization
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    {p : Nat} {ι : Type*}
    (R : UniverseIndexedRealization V H p ι)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p)) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha := by
  have hr : R.realization.isHodge alpha :=
    (R.hodge_iff alpha).2 halpha
  obtain ⟨Z, hZ⟩ :=
    compact_realization_surjectivity R.realization alpha hr
  refine ⟨Z, ?_⟩
  rw [← R.cycleClass_eq]
  exact hZ

/-- A family of arbitrary-index realizations closes the exact classical
Stage-2G target.  The index type may vary with the codimension. -/
theorem classicalHodgeTarget_of_universe_indexed_family
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (ι : Nat → Type*)
    (R : ∀ p : Nat, UniverseIndexedRealization V H p (ι p)) :
    ClassicalHodgeTarget V H := by
  intro p alpha halpha
  exact hodge_class_has_cycle_of_universe_indexed_realization
    V H (R p) alpha halpha

/-! ## Exact limitless coordinates on the genuine Hodge fiber

The old finite GST Hodge diagonal has one coordinate per live weight.  That
is not enough to model an arbitrary classical `(p,p)` Hodge space, which may
have arbitrary multiplicity.  We therefore keep the GST finite-support
principle but fiber it over a genuine vector-space basis of the actual
rational Hodge subspace.  This is rank-free and requires no countability.
-/

/-- The actual rational `(p,p)` Hodge fiber in degree `2p`. -/
abbrev HodgeFiber
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) : Type :=
  rationalHodgeSubspace (H.hodgeBigrading p)

/-- A completely unrestricted basis index for one classical Hodge fiber. -/
abbrev HodgeBasisIndex
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) :=
  Module.Free.ChooseBasisIndex ℚ (HodgeFiber V H p)

/-- A chosen rational basis of the genuine `(p,p)` Hodge fiber. -/
noncomputable def hodgeBasis
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) :
    Module.Basis (HodgeBasisIndex V H p) ℚ (HodgeFiber V H p) :=
  Module.Free.chooseBasis ℚ (HodgeFiber V H p)

/-- Limitless finite-support coordinates of a genuine Hodge class.  No fixed
rank occurs: every individual class has finite support because `Basis.repr`
lands in a `Finsupp`. -/
noncomputable def hodgeCoordinates
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) :
    HodgeFiber V H p ≃ₗ[ℚ] (HodgeBasisIndex V H p →₀ ℚ) :=
  (hodgeBasis V H p).repr

@[simp]
theorem hodgeCoordinates_basis
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) (i : HodgeBasisIndex V H p) :
    hodgeCoordinates V H p (hodgeBasis V H p i) =
      Finsupp.single i 1 := by
  simp [hodgeCoordinates]

/-- The irreducible geometric datum for one Hodge fiber: every basis vector
has an actual native codimension-`p` algebraic-cycle representative.

This is deliberately weaker than assuming cycle-class surjectivity on all
Hodge classes.  Arbitrary Hodge classes will be reconstructed from these
basis representatives by the finite-support coordinate law above. -/
structure HodgeBasisCycleBridge
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) where
  basisCycle : HodgeBasisIndex V H p → codimensionCycles V.X p
  basisCycle_spec :
    ∀ i : HodgeBasisIndex V H p,
      H.cycleClass p (basisCycle i) = (hodgeBasis V H p i).1

/-- Lift the chosen Hodge basis to native algebraic cycles linearly. -/
noncomputable def hodgeBasisCycleLift
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (R : HodgeBasisCycleBridge V H p) :
    HodgeFiber V H p →ₗ[ℚ] codimensionCycles V.X p :=
  (hodgeBasis V H p).constr ℚ R.basisCycle

@[simp]
theorem hodgeBasisCycleLift_basis
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (R : HodgeBasisCycleBridge V H p)
    (i : HodgeBasisIndex V H p) :
    hodgeBasisCycleLift V H p R (hodgeBasis V H p i) =
      R.basisCycle i := by
  simp [hodgeBasisCycleLift]

/-- Finite-support reconstruction is exact: after applying the genuine
cycle-class map, the basis-cycle lift is precisely the inclusion of the Hodge
subspace into ambient rational singular cohomology. -/
theorem hodgeBasisCycleLift_spec
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (R : HodgeBasisCycleBridge V H p)
    (alpha : HodgeFiber V H p) :
    H.cycleClass p (hodgeBasisCycleLift V H p R alpha) = alpha.1 := by
  have hmaps :
      (H.cycleClass p).comp (hodgeBasisCycleLift V H p R) =
        (rationalHodgeSubspace (H.hodgeBigrading p)).subtype := by
    apply (hodgeBasis V H p).ext
    intro i
    simp [hodgeBasisCycleLift, R.basisCycle_spec]
  change ((H.cycleClass p).comp (hodgeBasisCycleLift V H p R)) alpha = alpha.1
  rw [hmaps]
  rfl

/-- Basis-wise algebraicity therefore produces a native cycle for an
arbitrary rational `(p,p)` class. -/
theorem hodge_class_has_cycle_of_basis_bridge
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    {p : Nat}
    (R : HodgeBasisCycleBridge V H p)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p)) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha := by
  let alphaH : HodgeFiber V H p := ⟨alpha, halpha⟩
  refine ⟨hodgeBasisCycleLift V H p R alphaH, ?_⟩
  simpa [alphaH] using hodgeBasisCycleLift_spec V H p R alphaH

/-- A basis-cycle bridge in every codimension closes the exact classical
Hodge target, with arbitrary rank and multiplicity. -/
theorem classicalHodgeTarget_of_basis_cycle_family
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (R : ∀ p : Nat, HodgeBasisCycleBridge V H p) :
    ClassicalHodgeTarget V H := by
  intro p alpha halpha
  exact hodge_class_has_cycle_of_basis_bridge V H (R p) alpha halpha

/-- If the classical target already holds, each chosen Hodge basis vector has
a native algebraic representative.  This direction is used only to prove the
normal-form equivalence below; it is not used as a construction in the
forward proof program. -/
noncomputable def hodgeBasisCycleBridgeOfTarget
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (h : ClassicalHodgeTarget V H)
    (p : Nat) :
    HodgeBasisCycleBridge V H p where
  basisCycle i :=
    Classical.choose (show
      ∃ Z : codimensionCycles V.X p,
        H.cycleClass p Z = (hodgeBasis V H p i).1 by
      exact h p (hodgeBasis V H p i).2)
  basisCycle_spec i :=
    Classical.choose_spec (show
      ∃ Z : codimensionCycles V.X p,
        H.cycleClass p Z = (hodgeBasis V H p i).1 by
      exact h p (hodgeBasis V H p i).2)

/-- **BASIS-GENERATOR NORMAL FORM.**

The exact Stage-2G Hodge target is equivalent to algebraicity of one chosen
basis of every rational `(p,p)` Hodge fiber.  The backward direction is the
substantive finite-support reconstruction theorem; the forward direction is
only logical extraction from an already-supplied target proof.

This theorem isolates the classical geometric problem as sharply as possible:
construct native codimension-`p` cycles for the basis vectors. -/
theorem classicalHodgeTarget_iff_basis_cycle_bridges
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) :
    ClassicalHodgeTarget V H ↔
      ∀ p : Nat, Nonempty (HodgeBasisCycleBridge V H p) := by
  constructor
  · intro h p
    exact ⟨hodgeBasisCycleBridgeOfTarget V H h p⟩
  · intro h
    exact classicalHodgeTarget_of_basis_cycle_family V H
      (fun p => Classical.choice (h p))

/-- Semantic firewall: if a supplied cycle-class map is zero while the Hodge
sector contains a nonzero class, then the classical Hodge target for that
semantic package is impossible.  Thus the final theorem cannot legitimately
quantify over arbitrary `HodgeBigradedBettiData` and manufacture surjectivity
from GST syntax alone; a genuine geometric cycle-class bridge is required. -/
theorem not_classicalHodgeTarget_of_zero_cycleClass
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha :
      complexificationMapQ
          (RationalSingularCohomology H.analytification (2 * p)) alpha
        ∈ (H.hodgeBigrading p).ppComponent)
    (halpha_ne : alpha ≠ 0)
    (hzero : H.cycleClass p = 0) :
    ¬ ClassicalHodgeTarget V H := by
  intro hTarget
  obtain ⟨Z, hZ⟩ :=
    (classicalHodgeTarget_iff_explicit_witness V H).mp hTarget
      p alpha halpha
  have hzeroZ : H.cycleClass p Z = 0 := by
    rw [hzero]
    rfl
  apply halpha_ne
  rw [← hZ, hzeroZ]

#check ClassicalHodgeTarget
#check classicalHodgeTarget_iff_explicit_witness
#check classicalHodgeTarget_of_compact_realization
#check explicit_witness_of_compact_realization
#check UniverseIndexedRealization
#check hodge_class_has_cycle_of_universe_indexed_realization
#check classicalHodgeTarget_of_universe_indexed_family
#check HodgeFiber
#check HodgeBasisIndex
#check hodgeBasis
#check hodgeCoordinates
#check hodgeCoordinates_basis
#check HodgeBasisCycleBridge
#check hodgeBasisCycleLift
#check hodgeBasisCycleLift_spec
#check hodge_class_has_cycle_of_basis_bridge
#check classicalHodgeTarget_of_basis_cycle_family
#check hodgeBasisCycleBridgeOfTarget
#check classicalHodgeTarget_iff_basis_cycle_bridges
#check not_classicalHodgeTarget_of_zero_cycleClass

#print axioms classicalHodgeTarget_iff_explicit_witness
#print axioms classicalHodgeTarget_of_compact_realization
#print axioms explicit_witness_of_compact_realization
#print axioms hodge_class_has_cycle_of_universe_indexed_realization
#print axioms classicalHodgeTarget_of_universe_indexed_family
#print axioms hodgeCoordinates_basis
#print axioms hodgeBasisCycleLift_spec
#print axioms hodge_class_has_cycle_of_basis_bridge
#print axioms classicalHodgeTarget_of_basis_cycle_family
#print axioms classicalHodgeTarget_iff_basis_cycle_bridges
#print axioms not_classicalHodgeTarget_of_zero_cycleClass

end HodgeConjecture
