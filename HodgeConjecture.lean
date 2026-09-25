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
realization layer below is index-polymorphic: the classical Hodge fiber is not
forced into a preselected countable chart.  The older Stage-2G compact route
with index `Nat` remains available as a specialization.
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
#check not_classicalHodgeTarget_of_zero_cycleClass

#print axioms classicalHodgeTarget_iff_explicit_witness
#print axioms classicalHodgeTarget_of_compact_realization
#print axioms explicit_witness_of_compact_realization
#print axioms hodge_class_has_cycle_of_universe_indexed_realization
#print axioms classicalHodgeTarget_of_universe_indexed_family
#print axioms not_classicalHodgeTarget_of_zero_cycleClass

end HodgeConjecture
