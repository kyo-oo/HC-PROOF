import GSTClassicalHodgeActualPointFiniteFrame

/-!
# Exact, noncircular geometric rank/defect in finite rational Hodge fibers

The actually constructed finite independent codimension-point frame generates
precisely the full algebraic Hodge subspace. The difference between its
geometric rank and the genuine rational Hodge-fiber dimension is the exact
finite-dimensional Hodge defect.

No target-cycle lift, full-rank determinant, nonzero commutator, abstract
matrix-unit stability, or canonical Hodge algebraicity theorem is assumed.

This is an exact rank calculation for what the existing geometric
constructions actually prove, not a declaration that the defect vanishes.
-/

set_option maxHeartbeats 8000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeActualPointFiniteFrame

namespace GSTClassicalHodgeExactGeometricRankDefect

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- The MAXIMAL independent actual-point frame is exactly the algebraic
Hodge subspace. This equality comes from the genuine finite point-cycle
presentation, not from abstract basis-projector closure. -/
theorem actual_point_span_eq_algebraic_hodge_subspace
    (G : GeometricCycleClassSpine V H)
    (p : Nat) :
    actualPointHodgeSpan G p = AlgebraicHodgeSubspace V H p := by
  let L := (rationalHodgeSubspace (H.hodgeBigrading p)).subtype
  have hmap :
      Submodule.map L (actualPointHodgeSpan G p) =
        pointCycleClassSpan p (H.cycleClass p) := by
    change Submodule.map L
        (Submodule.span ℚ (Set.range (actualPointHodgeClass G p))) =
      Submodule.span ℚ (Set.range
        (fun x : CodimensionPoint V.X p =>
          H.cycleClass p (codimensionPointCycle V.X p x)))
    rw [Submodule.map_span]
    apply congrArg (Submodule.span ℚ)
    ext y
    constructor
    · rintro ⟨v, ⟨x, rfl⟩, rfl⟩
      exact ⟨x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨actualPointHodgeClass G p x, ⟨x, rfl⟩, rfl⟩
  calc
    actualPointHodgeSpan G p =
        Submodule.comap L (Submodule.map L (actualPointHodgeSpan G p)) := by
      symm
      exact Submodule.comap_map_eq_of_injective (Submodule.subtype_injective _)
        (actualPointHodgeSpan G p)
    _ = AlgebraicHodgeSubspace V H p := by
      rw [hmap]
      rfl

/-- Exact unfilled *geometric* quotient. The quotient is defined only from
actual codimension-point cycle classes; there is no universal-cycle
existence field and no supplied Hodge target representative. -/
noncomputable def geometricHodgeDefectRank
    (G : GeometricCycleClassSpine V H)
    (p : Nat) : Nat :=
  Module.finrank ℚ
    (ClassicalHodgeFiber V H p ⧸ actualPointHodgeSpan G p)

/-- GEOMETRIC RANK + MISSING HODGE DEFECT = FULL RATIONAL HODGE RANK.
This is rank-nullity for the actual point-generated algebraic Hodge sector,
valid at every finite-dimensional Hodge weight without Hodge surjectivity. -/
theorem actual_geometric_rank_plus_defect_eq_hodge_rank
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    [FiniteDimensional ℚ (ClassicalHodgeFiber V H p)] :
    Module.finrank ℚ (actualPointHodgeSpan G p) +
      geometricHodgeDefectRank G p =
    Module.finrank ℚ (ClassicalHodgeFiber V H p) := by
  change Module.finrank ℚ (actualPointHodgeSpan G p) +
      Module.finrank ℚ
        (ClassicalHodgeFiber V H p ⧸ actualPointHodgeSpan G p) =
      Module.finrank ℚ (ClassicalHodgeFiber V H p)
  simpa only [add_comm] using
    (actualPointHodgeSpan G p).finrank_quotient_add_finrank

#check actual_point_span_eq_algebraic_hodge_subspace
#check geometricHodgeDefectRank
#check actual_geometric_rank_plus_defect_eq_hodge_rank

#print axioms actual_point_span_eq_algebraic_hodge_subspace
#print axioms actual_geometric_rank_plus_defect_eq_hodge_rank

end GSTClassicalHodgeExactGeometricRankDefect
