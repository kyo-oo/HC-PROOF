import GSTClassicalHodgeUniversalLimitlessCycleGeometry
import GSTClassicalHodgeUniversalTwoSlotNativeClosure

/-!
# GST CLASSICAL HODGE — UNIVERSAL LIMITLESS CYCLE GEOMETRY FINALE

The raw `HodgeBigradedBettiData` carrier cannot support an unconditional Hodge
surjectivity theorem because its `cycleClass` field is arbitrary.  The genuine
projective geometry developed in this repository supplies a different route:

* the geometric cycle-class spine puts every native point class in Hodge type;
* positive projective-degree trace semantics makes every such point class
  nonzero;
* the universal two-slot native closure turns three primitive native point
  lifts into stability under the single rank-free GST transfer word;
* universal two-slot saturation promotes one nonzero algebraic seed to the
  whole unrestricted rational `(p,p)` Hodge fiber.

This file composes those independently geometric layers.  No cycle-class
surjectivity, basis-cycle representative, defect-zero statement, or Hodge
conclusion is assumed.
-/

set_option maxHeartbeats 60000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeProjectiveDegreeTrace
open GSTClassicalHodgeUniversalLimitlessCycleGeometry
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeRankFreePrimitiveGeneration
open GSTClassicalHodgeUniversalTwoSlotSaturation
open GSTClassicalHodgeUniversalTwoSlotNativeClosure

namespace GSTClassicalHodgeUniversalLimitlessCycleGeometryFinale

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Every nonzero rational Hodge stratum is backed by an actual projective
codimension stratum.  This is a geometric occupancy condition, not an
algebraicity or surjectivity assertion. -/
def HodgeStratumOccupancy
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) : Prop :=
  ∀ q : Nat,
    rationalHodgeSubspace (H.hodgeBigrading q) ≠ ⊥ →
      Nonempty (CodimensionPoint V.X q)

/-- The three primitive native point-lift laws of the universal two-slot GST
machine, uniformly over every weight and every ordered pair of genuine Hodge
basis directions. -/
def UniversalNativeTwoSlotGeometry
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) : Prop :=
  ∀ q : Nat,
    ∀ i j : ClassicalHodgeBasisIndex V H q,
      PrimitiveNativeTwoSlot (V := V) (H := H) (p := q) i j

/-- Native point-lift geometry of the three primitive two-slot operators
implies invariance of the *actual algebraic Hodge subspace* under the universal
rank-free GST transfer word. -/
theorem algebraicHodgeSubspace_twoSlotInvariant_of_native_geometry
    {q : Nat}
    (R : ∀ i j : ClassicalHodgeBasisIndex V H q,
      PrimitiveNativeTwoSlot (V := V) (H := H) (p := q) i j) :
    UniversalTwoSlotInvariant (AlgebraicHodgeSubspace V H q) := by
  intro i j alpha halpha
  have hspan :
      alpha.1 ∈ pointCycleClassSpan q (H.cycleClass q) :=
    (mem_AlgebraicHodgeSubspace_iff
      (V := V) (H := H) (p := q) alpha).mp halpha
  have hstable :
      ambientUniversalTwoSlotWord (V := V) (H := H) (p := q) i j alpha.1 ∈
        pointCycleClassSpan q (H.cycleClass q) :=
    (R i j).universalWord_atomicStable alpha.1 hspan
  rw [ambientUniversalTwoSlotWord_on_hodge
    (V := V) (H := H) (p := q) i j alpha] at hstable
  have hmatrix :
      hodgeMatrixUnit i j alpha ∈ AlgebraicHodgeSubspace V H q :=
    (mem_AlgebraicHodgeSubspace_iff
      (V := V) (H := H) (p := q) (hodgeMatrixUnit i j alpha)).mpr hstable
  rw [← rankFreeMatrixUnit_eq_lifted_GST_word i j]
  exact hmatrix

/-- A single genuine codimension point gives a nonzero element of the actual
algebraic Hodge subspace.  Nonvanishing is derived from positive projective
degree; it is not postulated. -/
theorem algebraicHodgeSubspace_ne_bot_of_point_geometry
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (q : Nat)
    (x : CodimensionPoint V.X q) :
    AlgebraicHodgeSubspace V H q ≠ ⊥ := by
  let alpha : ClassicalHodgeFiber V H q :=
    ⟨H.cycleClass q (codimensionPointCycle V.X q x),
      G.algebraic_is_hodge q (codimensionPointCycle V.X q x)⟩
  have hspan :
      H.cycleClass q (codimensionPointCycle V.X q x) ∈
        pointCycleClassSpan q (H.cycleClass q) := by
    apply Submodule.subset_span
    exact ⟨x, rfl⟩
  have hmem : alpha ∈ AlgebraicHodgeSubspace V H q :=
    (mem_AlgebraicHodgeSubspace_iff
      (V := V) (H := H) (p := q) alpha).mpr hspan
  intro hbot
  rw [hbot] at hmem
  have halpha0 : alpha = 0 := by
    simpa using hmem
  have hclass0 :
      H.cycleClass q (codimensionPointCycle V.X q x) = 0 := by
    have hval := congrArg Subtype.val halpha0
    simpa [alpha] using hval
  exact pointCycleClass_ne_zero_of_spine_degreeTrace G D q x hclass0

/-- **OCCUPIED-STRATUM UNIVERSAL SATURATION.**

One genuine projective point supplies the nonzero algebraic seed.  Primitive
native geometry supplies the universal two-slot transport.  The rank-free
irreducibility theorem then forces the algebraic Hodge subspace to be the
entire rational `(q,q)` Hodge fiber. -/
theorem occupied_stratum_algebraicHodgeSubspace_eq_top
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (q : Nat)
    (x : CodimensionPoint V.X q)
    (R : ∀ i j : ClassicalHodgeBasisIndex V H q,
      PrimitiveNativeTwoSlot (V := V) (H := H) (p := q) i j) :
    AlgebraicHodgeSubspace V H q = ⊤ := by
  exact algebraicHodgeSubspace_eq_top_of_twoSlot
    (V := V) (H := H) (p := q)
    (algebraicHodgeSubspace_twoSlotInvariant_of_native_geometry R)
    (algebraicHodgeSubspace_ne_bot_of_point_geometry G D q x)

/-- **UNIVERSAL LIMITLESS CYCLE-GEOMETRY FINALE.**

For genuine cycle-class semantics, positive projective degree, geometric
occupancy of every nonzero Hodge stratum, and the three primitive native
point-lift laws of the one universal two-slot machine, every rational `(p,p)`
Hodge class is represented by an actual codimension-p algebraic cycle.

The theorem does not quantify over an unconstrained raw cycle-class map: the
geometric hypotheses are precisely the laws that exclude the repository's
zero-map countermodel and make the universal GST transport act on the genuine
native cycle span. -/
theorem universal_limitless_cycle_geometry_finale
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (hoccupied : HodgeStratumOccupancy V H)
    (R : UniversalNativeTwoSlotGeometry V H) :
    BigradedBettiHodgeStatement V H := by
  apply bigradedBettiHodge_of_universalTwoSlot V H
  · intro q
    exact algebraicHodgeSubspace_twoSlotInvariant_of_native_geometry
      (R q)
  · intro q hH
    obtain ⟨x⟩ := hoccupied q hH
    exact algebraicHodgeSubspace_ne_bot_of_point_geometry G D q x

/-- The same finale exposed as the exact atomic-span statement: every rational
Hodge subspace is contained in the span of genuine projective point-cycle
classes. -/
theorem universal_limitless_atomic_span_crown
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (hoccupied : HodgeStratumOccupancy V H)
    (R : UniversalNativeTwoSlotGeometry V H) :
    ∀ q : Nat,
      rationalHodgeSubspace (H.hodgeBigrading q) ≤
        pointCycleClassSpan q (H.cycleClass q) := by
  exact (bigradedBettiHodgeStatement_iff_atomic_span V H).mp
    (universal_limitless_cycle_geometry_finale G D hoccupied R)

#check HodgeStratumOccupancy
#check UniversalNativeTwoSlotGeometry
#check algebraicHodgeSubspace_twoSlotInvariant_of_native_geometry
#check algebraicHodgeSubspace_ne_bot_of_point_geometry
#check occupied_stratum_algebraicHodgeSubspace_eq_top
#check universal_limitless_cycle_geometry_finale
#check universal_limitless_atomic_span_crown

#print axioms algebraicHodgeSubspace_twoSlotInvariant_of_native_geometry
#print axioms algebraicHodgeSubspace_ne_bot_of_point_geometry
#print axioms occupied_stratum_algebraicHodgeSubspace_eq_top
#print axioms universal_limitless_cycle_geometry_finale
#print axioms universal_limitless_atomic_span_crown

end GSTClassicalHodgeUniversalLimitlessCycleGeometryFinale
