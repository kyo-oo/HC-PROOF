import GSTClassicalHodgeGeometricCycleClassSpine
import GSTClassicalHodgeProjectiveDegreeTrace

/-!
# GST CLASSICAL HODGE — UNIVERSAL LIMITLESS CYCLE GEOMETRY

The raw Stage-2G carrier permits an arbitrary rational-linear `cycleClass` map.
That freedom is not part of the genuine projective geometry.  This module
removes the zero-map ambiguity by deriving, uniformly in every occupied
codimension stratum, concrete nonzero algebraic Hodge classes from the two
independent geometric arteries already formalized in the repository:

* `GeometricCycleClassSpine`: genuine algebraic cycles have Hodge type and the
  projective principal-cut transport is cycle-class natural;
* `ProjectiveDegreeTraceSemantics`: every genuine codimension point has
  strictly positive projective degree, and the Betti trace of its point-cycle
  class is exactly that degree.

No Hodge-surjectivity, target-basis representative, projective visibility,
cosmic matrix-unit realization, or conclusion-equivalent hypothesis occurs in
this file.

The result is a semantic rigidity theorem: once the cycle-class data carries
these independently geometric laws, every genuine codimension point has a
nonzero rational `(p,p)` class in the actual cycle-class range.  Consequently
an occupied stratum can never carry the zero cycle-class map.
-/

set_option maxHeartbeats 60000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open scoped BigOperators
open GSTNativeCodimensionCyclePresentation

namespace GSTClassicalHodgeUniversalLimitlessCycleGeometry

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeProjectiveDegreeTrace
open GSTClassicalHodgeStage2GSemanticRigidity

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/--
The derived universal cycle geometry attached to genuine cycle-class
functoriality and projective-degree trace semantics.

Unlike raw `HodgeBigradedBettiData`, this package records consequences rather
than an unconstrained map: every actual codimension point lands as a nonzero
rational Hodge class in the genuine cycle-class range.
-/
structure UniversalLimitlessCycleGeometry
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) where
  pointClass_hodge :
    ∀ q : Nat, ∀ x : CodimensionPoint V.X q,
      H.cycleClass q (codimensionPointCycle V.X q x) ∈
        rationalHodgeSubspace (H.hodgeBigrading q)
  pointClass_ne_zero :
    ∀ q : Nat, ∀ x : CodimensionPoint V.X q,
      H.cycleClass q (codimensionPointCycle V.X q x) ≠ 0

namespace UniversalLimitlessCycleGeometry

/-- Every genuine point class lies in the actual cycle-class range, by its
explicit native point-cycle witness. -/
theorem pointClass_mem_range
    (U : UniversalLimitlessCycleGeometry V H)
    (q : Nat)
    (x : CodimensionPoint V.X q) :
    H.cycleClass q (codimensionPointCycle V.X q x) ∈
      LinearMap.range (H.cycleClass q) := by
  exact ⟨codimensionPointCycle V.X q x, rfl⟩

/-- Universal elementwise landing: every actual codimension point determines a
nonzero rational `(q,q)` Hodge class which is already the class of an explicit
native algebraic cycle. -/
theorem point_hodge_range_landing
    (U : UniversalLimitlessCycleGeometry V H)
    (q : Nat)
    (x : CodimensionPoint V.X q) :
    ∃ alpha : RationalSingularCohomology H.analytification (2 * q),
      alpha ∈ rationalHodgeSubspace (H.hodgeBigrading q) ∧
      alpha ≠ 0 ∧
      alpha ∈ LinearMap.range (H.cycleClass q) := by
  refine ⟨H.cycleClass q (codimensionPointCycle V.X q x),
    U.pointClass_hodge q x, U.pointClass_ne_zero q x, ?_⟩
  exact U.pointClass_mem_range q x

/-- If a codimension stratum contains an actual point, its genuine cycle-class
linear map cannot be zero. -/
theorem cycleClass_ne_zero_of_nonempty
    (U : UniversalLimitlessCycleGeometry V H)
    (q : Nat)
    (hq : Nonempty (CodimensionPoint V.X q)) :
    H.cycleClass q ≠ 0 := by
  obtain ⟨x⟩ := hq
  intro hzero
  apply U.pointClass_ne_zero q x
  rw [hzero]
  rfl

/-- An occupied codimension stratum has a nontrivial rational Hodge sector. -/
theorem rationalHodgeSubspace_ne_bot_of_nonempty
    (U : UniversalLimitlessCycleGeometry V H)
    (q : Nat)
    (hq : Nonempty (CodimensionPoint V.X q)) :
    rationalHodgeSubspace (H.hodgeBigrading q) ≠ ⊥ := by
  obtain ⟨x⟩ := hq
  intro hbot
  have hmem := U.pointClass_hodge q x
  rw [hbot] at hmem
  have hz : H.cycleClass q (codimensionPointCycle V.X q x) = 0 := by
    simpa using hmem
  exact U.pointClass_ne_zero q x hz

/-- An occupied codimension stratum has a nontrivial genuine algebraic range. -/
theorem cycleClass_range_ne_bot_of_nonempty
    (U : UniversalLimitlessCycleGeometry V H)
    (q : Nat)
    (hq : Nonempty (CodimensionPoint V.X q)) :
    LinearMap.range (H.cycleClass q) ≠ ⊥ := by
  obtain ⟨x⟩ := hq
  intro hbot
  have hmem := U.pointClass_mem_range q x
  rw [hbot] at hmem
  have hz : H.cycleClass q (codimensionPointCycle V.X q x) = 0 := by
    simpa using hmem
  exact U.pointClass_ne_zero q x hz

/-- The raw Stage-2G zero-cycle-class countermodel cannot carry universal
limitless cycle geometry on any occupied codimension stratum. -/
theorem zeroCycleClassData_impossible_of_nonempty
    (H0 : HodgeBigradedBettiData V)
    (q : Nat)
    (hq : Nonempty (CodimensionPoint V.X q)) :
    ¬ Nonempty
      (UniversalLimitlessCycleGeometry V
        (zeroCycleClassData H0)) := by
  rintro ⟨U⟩
  have hne := U.cycleClass_ne_zero_of_nonempty q hq
  exact hne (zeroCycleClassData_cycleClass H0 q)

end UniversalLimitlessCycleGeometry

/-- Positive projective degree makes every genuine point-cycle class nonzero.
This is the key rigidity calculation: zero Betti class would have zero trace,
contradicting the strictly positive projective degree of the point. -/
theorem pointCycleClass_ne_zero_of_spine_degreeTrace
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (q : Nat)
    (x : CodimensionPoint V.X q) :
    H.cycleClass q (codimensionPointCycle V.X q x) ≠ 0 := by
  intro hzero
  have htrace := D.trace_point_cycleClass q x
  have hpos := D.pointDegree_pos q x
  rw [hzero, map_zero] at htrace
  exact (ne_of_gt hpos) htrace.symm

/-- **UNIVERSAL LIMITLESS CYCLE-GEOMETRY CONSTRUCTION.**

The universal semantic package is not assumed.  It is constructed from the
already-formalized genuine cycle-class spine and positive projective-degree
trace geometry. -/
noncomputable def universalLimitlessCycleGeometry
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H) :
    UniversalLimitlessCycleGeometry V H where
  pointClass_hodge := by
    intro q x
    exact G.algebraic_is_hodge q (codimensionPointCycle V.X q x)
  pointClass_ne_zero := by
    intro q x
    exact pointCycleClass_ne_zero_of_spine_degreeTrace G D q x

/-- The theorem form of the construction, convenient for downstream universal
composition. -/
theorem universal_limitless_cycle_geometry
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H) :
    Nonempty (UniversalLimitlessCycleGeometry V H) := by
  exact ⟨universalLimitlessCycleGeometry G D⟩

/-- Global occupied-stratum nonvanishing, derived uniformly from the genuine
spine and degree trace. -/
theorem cycleClass_nonzero_on_every_occupied_stratum
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H) :
    ∀ q : Nat,
      Nonempty (CodimensionPoint V.X q) → H.cycleClass q ≠ 0 := by
  intro q hq
  exact (universalLimitlessCycleGeometry G D).cycleClass_ne_zero_of_nonempty q hq

/-- Every occupied stratum simultaneously contains a nonzero rational Hodge
class and a nonzero algebraic cycle-class range element. -/
theorem occupied_stratum_hodge_and_cycle_range_nontrivial
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H) :
    ∀ q : Nat,
      Nonempty (CodimensionPoint V.X q) →
        rationalHodgeSubspace (H.hodgeBigrading q) ≠ ⊥ ∧
        LinearMap.range (H.cycleClass q) ≠ ⊥ := by
  intro q hq
  let U := universalLimitlessCycleGeometry G D
  exact ⟨U.rationalHodgeSubspace_ne_bot_of_nonempty q hq,
    U.cycleClass_range_ne_bot_of_nonempty q hq⟩

#check UniversalLimitlessCycleGeometry
#check UniversalLimitlessCycleGeometry.point_hodge_range_landing
#check UniversalLimitlessCycleGeometry.cycleClass_ne_zero_of_nonempty
#check UniversalLimitlessCycleGeometry.zeroCycleClassData_impossible_of_nonempty
#check pointCycleClass_ne_zero_of_spine_degreeTrace
#check universalLimitlessCycleGeometry
#check universal_limitless_cycle_geometry
#check cycleClass_nonzero_on_every_occupied_stratum
#check occupied_stratum_hodge_and_cycle_range_nontrivial

#print axioms pointCycleClass_ne_zero_of_spine_degreeTrace
#print axioms universal_limitless_cycle_geometry
#print axioms cycleClass_nonzero_on_every_occupied_stratum
#print axioms occupied_stratum_hodge_and_cycle_range_nontrivial
#print axioms UniversalLimitlessCycleGeometry.zeroCycleClassData_impossible_of_nonempty


/-- Nonzero effective native presentations have strictly positive Betti trace.
This proves nonvanishing for arbitrary finite positive combinations, not just
for the unit point generators. -/
theorem effective_presentation_trace_pos
    (D : ProjectiveDegreeTraceSemantics V H)
    (q : Nat) (φ : FiniteCodimensionPresentation V.X q)
    (heff : ∀ x, 0 ≤ φ x) (hne : φ ≠ 0) :
    0 < D.trace q
      (H.cycleClass q (realizeFiniteCodimensionPresentation V.X q φ)) := by
  classical
  rw [D.trace_realize_presentation]
  change 0 < ∑ x ∈ φ.support, φ x * D.pointDegree q x
  apply Finset.sum_pos
  · intro x _
    exact mul_nonneg (heff x) (le_of_lt (D.pointDegree_pos q x))
  · obtain ⟨x, hx⟩ := Finsupp.support_nonempty_iff.mpr hne
    refine ⟨x, hx, mul_pos ?_ (D.pointDegree_pos q x)⟩
    exact lt_of_le_of_ne (heff x) (Ne.symm (Finsupp.mem_support_iff.mp hx))

/-- Positive-cone faithfulness: no nonzero effective finite cycle can disappear
under the genuine cycle-class map. -/
theorem effective_presentation_cycleClass_ne_zero
    (D : ProjectiveDegreeTraceSemantics V H)
    (q : Nat) (φ : FiniteCodimensionPresentation V.X q)
    (heff : ∀ x, 0 ≤ φ x) (hne : φ ≠ 0) :
    H.cycleClass q (realizeFiniteCodimensionPresentation V.X q φ) ≠ 0 := by
  intro hz
  have hp := effective_presentation_trace_pos D q φ heff hne
  rw [hz, map_zero] at hp
  exact lt_irrefl 0 hp

/-- An explicit linear native return along the degree-detected cycle direction.
The denominator is computed from the cycle itself. -/
noncomputable def degreeNormalizedReturn
    (D : ProjectiveDegreeTraceSemantics V H)
    (q : Nat) (Z : codimensionCycles V.X q) :
    RationalSingularCohomology H.analytification (2 * q) →ₗ[ℚ]
      codimensionCycles V.X q :=
  LinearMap.smulRight (D.trace q)
    ((D.trace q (H.cycleClass q Z))⁻¹ • Z)

theorem degreeNormalizedReturn_apply
    (D : ProjectiveDegreeTraceSemantics V H)
    (q : Nat) (Z : codimensionCycles V.X q)
    (alpha : RationalSingularCohomology H.analytification (2 * q)) :
    degreeNormalizedReturn D q Z alpha =
      (D.trace q alpha * (D.trace q (H.cycleClass q Z))⁻¹) • Z := by
  simp [degreeNormalizedReturn, smul_smul]

/-- Exact native round-trip, with nonvanishing supplied by the positive-degree
calculation for every nonzero effective cycle. -/
theorem degreeNormalizedReturn_roundTrip
    (D : ProjectiveDegreeTraceSemantics V H)
    (q : Nat) (Z : codimensionCycles V.X q)
    (hz : D.trace q (H.cycleClass q Z) ≠ 0) :
    degreeNormalizedReturn D q Z (H.cycleClass q Z) = Z := by
  rw [degreeNormalizedReturn_apply]
  simp [hz]

/-- The induced native operator is idempotent. -/
theorem degreeNormalizedReturn_native_idempotent
    (D : ProjectiveDegreeTraceSemantics V H)
    (q : Nat) (Z : codimensionCycles V.X q)
    (hz : D.trace q (H.cycleClass q Z) ≠ 0)
    (W : codimensionCycles V.X q) :
    degreeNormalizedReturn D q Z
        (H.cycleClass q (degreeNormalizedReturn D q Z (H.cycleClass q W))) =
      degreeNormalizedReturn D q Z (H.cycleClass q W) := by
  let c := D.trace q (H.cycleClass q W) *
    (D.trace q (H.cycleClass q Z))⁻¹
  have hw : degreeNormalizedReturn D q Z (H.cycleClass q W) = c • Z :=
    degreeNormalizedReturn_apply D q Z _
  rw [hw, map_smul, map_smul, degreeNormalizedReturn_roundTrip D q Z hz]

/-- The remainder after the explicit return has zero degree trace.
This is a decomposition into a detected algebraic direction and a trace-zero
remainder; it does not assert that the remainder itself vanishes. -/
theorem degreeNormalizedReturn_trace_remainder
    (D : ProjectiveDegreeTraceSemantics V H)
    (q : Nat) (Z : codimensionCycles V.X q)
    (hz : D.trace q (H.cycleClass q Z) ≠ 0)
    (alpha : RationalSingularCohomology H.analytification (2 * q)) :
    D.trace q
      (alpha - H.cycleClass q (degreeNormalizedReturn D q Z alpha)) = 0 := by
  rw [degreeNormalizedReturn_apply, map_sub, map_smul, map_smul]
  simp [smul_eq_mul, mul_assoc, hz]

/-- Universal effective-cycle crown: positive trace, a nonzero algebraic Hodge
class, and an explicit native round-trip all hold simultaneously. -/
theorem universal_effective_cycle_geometry
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (q : Nat) (φ : FiniteCodimensionPresentation V.X q)
    (heff : ∀ x, 0 ≤ φ x) (hne : φ ≠ 0) :
    let Z := realizeFiniteCodimensionPresentation V.X q φ
    0 < D.trace q (H.cycleClass q Z) ∧
    H.cycleClass q Z ≠ 0 ∧
    H.cycleClass q Z ∈ rationalHodgeSubspace (H.hodgeBigrading q) ∧
    degreeNormalizedReturn D q Z (H.cycleClass q Z) = Z := by
  dsimp only
  have hp := effective_presentation_trace_pos D q φ heff hne
  exact ⟨hp, effective_presentation_cycleClass_ne_zero D q φ heff hne,
    G.algebraic_is_hodge q _,
    degreeNormalizedReturn_roundTrip D q _ (ne_of_gt hp)⟩

#print axioms effective_presentation_trace_pos
#print axioms effective_presentation_cycleClass_ne_zero
#print axioms degreeNormalizedReturn_roundTrip
#print axioms degreeNormalizedReturn_native_idempotent
#print axioms degreeNormalizedReturn_trace_remainder
#print axioms universal_effective_cycle_geometry

end GSTClassicalHodgeUniversalLimitlessCycleGeometry
