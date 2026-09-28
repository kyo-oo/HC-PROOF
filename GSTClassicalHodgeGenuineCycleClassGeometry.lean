import GSTClassicalHodgeGeometricCycleClassSpine
import GSTClassicalHodgeProjectiveDegreeTrace
import GSTClassicalHodgeProjectiveCorrespondenceCosmicRealization
import GSTClassicalHodgeStage2GSemanticRigidity
import GSTClassicalHodgeFiberedCosmology

/-!
# GST CLASSICAL HODGE — GENUINE CYCLE-CLASS GEOMETRY

The raw Stage-2G carrier stores `cycleClass` as an arbitrary rational-linear
map.  The repository's semantic-rigidity audit therefore admits the zero-map
countermodel, and even the older geometric spine survives that countermodel.

The genuinely geometric foundation isolated here is intentionally smaller and
noncircular:

* the established geometric cycle-class spine;
* positive projective-degree / Betti-trace semantics.

These laws already exclude the zero cycle-class map and prove nonvanishing of
actual point-cycle classes.  They do **not** assert horizontal Hodge
surjectivity, projective detector visibility, a target basis representative,
or an exact GST matrix-unit action.

A stronger projective-orbit irreducibility principle is defined separately in
this module as an explicit *closure certificate*.  Downstream files may study
what it would imply, but it is not a field of `GenuineCycleClassGeometry` and
must not be confused with independently constructed geometry.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeGenuineCycleClassGeometry

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeProjectiveDegreeTrace
open GSTClassicalHodgeProjectiveCorrespondenceAlgebra
open GSTClassicalHodgeProjectiveCorrespondenceCosmicRealization
open GSTClassicalHodgeStage2GSemanticRigidity

/--
Independently geometric Stage-2G strengthening used by the Hodge landing.

No field mentions arbitrary Hodge basis algebraicity or projective visibility.
The positive projective-degree law is enough to make the zero-map semantic
countermodel impossible whenever an actual codimension point exists.
-/
structure GenuineCycleClassGeometry
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) extends
      GeometricCycleClassSpine V H,
      ProjectiveDegreeTraceSemantics V H

namespace GenuineCycleClassGeometry

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Explicit projection to the previously verified geometric-spine interface. -/
abbrev spine (J : GenuineCycleClassGeometry V H) :
    GeometricCycleClassSpine V H :=
  J.toGeometricCycleClassSpine

/-- Explicit projection to positive projective-degree / Betti-trace semantics. -/
abbrev degreeTrace (J : GenuineCycleClassGeometry V H) :
    ProjectiveDegreeTraceSemantics V H :=
  J.toProjectiveDegreeTraceSemantics

/-- Every genuine codimension point has a nonzero cycle class. -/
theorem point_cycleClass_ne_zero
    (J : GenuineCycleClassGeometry V H)
    (q : Nat)
    (x : CodimensionPoint V.X q) :
    H.cycleClass q (codimensionPointCycle V.X q x) ≠ 0 := by
  intro hzero
  have htrace := J.degreeTrace.trace_point_cycleClass q x
  have hpos := J.degreeTrace.pointDegree_pos q x
  rw [hzero, map_zero] at htrace
  exact (ne_of_gt hpos) htrace.symm

/--
**ZERO-MAP EXCLUSION.**  As soon as the projective carrier has one genuine
codimension-q point, the Stage-2G package obtained by replacing cycle class by
zero cannot carry `GenuineCycleClassGeometry`.

Only the positive projective-degree trace is used; no Hodge-surjectivity or
basis realization occurs in the proof.
-/
theorem not_nonempty_zeroCycleClassData
    (H : HodgeBigradedBettiData V)
    (q : Nat)
    (x : CodimensionPoint V.X q) :
    ¬ Nonempty
      (GenuineCycleClassGeometry V
        (GSTClassicalHodgeStage2GSemanticRigidity.zeroCycleClassData H)) := by
  rintro ⟨J⟩
  have htrace := J.degreeTrace.trace_point_cycleClass q x
  have hpos := J.degreeTrace.pointDegree_pos q x
  have hzero :
      J.degreeTrace.trace q
        ((GSTClassicalHodgeStage2GSemanticRigidity.zeroCycleClassData H).cycleClass q
          (codimensionPointCycle V.X q x)) = 0 := by
    simp [GSTClassicalHodgeStage2GSemanticRigidity.zeroCycleClassData]
  rw [hzero] at htrace
  exact (ne_of_gt hpos) htrace.symm

/-- Stronger map-level form: a genuine geometry certificate forces the cycle
class linear map to be nonzero in every codimension which contains a point. -/
theorem cycleClass_ne_zero
    (J : GenuineCycleClassGeometry V H)
    (q : Nat)
    (x : CodimensionPoint V.X q) :
    H.cycleClass q ≠ 0 := by
  intro hmap
  apply J.point_cycleClass_ne_zero q x
  rw [hmap]
  rfl

end GenuineCycleClassGeometry

/--
**EXPLICIT HORIZONTAL CLOSURE CERTIFICATE.**

This principle is intentionally *not* part of `GenuineCycleClassGeometry`.
It says that every nonzero algebraic source has projective orbit visible to any
linear detector which sees a rational Hodge state.  Combined with the native
spine and omniversal-ghost machinery, it is strong enough to imply Hodge; the
visibility-equivalence audit therefore prevents treating it as a free
geometric axiom.

The purpose of keeping it as a separate structure is to expose the exact
remaining theorem that a future independent classical/GST geometric argument
would have to construct.
-/
structure ProjectiveOrbitIrreducibility
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (J : GenuineCycleClassGeometry V H) where
  separates :
    ∀ (p : Nat)
      (Z : codimensionCycles V.X p),
      H.cycleClass p Z ≠ 0 →
      ∀ (alpha : ClassicalHodgeFiber V H p)
        (detector :
          RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ] ℚ),
        detector alpha.1 ≠ 0 →
        ∃ K : ProjectiveNativeKernel V p,
          detector
            ((projectiveCorrespondencePair J.spine K).cohomologyOperator
              (H.cycleClass p Z)) ≠ 0

#check GenuineCycleClassGeometry
#check GenuineCycleClassGeometry.spine
#check GenuineCycleClassGeometry.degreeTrace
#check GenuineCycleClassGeometry.point_cycleClass_ne_zero
#check GenuineCycleClassGeometry.not_nonempty_zeroCycleClassData
#check GenuineCycleClassGeometry.cycleClass_ne_zero
#check ProjectiveOrbitIrreducibility

#print axioms GenuineCycleClassGeometry.point_cycleClass_ne_zero
#print axioms GenuineCycleClassGeometry.not_nonempty_zeroCycleClassData
#print axioms GenuineCycleClassGeometry.cycleClass_ne_zero

end GSTClassicalHodgeGenuineCycleClassGeometry
