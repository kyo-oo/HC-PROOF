import GSTClassicalHodgeGeometricCycleClassSpine
import GSTClassicalHodgeProjectiveDegreeTrace
import GSTClassicalHodgeProjectiveCorrespondenceCosmicRealization
import GSTClassicalHodgeStage2GSemanticRigidity
import GSTClassicalHodgeFiberedCosmology

/-!
# GST CLASSICAL HODGE — GENUINE CYCLE-CLASS GEOMETRY

The Stage-2G carrier deliberately leaves `cycleClass` as a rational-linear map.
That freedom is useful for semantic audits, but it is too weak for the final
classical landing: the existing zero-map countermodel keeps the Hodge bigrading
and even satisfies the old geometric spine.

This module introduces a stronger *geometric* semantic layer.  It keeps the
already-proved projective spine and positive projective-degree trace, and adds
one global projective-orbit irreducibility law:

* start from any nonzero genuine algebraic cycle class in one Hodge weight;
* take any rational detector which is genuinely nonzero on some rational
  Hodge state in that weight;
* then some operator in the rational span of actual projective self-transports
  has nonzero detector response on that algebraic source.

The law is intentionally much broader than a basis-cycle bridge or a matrix
unit realization.  It stores neither a target basis cycle nor an exact GST
operator action.  It is a cosmological irreducibility statement for the whole
projective correspondence representation.  The downstream tomography layer
will use only one scalar consequence of it.

The positive projective-degree component independently rules out the zero-map
semantic countermodel before any Hodge-closure argument is invoked.
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
Projective-orbit irreducibility at the genuine cohomological level.

This is deliberately detector-based rather than basis-based.  No basis vector
is required to be algebraic and no exact Hodge operator is prescribed.  The
law says that a detector which sees *some* rational Hodge state cannot vanish
on the entire genuine projective orbit of a nonzero algebraic source.
-/
structure ProjectiveOrbitIrreducibility
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (G : GeometricCycleClassSpine V H) where
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
            ((projectiveCorrespondencePair G K).cohomologyOperator
              (H.cycleClass p Z)) ≠ 0

/--
The strengthened geometric semantic package used by the transformed Hodge
attack.

The first two parents are existing independently developed geometry.  The
third field is the new limitless projective-orbit irreducibility law.  It does
not change `HodgeBigradedBettiData`; instead it certifies that a particular
Stage-2G package is attached to the stronger genuine geometry.
-/
structure GenuineCycleClassGeometry
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) extends
      GeometricCycleClassSpine V H,
      ProjectiveDegreeTraceSemantics V H where
  projectiveOrbitIrreducibility :
    ProjectiveOrbitIrreducibility V H toGeometricCycleClassSpine

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

/-- Explicit projection to the new projective-orbit irreducibility law. -/
abbrev orbitIrreducibility (J : GenuineCycleClassGeometry V H) :
    ProjectiveOrbitIrreducibility V H J.spine :=
  J.projectiveOrbitIrreducibility

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

#check ProjectiveOrbitIrreducibility
#check GenuineCycleClassGeometry
#check GenuineCycleClassGeometry.spine
#check GenuineCycleClassGeometry.degreeTrace
#check GenuineCycleClassGeometry.orbitIrreducibility
#check GenuineCycleClassGeometry.point_cycleClass_ne_zero
#check GenuineCycleClassGeometry.not_nonempty_zeroCycleClassData
#check GenuineCycleClassGeometry.cycleClass_ne_zero

#print axioms GenuineCycleClassGeometry.point_cycleClass_ne_zero
#print axioms GenuineCycleClassGeometry.not_nonempty_zeroCycleClassData
#print axioms GenuineCycleClassGeometry.cycleClass_ne_zero

end GSTClassicalHodgeGenuineCycleClassGeometry
