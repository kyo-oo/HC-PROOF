import GSTClassicalHodgeSeparatorGenericExact
import GSTClassicalHodgeProjectiveDegreeTrace

/-!
# GST CLASSICAL HODGE — GENERIC SEPARATOR DEGREE SEED

The generic separator exactness theorem removes the ambient-stratum hypothesis
from the first geometric successor step on an irreducible carrier.  This file
pushes that unconditional exactness through the already-independent projective
degree semantics.

For every projectively-live codimension-zero source:

* the canonical separator successor is ambient codimension one;
* the native successor cycle is nonzero;
* its projective Betti trace is strictly positive;
* therefore its genuine Betti cycle class is nonzero;
* consequently it gives a native algebraic Hodge orbit seed in weight one.

No Hodge-surjectivity statement is used.  The only semantic input beyond the
geometric cycle-class spine is the classical projective degree trace law.
-/

set_option maxHeartbeats 70000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgePointClosureRelativeCut
open GSTClassicalHodgePrincipalCutSuccessorOperator
open GSTClassicalHodgeProjectiveDegreeTrace
open GSTClassicalHodgeSeparatorGenericExact

namespace GSTClassicalHodgeGenericSeparatorDegreeSeed

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- The generic separator successor has nonzero genuine Betti class, with no
ambient exactness hypothesis left to supply. -/
theorem generic_separator_successor_cycleClass_ne_zero
    [IrreducibleSpace V.X]
    (D : ProjectiveDegreeTraceSemantics V H)
    (x : CodimensionPoint V.X 0)
    (hlive : ProjectivelyLiveSource V.projective.n
      (V.projective.immersion x.1)) :
    H.cycleClass 1
      (successorNativeOperator V 0
        (codimensionPointCycle V.X 0 x)) ≠ 0 := by
  have hExact := separatorSuccessor_ambient_exact_zero V x hlive
  simpa using D.separator_successor_cycleClass_ne_zero 0 x hlive hExact

/-- **GENERIC GEOMETRIC HODGE SEED.**  Projective degree upgrades the
unconditional generic separator successor to a nonzero native algebraic Hodge
seed in weight one. -/
noncomputable def generic_separator_nativeHodgeSeed
    [IrreducibleSpace V.X]
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (x : CodimensionPoint V.X 0)
    (hlive : ProjectivelyLiveSource V.projective.n
      (V.projective.immersion x.1)) :
    GSTClassicalHodgeSynchronizedDefectOrbit.NativeHodgeOrbitSeed
      (V := V) (H := H) (p := 1) := by
  have hExact := separatorSuccessor_ambient_exact_zero V x hlive
  simpa using D.separator_successor_nativeHodgeSeed G 0 x hlive hExact

/-- Once the existing geometry-first two-generator primitives are available
from this concrete source sheet, the entire rational Hodge weight one is in the
genuine cycle-class range. -/
theorem hodge_weight_one_of_generic_separator
    [IrreducibleSpace V.X]
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (x : CodimensionPoint V.X 0)
    (hlive : ProjectivelyLiveSource V.projective.n
      (V.projective.immersion x.1))
    (R : ∀ j : ClassicalHodgeBasisIndex V H 1,
      GSTClassicalHodgeGeometryFirstTwoGenerator.GeometryFirstTwoGenerator
        (V := V) (H := H)
        (generic_separator_nativeHodgeSeed G D x hlive).sourceIndex j) :
    rationalHodgeSubspace (H.hodgeBigrading 1) ≤
      LinearMap.range (H.cycleClass 1) := by
  have hExact := separatorSuccessor_ambient_exact_zero V x hlive
  simpa using D.hodge_weight_of_separator_successor
    G 0 x hlive hExact R

#check generic_separator_successor_cycleClass_ne_zero
#check generic_separator_nativeHodgeSeed
#check hodge_weight_one_of_generic_separator

#print axioms generic_separator_successor_cycleClass_ne_zero
#print axioms generic_separator_nativeHodgeSeed
#print axioms hodge_weight_one_of_generic_separator

end GSTClassicalHodgeGenericSeparatorDegreeSeed
