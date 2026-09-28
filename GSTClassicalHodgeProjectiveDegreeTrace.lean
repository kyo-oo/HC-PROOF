import GSTClassicalHodgeSuccessorSeedEscapeDichotomy
import GSTNativeCodimensionCyclePresentation

/-!
# GST CLASSICAL HODGE — PROJECTIVE DEGREE / BETTI TRACE ARTERY

Stage 2F fixes the actual Betti carrier to rational singular cohomology, but the
current semantic package does not yet expose the classical projective degree
pairing.  This file adds exactly that missing geometric artery and nothing
stronger.

For every codimension q there is a rational Betti trace functional obtained in
classical geometry by pairing with a complementary power of an ample
hyperplane class and evaluating on the projective fundamental class.  A unit
cycle supported on an irreducible codimension-q projective subvariety is sent
to its projective degree, which is strictly positive.

We package only these independent degree facts:

* one rational-linear Betti trace in each codimension;
* the projective degree of every native codimension point is positive;
* tracing its genuine cycle class gives exactly that projective degree.

No Hodge-surjectivity, basis representative, matrix-unit naturality, or Hodge
conclusion is stored here.

The payoff is immediate for the geometry-built principal-cut successor.  Its
finite presentation has coefficients 0 or +1.  Hence one exact surviving
successor gives strictly positive projective degree.  By trace compatibility
its Betti cycle class cannot vanish.  The `PositiveCosmicHomologyEscape` from
the preceding reduction is therefore impossible for separator successors once
this standard projective-degree semantics is materialized.
-/

set_option maxHeartbeats 70000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open scoped BigOperators

namespace GSTClassicalHodgeProjectiveDegreeTrace

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgePointClosureRelativeCut
open GSTClassicalHodgePrincipalCutSuccessorOperator
open GSTClassicalHodgeSingleExactSuccessorSurvival
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeSynchronizedDefectOrbit
open GSTClassicalHodgeFiberedCosmology

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Genuine projective degree semantics for the actual Betti cycle-class map.
The intended realization of `trace q` is cup product with a complementary
power of the hyperplane class followed by integration over the projective
fundamental class. -/
structure ProjectiveDegreeTraceSemantics
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) where
  trace : ∀ q : Nat,
    RationalSingularCohomology H.analytification (2 * q) →ₗ[ℚ] ℚ
  pointDegree : ∀ q : Nat, CodimensionPoint V.X q → ℚ
  pointDegree_pos : ∀ q (x : CodimensionPoint V.X q),
    0 < pointDegree q x
  trace_point_cycleClass : ∀ q (x : CodimensionPoint V.X q),
    trace q (H.cycleClass q (codimensionPointCycle V.X q x)) =
      pointDegree q x

namespace ProjectiveDegreeTraceSemantics

/-- Trace of any finite native point presentation is the corresponding
weighted sum of positive projective point-degrees. -/
theorem trace_realize_presentation
    (D : ProjectiveDegreeTraceSemantics V H)
    (q : Nat)
    (φ : FiniteCodimensionPresentation V.X q) :
    D.trace q
        (H.cycleClass q
          (realizeFiniteCodimensionPresentation V.X q φ)) =
      φ.sum (fun x a => a * D.pointDegree q x) := by
  rw [linearMap_realizeFiniteCodimensionPresentation]
  classical
  simp only [map_finsuppSum, LinearMap.map_smul, smul_eq_mul]
  apply Finsupp.sum_congr
  intro x a ha
  rw [D.trace_point_cycleClass]

/-- Trace contribution of one relative successor candidate: exact survivors
contribute their strictly positive projective degree, while wrong ambient
strata contribute zero. -/
theorem trace_successorAtomPresentation
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (y : {y : pointClosureScheme V x.1 // Order.coheight y = 1}) :
    D.trace (p + 1)
      (H.cycleClass (p + 1)
        (realizeFiniteCodimensionPresentation V.X (p + 1)
          (successorAtomPresentation V p x y))) =
      if hy : Order.coheight (ambientSuccessorPoint V x.1 y) = p + 1 then
        D.pointDegree (p + 1)
          (⟨ambientSuccessorPoint V x.1 y, hy⟩ : CodimensionPoint V.X (p + 1))
      else 0 := by
  classical
  by_cases hy : Order.coheight (ambientSuccessorPoint V x.1 y) = p + 1
  · rw [successorAtomPresentation_eq_single V p x y hy]
    simp [D.trace_point_cycleClass, hy]
  · rw [successorAtomPresentation_eq_zero V p x y hy]
    simp [hy]

/-- Exact formula for the Betti trace of the whole geometry-built successor of
one source point atom. -/
theorem trace_successorNativeOperator_point
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat)
    (x : CodimensionPoint V.X p) :
    D.trace (p + 1)
      (H.cycleClass (p + 1)
        (successorNativeOperator V p
          (codimensionPointCycle V.X p x))) =
      ∑ y in relativeCodimensionOneFinset V x.1,
        if hy : Order.coheight (ambientSuccessorPoint V x.1 y) = p + 1 then
          D.pointDegree (p + 1)
            (⟨ambientSuccessorPoint V x.1 y, hy⟩ :
              CodimensionPoint V.X (p + 1))
        else 0 := by
  rw [successorNativeOperator_point]
  rw [trace_realize_presentation D]
  classical
  unfold successorPresentation
  rw [Finsupp.sum_finset_sum]
  apply Finset.sum_congr rfl
  intro y hyMem
  by_cases hy : Order.coheight (ambientSuccessorPoint V x.1 y) = p + 1
  · rw [successorAtomPresentation_eq_single V p x y hy]
    simp [hy]
  · rw [successorAtomPresentation_eq_zero V p x y hy]
    simp [hy]

/-- One exact relative successor forces strictly positive projective Betti
trace for the complete successor cycle because every surviving contribution is
positive and no negative coefficient occurs. -/
theorem trace_successor_positive_of_one_exact
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (y0 : {y : pointClosureScheme V x.1 // Order.coheight y = 1})
    (hy0Mem : y0 ∈ relativeCodimensionOneFinset V x.1)
    (hy0Exact : Order.coheight (ambientSuccessorPoint V x.1 y0) = p + 1) :
    0 < D.trace (p + 1)
      (H.cycleClass (p + 1)
        (successorNativeOperator V p
          (codimensionPointCycle V.X p x))) := by
  rw [trace_successorNativeOperator_point D]
  classical
  apply Finset.sum_pos
  · intro y hy
    by_cases hExact : Order.coheight (ambientSuccessorPoint V x.1 y) = p + 1
    · simp [hExact, le_of_lt (D.pointDegree_pos (p + 1)
        (⟨ambientSuccessorPoint V x.1 y, hExact⟩ :
          CodimensionPoint V.X (p + 1)))]
    · simp [hExact]
  · refine ⟨y0, hy0Mem, ?_⟩
    simp [hy0Exact, D.pointDegree_pos (p + 1)
      (⟨ambientSuccessorPoint V x.1 y0, hy0Exact⟩ :
        CodimensionPoint V.X (p + 1))]

/-- **PROJECTIVE DEGREE EXCLUDES SEPARATOR HOMOLOGY ESCAPE.**
The canonical separator successor cannot have zero genuine Betti cycle class
once its single relative height-one successor is known to have the exact
ambient codimension. -/
theorem separator_successor_cycleClass_ne_zero
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hlive : ProjectivelyLiveSource V.projective.n
      (V.projective.immersion x.1))
    (hExact :
      Order.coheight
        (ambientSuccessorPoint V x.1
          (relativeHeightOneSeparatorSuccessor V x.1 hlive)) = p + 1) :
    H.cycleClass (p + 1)
      (successorNativeOperator V p
        (codimensionPointCycle V.X p x)) ≠ 0 := by
  intro hzero
  have hpos := trace_successor_positive_of_one_exact D p x
    (relativeHeightOneSeparatorSuccessor V x.1 hlive)
    (relativeHeightOneSeparatorSuccessor_mem_finset V x.1 hlive)
    hExact
  rw [hzero, map_zero] at hpos
  exact lt_irrefl 0 hpos

/-- Projective degree upgrades the separator successor directly to the
nonzero algebraic Hodge seed consumed by the synchronized limitless orbit
machine. -/
theorem separator_successor_nativeHodgeSeed
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hlive : ProjectivelyLiveSource V.projective.n
      (V.projective.immersion x.1))
    (hExact :
      Order.coheight
        (ambientSuccessorPoint V x.1
          (relativeHeightOneSeparatorSuccessor V x.1 hlive)) = p + 1) :
    NativeHodgeOrbitSeed (V := V) (H := H) (p := p + 1) := by
  let Z : codimensionCycles V.X (p + 1) :=
    successorNativeOperator V p (codimensionPointCycle V.X p x)
  let alpha : ClassicalHodgeFiber V H (p + 1) :=
    ⟨H.cycleClass (p + 1) Z, G.algebraic_is_hodge (p + 1) Z⟩
  refine {
    cycle := Z
    hodge := alpha
    hodge_ne_zero := ?_
    class_eq := rfl
  }
  intro hz
  have hval : H.cycleClass (p + 1) Z = 0 := congrArg Subtype.val hz
  exact separator_successor_cycleClass_ne_zero D p x hlive hExact
    (by simpa [Z] using hval)

/-- Once the two geometry-first GST primitives are available from that source
sheet, the projective-degree-certified successor closes the entire Hodge
weight p+1. -/
theorem hodge_weight_of_separator_successor
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hlive : ProjectivelyLiveSource V.projective.n
      (V.projective.immersion x.1))
    (hExact :
      Order.coheight
        (ambientSuccessorPoint V x.1
          (relativeHeightOneSeparatorSuccessor V x.1 hlive)) = p + 1)
    (R : ∀ j : ClassicalHodgeBasisIndex V H (p + 1),
      GSTClassicalHodgeGeometryFirstTwoGenerator.GeometryFirstTwoGenerator
        (V := V) (H := H)
        (separator_successor_nativeHodgeSeed G D p x hlive hExact).sourceIndex j) :
    rationalHodgeSubspace (H.hodgeBigrading (p + 1)) ≤
      LinearMap.range (H.cycleClass (p + 1)) := by
  exact (separator_successor_nativeHodgeSeed G D p x hlive hExact).hodge_weight R

#check ProjectiveDegreeTraceSemantics
#check ProjectiveDegreeTraceSemantics.trace_realize_presentation
#check ProjectiveDegreeTraceSemantics.trace_successorNativeOperator_point
#check ProjectiveDegreeTraceSemantics.trace_successor_positive_of_one_exact
#check ProjectiveDegreeTraceSemantics.separator_successor_cycleClass_ne_zero
#check ProjectiveDegreeTraceSemantics.separator_successor_nativeHodgeSeed
#check ProjectiveDegreeTraceSemantics.hodge_weight_of_separator_successor

#print axioms ProjectiveDegreeTraceSemantics.trace_realize_presentation
#print axioms ProjectiveDegreeTraceSemantics.trace_successor_positive_of_one_exact
#print axioms ProjectiveDegreeTraceSemantics.separator_successor_cycleClass_ne_zero
#print axioms ProjectiveDegreeTraceSemantics.separator_successor_nativeHodgeSeed

end ProjectiveDegreeTraceSemantics
end GSTClassicalHodgeProjectiveDegreeTrace
