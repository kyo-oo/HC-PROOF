import GSTGeometricRealizationStage2G
import GSTNativeCodimensionCyclePresentation

/-!
# Projective degree semantics and finite-cycle trace

The semantic data and its finite-presentation trace formula are independent of
separator survival and the operator-generation arguments. Their declaration
names remain in the existing projective-degree namespace.
-/

noncomputable section
open AlgebraicGeometry
open scoped BigOperators

namespace GSTClassicalHodgeProjectiveDegreeTrace
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation

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
  intro x _
  rw [D.trace_point_cycleClass]


end ProjectiveDegreeTraceSemantics
end GSTClassicalHodgeProjectiveDegreeTrace
