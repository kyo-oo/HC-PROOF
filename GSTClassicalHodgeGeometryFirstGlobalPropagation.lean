import GSTClassicalHodgeGradedNativeCohomologyRealization
import GSTClassicalHodgeGeometryFirstTwoGenerator
import GSTClassicalHodgeNativePointSeedSaturation
import GSTClassicalHodgeCrossWeightNativePropagation

/-!
# GST CLASSICAL HODGE — GEOMETRY-FIRST GLOBAL PROPAGATION

The fixed-weight limitless arsenal needs only one nonzero algebraic Hodge seed
per weight.  The cross-weight Lefschetz mechanism shows those seeds should not
be independent.  This file makes that mechanism geometry-first as well.

A native graded cycle operator is primary.  Graded kernel stability produces
its genuine ambient Betti action automatically.  If that derived action sends
a chosen source Hodge seed to the exact nonzero GST Lefschetz scalar times a
target Hodge seed, algebraicity propagates to the target by applying the
native cycle operator and dividing by the scalar.

Consequently one actual native point seed in weight zero, a chain of genuine
native graded Lefschetz transports, and the two geometry-first fixed-weight
primitives are enough to saturate every Hodge fiber.  No independent seed in
higher weight and no independently supplied graded cohomology operator remain.
-/

set_option maxHeartbeats 40000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeCrossWeightNativePropagation
open GSTClassicalHodgeGradedNativeCohomologyRealization
open GSTClassicalHodgeGeometryFirstTwoGenerator
open GSTClassicalHodgeNativePointSeedSaturation

namespace GSTClassicalHodgeGeometryFirstGlobalPropagation

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- One geometry-first graded Lefschetz step.  The Betti action is generated
from the native cycle operator rather than supplied separately. -/
structure GeometryFirstLefschetzStep
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p q : Nat) where
  hpq : p ≤ q
  cycleOperator :
    codimensionCycles V.X p →ₗ[ℚ] codimensionCycles V.X q
  kernelStable :
    GradedKernelStable (H := H) cycleOperator
  source : ClassicalHodgeFiber V H p
  target : ClassicalHodgeFiber V H q
  source_ne_zero : source ≠ 0
  target_ne_zero : target ≠ 0
  transport_formula :
    gradedAmbientOperator cycleOperator kernelStable source.1 =
      limitlessLefschetzScalar p q • target.1

namespace GeometryFirstLefschetzStep

variable {p q : Nat}

/-- The complete graded cycle/cohomology pair generated from the native step. -/
noncomputable def operatorPair
    (T : GeometryFirstLefschetzStep V H p q) :
    GradedCycleClassOperatorPair V H p q :=
  toGradedCycleClassOperatorPair T.cycleOperator T.kernelStable

/-- Normalize the native transport by the exact nonzero limitless Lefschetz
coefficient. -/
noncomputable def targetCycle
    (T : GeometryFirstLefschetzStep V H p q)
    (Z : codimensionCycles V.X p) :
    codimensionCycles V.X q :=
  (limitlessLefschetzScalar p q)⁻¹ • T.cycleOperator Z

/-- Exact target class produced from one source native representative. -/
theorem targetCycle_spec
    (T : GeometryFirstLefschetzStep V H p q)
    (Z : codimensionCycles V.X p)
    (hZ : H.cycleClass p Z = T.source.1) :
    H.cycleClass q (T.targetCycle Z) = T.target.1 := by
  unfold targetCycle
  rw [LinearMap.map_smul]
  rw [← cycleClass_gradedAmbientOperator
    (H := H) T.cycleOperator T.kernelStable Z]
  rw [hZ, T.transport_formula]
  simp [limitlessLefschetzScalar_ne_zero]

/-- Algebraicity propagates through the geometry-first graded step. -/
theorem target_mem_algebraic_of_source
    (T : GeometryFirstLefschetzStep V H p q)
    (hsource : T.source ∈ AlgebraicHodgeSubspace V H p) :
    T.target ∈ AlgebraicHodgeSubspace V H q := by
  have hrange : T.source.1 ∈ LinearMap.range (H.cycleClass p) := by
    have hatomic : T.source.1 ∈ pointCycleClassSpan p (H.cycleClass p) := hsource
    rwa [← smoothProjective_cycleClass_range_eq_atomic_span V H p] at hatomic
  rcases hrange with ⟨Z, hZ⟩
  have htarget : T.target.1 ∈ LinearMap.range (H.cycleClass q) :=
    ⟨T.targetCycle Z, T.targetCycle_spec Z hZ⟩
  rw [smoothProjective_cycleClass_range_eq_atomic_span V H q] at htarget
  exact htarget

end GeometryFirstLefschetzStep

/-- A single seed family propagated from weight to weight by native graded
Lefschetz operators whose Betti action is derived automatically. -/
structure GeometryFirstSeedPropagation
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) where
  seed : ∀ p : Nat, ClassicalHodgeFiber V H p
  seed_ne_zero : ∀ p : Nat, seed p ≠ 0
  step : ∀ p : Nat, GeometryFirstLefschetzStep V H p (p + 1)
  step_source : ∀ p : Nat, (step p).source = seed p
  step_target : ∀ p : Nat, (step p).target = seed (p + 1)

namespace GeometryFirstSeedPropagation

/-- Algebraicity of the initial seed propagates through every weight. -/
theorem seed_mem_algebraic_of_zero
    (F : GeometryFirstSeedPropagation V H)
    (h0 : F.seed 0 ∈ AlgebraicHodgeSubspace V H 0) :
    ∀ p : Nat, F.seed p ∈ AlgebraicHodgeSubspace V H p := by
  intro p
  induction p with
  | zero => exact h0
  | succ p ih =>
      have hnext := (F.step p).target_mem_algebraic_of_source
        (by simpa [F.step_source p] using ih)
      simpa [F.step_target p] using hnext

end GeometryFirstSeedPropagation

/-- Complete geometry-first limitless package:

* one actual native point seed in weight zero;
* one native graded Lefschetz transport at every successive weight;
* two native fixed-weight primitives for every ordered Hodge-basis pair.

All ambient Betti actions are derived from native cycle operators. -/
structure GeometryFirstGlobalPropagation
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) where
  zeroSeed : NativePointHodgeSeed V H 0
  propagation : GeometryFirstSeedPropagation V H
  zero_seed_eq : propagation.seed 0 = zeroSeed.hodgeClass
  fixedWeight :
    ∀ p : Nat, ∀ i j : ClassicalHodgeBasisIndex V H p,
      GeometryFirstTwoGenerator (V := V) (H := H) i j

namespace GeometryFirstGlobalPropagation

/-- The propagated distinguished seed is algebraic in every weight. -/
theorem seed_mem_algebraic
    (G : GeometryFirstGlobalPropagation V H) :
    ∀ p : Nat,
      G.propagation.seed p ∈ AlgebraicHodgeSubspace V H p := by
  apply G.propagation.seed_mem_algebraic_of_zero
  rw [G.zero_seed_eq]
  exact G.zeroSeed.hodgeClass_mem_algebraicHodgeSubspace

/-- The algebraic Hodge subspace is nonzero in every weight. -/
theorem algebraicHodgeSubspace_ne_bot
    (G : GeometryFirstGlobalPropagation V H)
    (p : Nat) :
    AlgebraicHodgeSubspace V H p ≠ ⊥ := by
  intro hbot
  have hmem := G.seed_mem_algebraic p
  rw [hbot] at hmem
  have hz : G.propagation.seed p = 0 := by simpa using hmem
  exact G.propagation.seed_ne_zero p hz

/-- Rank-free two-generator saturation makes the algebraic Hodge subspace the
whole genuine Hodge fiber in every weight. -/
theorem algebraicHodgeSubspace_eq_top
    (G : GeometryFirstGlobalPropagation V H)
    (p : Nat) :
    AlgebraicHodgeSubspace V H p = ⊤ := by
  exact algebraicHodgeSubspace_eq_top_of_geometryFirstTwoGenerators
    (G.fixedWeight p) (G.algebraicHodgeSubspace_ne_bot p)

/-- Every rational Hodge class acquires an actual native algebraic cycle. -/
theorem every_hodge_class_has_native_cycle
    (G : GeometryFirstGlobalPropagation V H)
    (p : Nat)
    (alpha : ClassicalHodgeFiber V H p) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha.1 := by
  have htop := G.algebraicHodgeSubspace_eq_top p
  have halg : alpha ∈ AlgebraicHodgeSubspace V H p := by
    rw [htop]
    trivial
  have hatomic : alpha.1 ∈ pointCycleClassSpan p (H.cycleClass p) := halg
  rw [← smoothProjective_cycleClass_range_eq_atomic_span V H p] at hatomic
  exact hatomic

/-- **GEOMETRY-FIRST GLOBAL CROWN.** -/
theorem bigradedBettiHodge
    (G : GeometryFirstGlobalPropagation V H) :
    BigradedBettiHodgeStatement V H := by
  intro p alpha halpha
  let alphaH : ClassicalHodgeFiber V H p := ⟨alpha, halpha⟩
  exact G.every_hodge_class_has_native_cycle p alphaH

end GeometryFirstGlobalPropagation

#check GeometryFirstLefschetzStep
#check GeometryFirstLefschetzStep.operatorPair
#check GeometryFirstLefschetzStep.targetCycle
#check GeometryFirstLefschetzStep.targetCycle_spec
#check GeometryFirstSeedPropagation
#check GeometryFirstSeedPropagation.seed_mem_algebraic_of_zero
#check GeometryFirstGlobalPropagation
#check GeometryFirstGlobalPropagation.seed_mem_algebraic
#check GeometryFirstGlobalPropagation.algebraicHodgeSubspace_eq_top
#check GeometryFirstGlobalPropagation.every_hodge_class_has_native_cycle
#check GeometryFirstGlobalPropagation.bigradedBettiHodge

#print axioms GeometryFirstLefschetzStep.targetCycle_spec
#print axioms GeometryFirstLefschetzStep.target_mem_algebraic_of_source
#print axioms GeometryFirstSeedPropagation.seed_mem_algebraic_of_zero
#print axioms GeometryFirstGlobalPropagation.algebraicHodgeSubspace_eq_top
#print axioms GeometryFirstGlobalPropagation.every_hodge_class_has_native_cycle
#print axioms GeometryFirstGlobalPropagation.bigradedBettiHodge

end GSTClassicalHodgeGeometryFirstGlobalPropagation
