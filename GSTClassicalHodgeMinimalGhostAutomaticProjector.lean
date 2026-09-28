import GSTClassicalHodgeMinimalGhostSingleTransportExtinction
import GSTClassicalHodgeNativeGeneratorNaturality
import GSTClassicalHodgeAtomicOperatorAlgebra

/-!
# GST CLASSICAL HODGE — AUTOMATIC GHOST PROJECTOR

A least-weight atomic separator carries its own rank-one projector.  If `v` is
the detected Hodge sheet and `ell(v) != 0`, define

  P(x) = ell(x) * ell(v)^(-1) • v.

This operator needs no geometric externalization.  Every genuine algebraic
point-cycle class is annihilated by `ell`, so `P` sends every point-cycle class
to zero.  The zero native cycle therefore gives a canonical native point lift.
On the other hand `P(v)=v` exactly.

Consequently the old two-generator externalization problem collapses even
further at the least bad sheet.  The projector/readout primitive is automatic.
To contradict the ghost one only needs ONE native-natural ambient operator
which sends ONE algebraic Hodge source to a nonzero multiple of the detected
sheet.  No complete matrix-unit word and no code observable realization is
required.
-/

set_option maxHeartbeats 90000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeMinimalGhostAutomaticProjector

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeAtomicAnnihilator
open GSTClassicalHodgeGeneratorwiseAtomicStability
open GSTClassicalHodgeAtomicOperatorAlgebra
open GSTClassicalHodgeNativeGeneratorNaturality
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeMinimalPrimitiveSeparatorGhost
open GSTClassicalHodgeMinimalAlgebraicPrimitiveQuotient
open GSTClassicalHodgePrimitiveAlgebraicDefect

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

abbrev AmbientCoh
    (H : HodgeBigradedBettiData V) (p : Nat) :=
  RationalSingularCohomology H.analytification (2 * p)

/-- Normalized rank-one ambient projector carried canonically by the minimal
separator itself. -/
noncomputable def minimalGhostAmbientProjector
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G) :
    AmbientCoh H M.weight →ₗ[ℚ] AmbientCoh H M.weight :=
  LinearMap.smulRight M.separator.detector
    ((M.separator.detector
      (classicalHodgeBasis V H M.weight M.sheet).1)⁻¹ •
      (classicalHodgeBasis V H M.weight M.sheet).1)

/-- The separator projector fixes the detected Hodge sheet exactly. -/
theorem minimalGhostAmbientProjector_fixes_sheet
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G) :
    minimalGhostAmbientProjector G M
        (classicalHodgeBasis V H M.weight M.sheet).1 =
      (classicalHodgeBasis V H M.weight M.sheet).1 := by
  simp [minimalGhostAmbientProjector, M.separator.detects_basis]

/-- Every genuine point-cycle class is killed by the separator projector. -/
theorem minimalGhostAmbientProjector_point_zero
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    (x : CodimensionPoint V.X M.weight) :
    minimalGhostAmbientProjector G M
        (H.cycleClass M.weight
          (codimensionPointCycle V.X M.weight x)) = 0 := by
  simp [minimalGhostAmbientProjector,
    M.separator.annihilates_atoms x]

/-- **THE GHOST PROJECTOR IS AUTOMATICALLY NATIVE-NATURAL.**
The native lift of every transformed point class is simply the zero cycle. -/
theorem minimalGhostAmbientProjector_hasNativePointLifts
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G) :
    HasNativePointLifts (p := M.weight) (cl := H.cycleClass M.weight)
      (minimalGhostAmbientProjector G M) := by
  intro x
  refine ⟨0, ?_⟩
  rw [LinearMap.map_zero]
  exact (minimalGhostAmbientProjector_point_zero G M x).symm

/-- Hence the canonical separator projector preserves the full atomic
cycle-class span, with no externalization assumption. -/
theorem minimalGhostAmbientProjector_atomicStable
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G) :
    AtomicSpanStable (p := M.weight) (cl := H.cycleClass M.weight)
      (minimalGhostAmbientProjector G M) := by
  exact (smoothProjective_atomicStable_iff_nativePointLifts
    (V := V) (H := H) (p := M.weight)
    (minimalGhostAmbientProjector G M)).2
      (minimalGhostAmbientProjector_hasNativePointLifts G M)

/-- The projector kills every algebraic Hodge class, not merely the point
generators. -/
theorem minimalGhostAmbientProjector_kills_algebraicHodge
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    (alpha : ClassicalHodgeFiber V H M.weight)
    (halpha : alpha ∈ AlgebraicHodgeSubspace V H M.weight) :
    minimalGhostAmbientProjector G M alpha.1 = 0 := by
  have hzero : M.separator.detector alpha.1 = 0 :=
    AlgebraicHodgeSubspace_le_minimalGhostHodgeDetector_kernel G M halpha
  simp [minimalGhostAmbientProjector, hzero]

/-- A single native-natural crossing datum.  This is strictly weaker than a
geometry-first two-generator package: only its action on one algebraic source
is prescribed. -/
structure MinimalGhostNativeCrossing
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G) where
  source : ClassicalHodgeFiber V H M.weight
  source_algebraic : source ∈ AlgebraicHodgeSubspace V H M.weight
  operator : AmbientCoh H M.weight →ₗ[ℚ] AmbientCoh H M.weight
  operator_native :
    HasNativePointLifts (p := M.weight) (cl := H.cycleClass M.weight) operator
  scalar : ℚ
  scalar_ne_zero : scalar ≠ 0
  source_to_target :
    operator source.1 =
      scalar • (classicalHodgeBasis V H M.weight M.sheet).1

/-- **ONE NATIVE CROSSING EXTINCTION.**
No minimal separator ghost can admit even one native-natural operator taking
one algebraic source to a nonzero multiple of its detected sheet. -/
theorem minimalGhost_false_of_nativeCrossing
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    (C : MinimalGhostNativeCrossing G M) : False := by
  have hstable : AtomicSpanStable
      (p := M.weight) (cl := H.cycleClass M.weight) C.operator :=
    (smoothProjective_atomicStable_iff_nativePointLifts
      (V := V) (H := H) (p := M.weight) C.operator).2 C.operator_native
  have himage :
      C.operator C.source.1 ∈
        pointCycleClassSpan M.weight (H.cycleClass M.weight) :=
    hstable C.source.1 C.source_algebraic
  have hker :
      pointCycleClassSpan M.weight (H.cycleClass M.weight) ≤
        LinearMap.ker M.separator.detector :=
    (annihilatesPointCycles_iff_atomicSpan_le_ker
      M.weight (H.cycleClass M.weight) M.separator.detector).mp
      M.separator.annihilates_atoms
  have hzero := hker himage
  rw [C.source_to_target, LinearMap.map_smul] at hzero
  have hnonzero :
      C.scalar •
        M.separator.detector
          (classicalHodgeBasis V H M.weight M.sheet).1 ≠ 0 := by
    exact smul_ne_zero C.scalar_ne_zero M.separator.detects_basis
  exact hnonzero hzero

/-- **SINGLE-CROSSING HODGE CRITERION.**
The complete Stage-2G target follows if every hypothetical minimal ghost admits
one such independently native-natural crossing. -/
theorem bigradedBettiHodge_of_minimalGhost_nativeCrossings
    (G : GeometricCycleClassSpine V H)
    (C : ∀ M : MinimalPrimitiveGhost G,
      Nonempty (MinimalGhostNativeCrossing G M)) :
    BigradedBettiHodgeStatement V H := by
  by_contra hnot
  let M : MinimalPrimitiveGhost G := minimalPrimitiveGhostOfFailure G hnot
  exact minimalGhost_false_of_nativeCrossing G M (C M).some

#check minimalGhostAmbientProjector
#check minimalGhostAmbientProjector_fixes_sheet
#check minimalGhostAmbientProjector_point_zero
#check minimalGhostAmbientProjector_hasNativePointLifts
#check minimalGhostAmbientProjector_atomicStable
#check minimalGhostAmbientProjector_kills_algebraicHodge
#check MinimalGhostNativeCrossing
#check minimalGhost_false_of_nativeCrossing
#check bigradedBettiHodge_of_minimalGhost_nativeCrossings

#print axioms minimalGhostAmbientProjector_fixes_sheet
#print axioms minimalGhostAmbientProjector_hasNativePointLifts
#print axioms minimalGhostAmbientProjector_atomicStable
#print axioms minimalGhostAmbientProjector_kills_algebraicHodge
#print axioms minimalGhost_false_of_nativeCrossing
#print axioms bigradedBettiHodge_of_minimalGhost_nativeCrossings

end GSTClassicalHodgeMinimalGhostAutomaticProjector
