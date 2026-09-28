import GSTClassicalHodgeMinimalGhostAutomaticProjector
import GSTClassicalHodgeNativeGeneratorNaturality
import GSTClassicalHodgeAtomicOperatorAlgebra

/-!
# GST CLASSICAL HODGE — MINIMAL GHOST NATIVE-ORBIT ANNIHILATION

The least-weight separator does more than forbid one chosen crossing.  Because
it annihilates the complete algebraic Hodge subspace, every ambient operator
which admits genuine native point lifts sends every algebraic Hodge source
back into the separator kernel.

Thus a hypothetical minimal ghost imposes a universal conservation law on the
entire independently native-natural operator algebra:

  algebraic source -> native-natural orbit -> ghost value zero.

This isolates the final contradiction mechanism.  To kill the ghost it is no
longer necessary to build a complete matrix-unit realization.  Any geometric
operator algebra whose orbit of one algebraic source meets the detected sheet,
or whose restriction to the relevant primitive quotient is irreducible, is
incompatible with the ghost conservation law.
-/

set_option maxHeartbeats 90000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeMinimalGhostNativeOrbitAnnihilation

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
open GSTClassicalHodgePrimitiveAlgebraicDefect
open GSTClassicalHodgeMinimalGhostAutomaticProjector

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

abbrev AmbientCoh
    (H : HodgeBigradedBettiData V) (p : Nat) :=
  RationalSingularCohomology H.analytification (2 * p)

/-- Every native-natural ambient operator sends every algebraic Hodge source
into the kernel of the minimal separator. -/
theorem minimalGhost_annihilates_nativeNatural_image
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    (T : AmbientCoh H M.weight →ₗ[ℚ] AmbientCoh H M.weight)
    (hT : HasNativePointLifts
      (p := M.weight) (cl := H.cycleClass M.weight) T)
    (alpha : ClassicalHodgeFiber V H M.weight)
    (halpha : alpha ∈ AlgebraicHodgeSubspace V H M.weight) :
    M.separator.detector (T alpha.1) = 0 := by
  have hstable : AtomicSpanStable
      (p := M.weight) (cl := H.cycleClass M.weight) T :=
    (smoothProjective_atomicStable_iff_nativePointLifts
      (V := V) (H := H) (p := M.weight) T).2 hT
  have himage :
      T alpha.1 ∈ pointCycleClassSpan M.weight (H.cycleClass M.weight) :=
    hstable alpha.1 halpha
  have hker :
      pointCycleClassSpan M.weight (H.cycleClass M.weight) ≤
        LinearMap.ker M.separator.detector :=
    (annihilatesPointCycles_iff_atomicSpan_le_ker
      M.weight (H.cycleClass M.weight) M.separator.detector).mp
      M.separator.annihilates_atoms
  exact hker himage

/-- Orbit form: every member of any family of independently native-natural
operators is ghost-invisible on every algebraic source. -/
theorem minimalGhost_annihilates_nativeNatural_family
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    {ι : Type*}
    (T : ι → AmbientCoh H M.weight →ₗ[ℚ] AmbientCoh H M.weight)
    (hT : ∀ a : ι,
      HasNativePointLifts
        (p := M.weight) (cl := H.cycleClass M.weight) (T a))
    (alpha : ClassicalHodgeFiber V H M.weight)
    (halpha : alpha ∈ AlgebraicHodgeSubspace V H M.weight) :
    ∀ a : ι, M.separator.detector (T a alpha.1) = 0 := by
  intro a
  exact minimalGhost_annihilates_nativeNatural_image G M
    (T a) (hT a) alpha halpha

/-- If one native-natural orbit element has a nonzero component purely in the
detected sheet, the minimal ghost is impossible.  This recovers the one-crossing
criterion from the universal orbit law. -/
theorem minimalGhost_false_of_nativeNatural_detected_image
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    (T : AmbientCoh H M.weight →ₗ[ℚ] AmbientCoh H M.weight)
    (hT : HasNativePointLifts
      (p := M.weight) (cl := H.cycleClass M.weight) T)
    (alpha : ClassicalHodgeFiber V H M.weight)
    (halpha : alpha ∈ AlgebraicHodgeSubspace V H M.weight)
    (c : ℚ) (hc : c ≠ 0)
    (himage : T alpha.1 =
      c • (classicalHodgeBasis V H M.weight M.sheet).1) : False := by
  have hzero :=
    minimalGhost_annihilates_nativeNatural_image G M T hT alpha halpha
  rw [himage, LinearMap.map_smul] at hzero
  exact (smul_ne_zero hc M.separator.detects_basis) hzero

/-- The automatically derived ghost projector belongs to the same
native-natural algebra and, consistently, kills every algebraic source. -/
theorem minimalGhost_projector_is_conserved_native_operator
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    (alpha : ClassicalHodgeFiber V H M.weight)
    (halpha : alpha ∈ AlgebraicHodgeSubspace V H M.weight) :
    M.separator.detector
      (minimalGhostAmbientProjector G M alpha.1) = 0 := by
  exact minimalGhost_annihilates_nativeNatural_image G M
    (minimalGhostAmbientProjector G M)
    (minimalGhostAmbientProjector_hasNativePointLifts G M)
    alpha halpha

/-- **NATIVE-ORBIT CONSERVATION CROWN.**  A surviving minimal ghost forces its
separator detector to vanish on the full orbit of every algebraic Hodge source
under every independently native-natural ambient operator. -/
theorem minimalGhost_nativeOrbit_conservation_crown
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G) :
    ∀ (T : AmbientCoh H M.weight →ₗ[ℚ] AmbientCoh H M.weight),
      HasNativePointLifts
        (p := M.weight) (cl := H.cycleClass M.weight) T →
      ∀ alpha : ClassicalHodgeFiber V H M.weight,
        alpha ∈ AlgebraicHodgeSubspace V H M.weight →
          M.separator.detector (T alpha.1) = 0 := by
  intro T hT alpha halpha
  exact minimalGhost_annihilates_nativeNatural_image G M T hT alpha halpha

#check minimalGhost_annihilates_nativeNatural_image
#check minimalGhost_annihilates_nativeNatural_family
#check minimalGhost_false_of_nativeNatural_detected_image
#check minimalGhost_projector_is_conserved_native_operator
#check minimalGhost_nativeOrbit_conservation_crown

#print axioms minimalGhost_annihilates_nativeNatural_image
#print axioms minimalGhost_false_of_nativeNatural_detected_image
#print axioms minimalGhost_nativeOrbit_conservation_crown

end GSTClassicalHodgeMinimalGhostNativeOrbitAnnihilation
