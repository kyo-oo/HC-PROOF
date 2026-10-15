import GSTUniversalCodimensionTwoPrimitiveExtraction

/-!
# GST genuine primitive cycle extraction from non-Lefschetz algebraic geometry

The existing all-dimensional codimension-two theorem constructs a
primitive remainder of an arbitrary rational Hodge class and the
native codimension-two cycle realizing its nonprimitive correction.

This module closes a mathematical weakness in that formulation:
real Hard Lefschetz is an ISOMORPHISM, but the earlier structural
interface demanded only surjectivity. Adding its standard
injectivity gives a canonical primitive projector:
  P(alpha) = alpha - h cup (L^(d-2))^(-1)(L^(d-3) alpha).

PROVEN NEW THEOREM: for any actual native algebraic codimension-two
cycle Z, its corrected native cycle P_native(Z) is a NONZERO
ALGEBRAIC PRIMITIVE class if and only if cl(Z) lies outside
the h-cup image of rational Hodge divisors.

This produces nonzero algebraic primitive classes from explicit
geometric incidence cycles *without assuming any primitive
class is already algebraic*. It does not imply that ALL primitive
rational Hodge classes are represented by such Z. The latter
universal surjectivity remains the Hodge conjecture problem.
-/

set_option maxHeartbeats 20000000
noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeGeometricMatrixRankLanding
open GSTUniversalLefschetzCurveCycles
open GSTUniversalCodimensionTwoPrimitiveExtraction

namespace GSTPrimitiveTransverseCycleExtraction

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {d : Nat}

/-- The algebraic correction always belongs to the genuine
hyperplane-times-divisor Hodge image, with its exact Lefschetz
test value prescribed by alpha. -/
theorem correction_is_cup_of_real_divisor
    (G : GeometricCycleClassSpine V H)
    (P : GeometricHigherLefschetzData G d)
    (h11 : DivisorsRepresentHodge11 H)
    (alpha : ClassicalHodgeFiber V H 2) :
    ∃ beta : ClassicalHodgeFiber V H 1,
      nativeToHodgeFiberLinear G
        (algebraicLefschetzCorrection G P h11 alpha) =
        P.cupH beta ∧
      P.cupH2 beta = P.primitiveTest alpha := by
  let beta : ClassicalHodgeFiber V H 1 :=
    Classical.choose (P.hardLefschetz (P.primitiveTest alpha))
  let D : codimensionCycles V.X 1 :=
    Classical.choose (h11 beta)
  have hD : nativeToHodgeFiberLinear G D = beta := by
    apply Subtype.ext
    exact Classical.choose_spec (h11 beta)
  refine ⟨beta, ?_, Classical.choose_spec (P.hardLefschetz (P.primitiveTest alpha))⟩
  change nativeToHodgeFiberLinear G (P.nativeCupH D) = P.cupH beta
  rw [P.nativeNaturality D, hD]

/-- Hard Lefschetz INJECTIVITY forces the primitive projection to
vanish on EVERY h-times-divisor Hodge class. The previous data
required only surjectivity, which was not enough for this fact. -/
theorem primitive_remainder_vanishes_on_cupH
    (G : GeometricCycleClassSpine V H)
    (P : GeometricHigherLefschetzData G d)
    (h11 : DivisorsRepresentHodge11 H)
    (hInject : Function.Injective P.cupH2)
    (beta : ClassicalHodgeFiber V H 1) :
    primitiveHodgeRemainder G P h11 (P.cupH beta) = 0 := by
  obtain ⟨gamma, hc, hg⟩ :=
    correction_is_cup_of_real_divisor G P h11 (P.cupH beta)
  have heq : gamma = beta := by
    apply hInject
    calc
      P.cupH2 gamma = P.primitiveTest (P.cupH beta) := hg
      _ = P.cupH2 beta := P.twoStepCompatibility beta
  unfold primitiveHodgeRemainder
  rw [hc, heq]
  exact sub_self _

/-- Exact equality between the true rational Hodge primitive
projection and the class of the native algebraic corrected cycle. -/
theorem native_primitive_projection_cycleClass
    (G : GeometricCycleClassSpine V H)
    (P : GeometricHigherLefschetzData G d)
    (h11 : DivisorsRepresentHodge11 H)
    (Z : codimensionCycles V.X 2) :
    nativeToHodgeFiberLinear G
      (primitiveizeNativeMiddleCycle G P h11 Z) =
      primitiveHodgeRemainder G P h11
        (nativeToHodgeFiberLinear G Z) := by
  simp [primitiveizeNativeMiddleCycle, primitiveHodgeRemainder, map_sub]

/-- A truly primitive rational class from a native algebraic cycle
is NONZERO exactly when the original cycle is not in the
divisor-times-ample subspace. This detects genuine geometric
primitive directions, not just a nonzero zeta/CM scalar. -/
theorem native_primitive_nonzero_iff_outside_divisor_cup
    (G : GeometricCycleClassSpine V H)
    (P : GeometricHigherLefschetzData G d)
    (h11 : DivisorsRepresentHodge11 H)
    (hInject : Function.Injective P.cupH2)
    (Z : codimensionCycles V.X 2) :
    (nativeToHodgeFiberLinear G
      (primitiveizeNativeMiddleCycle G P h11 Z) ≠ 0) ↔
      (∀ beta : ClassicalHodgeFiber V H 1,
        nativeToHodgeFiberLinear G Z ≠ P.cupH beta) := by
  rw [native_primitive_projection_cycleClass]
  constructor
  · intro hnonzero beta hZ
    rw [hZ] at hnonzero
    exact hnonzero
      (primitive_remainder_vanishes_on_cupH G P h11 hInject beta)
  · intro houtside hzero
    obtain ⟨beta, hc, _⟩ :=
      correction_is_cup_of_real_divisor G P h11
        (nativeToHodgeFiberLinear G Z)
    have hZ : nativeToHodgeFiberLinear G Z = P.cupH beta := by
      have heq :
          nativeToHodgeFiberLinear G Z =
          nativeToHodgeFiberLinear G
            (algebraicLefschetzCorrection G P h11
              (nativeToHodgeFiberLinear G Z)) := by
        exact sub_eq_zero.mp hzero
      exact heq.trans hc
    exact houtside beta hZ

/-- A TRUE new construction: given an actual codimension-two
algebraic cycle with an independently testable class outside
h times divisors, return an actual nonzero primitive algebraic
cycle. Its Hodge class is forced to be primitive by geometry,
and forced nonzero by Hard Lefschetz injectivity. No algebraic
preimage of an arbitrary primitive target class is assumed. -/
theorem exists_actual_nonzero_algebraic_primitive_of_transverse_cycle
    (G : GeometricCycleClassSpine V H)
    (P : GeometricHigherLefschetzData G d)
    (h11 : DivisorsRepresentHodge11 H)
    (hInject : Function.Injective P.cupH2)
    (Z : codimensionCycles V.X 2)
    (houtside : ∀ beta : ClassicalHodgeFiber V H 1,
      nativeToHodgeFiberLinear G Z ≠ P.cupH beta) :
    ∃ W : codimensionCycles V.X 2,
      nativeToHodgeFiberLinear G W ≠ 0 ∧
      P.primitiveTest (nativeToHodgeFiberLinear G W) = 0 := by
  refine ⟨primitiveizeNativeMiddleCycle G P h11 Z, ?_, ?_⟩
  · exact (native_primitive_nonzero_iff_outside_divisor_cup
        G P h11 hInject Z).2 houtside
  · exact primitiveizeNativeMiddleCycle_primitive G P h11 Z

#check correction_is_cup_of_real_divisor
#check primitive_remainder_vanishes_on_cupH
#check native_primitive_projection_cycleClass
#check native_primitive_nonzero_iff_outside_divisor_cup
#check exists_actual_nonzero_algebraic_primitive_of_transverse_cycle

#print axioms native_primitive_nonzero_iff_outside_divisor_cup
#print axioms exists_actual_nonzero_algebraic_primitive_of_transverse_cycle

end GSTPrimitiveTransverseCycleExtraction
