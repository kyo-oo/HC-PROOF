import GSTClassicalHodgeActualNoncommutativeNativeFrame
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Strict geometric rank-gain certificate from noncommutative GST cycles

The actual geometric projective spine carries a NONZERO conserved charge.
A genuine geometric correspondence E can act as a scalar on that charge
functional even while acting nontrivially on the Hodge fiber.

If E and F each act by scalars on the same charge, their commutator has
exactly ZERO charge. When the constructed commutator Betti class is NONZERO,
it is automatically linearly independent from the actual nonzero-charge
native spine. Hence actual geometric noncommutativity opens a SECOND
algebraic Hodge direction, not just another formula for the same class.

The nonzero commutator is an independently testable geometric requirement.
This file does not assume the Hodge conjecture or target-cycle preimages,
nor does it prove such a nonzero commutator exists on every variety.
-/

set_option maxHeartbeats 12000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeLimitlessSpinePropagation
open GSTClassicalHodgeRealizedCorrespondenceExpressionAlgebra
open GSTClassicalHodgeActualNoncommutativeNativeFrame

namespace GSTClassicalHodgeActualCommutatorRankGain

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- The recursively manufactured projective spine has a genuine nonzero
cohomological charge, derived from the native charge law and exact naturality. -/
theorem actualSpine_betti_charge_nonzero
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge G) :
    D.cohomologyRead p (spineHodgeSeed G p).1 ≠ 0 := by
  rw [← spineNativeTower_cycleClass G p]
  rw [D.cycleClass_read p (spineNativeTower G p)]
  exact D.nativeRead_spineNativeTower_ne_zero p

/-- Two REALIZED geometric actions preserving the charge line necessarily
have a zero-charge commutator, even if the cohomological commutator itself
is a new nonzero algebraic Hodge direction. -/
theorem geometric_commutator_charge_zero
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge G)
    (E F : RealizedCorrespondenceExpr V H p)
    (a b : ℚ)
    (hE : ∀ x : RationalSingularCohomology H.analytification (2 * p),
      D.cohomologyRead p (E.cohomologyOperator x) =
        a * D.cohomologyRead p x)
    (hF : ∀ x : RationalSingularCohomology H.analytification (2 * p),
      D.cohomologyRead p (F.cohomologyOperator x) =
        b * D.cohomologyRead p x) :
    D.cohomologyRead p (bettiGeometricCommutator G E F) = 0 := by
  unfold bettiGeometricCommutator
  rw [map_sub, hE, hF, hF, hE]
  ring

/-- A charge-zero NONZERO native geometric commutator is automatically
independent from the original nonzero-charge native spine.

This is an exact algebraic two-vector independence proof; the target
Hodge space and any desired target class are not supplied as premises. -/
theorem geometric_spine_commutator_coefficient_rigidity
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge G)
    (E F : RealizedCorrespondenceExpr V H p)
    (hcomm : bettiGeometricCommutator G E F ≠ 0)
    (hcommcharge : D.cohomologyRead p
      (bettiGeometricCommutator G E F) = 0) :
    ∀ a b : ℚ,
      a • (spineHodgeSeed G p).1 +
        b • bettiGeometricCommutator G E F = 0 →
      a = 0 ∧ b = 0 := by
  intro a b hab
  have hread :
      a * D.cohomologyRead p (spineHodgeSeed G p).1 +
        b * D.cohomologyRead p (bettiGeometricCommutator G E F) = 0 := by
    have h := congrArg (D.cohomologyRead p) hab
    simpa only [map_add, map_smul, map_zero, smul_eq_mul] using h
  have hamul : a * D.cohomologyRead p (spineHodgeSeed G p).1 = 0 := by
    simpa [hcommcharge] using hread
  have ha : a = 0 :=
    (mul_eq_zero.mp hamul).resolve_right
      (actualSpine_betti_charge_nonzero G D)
  subst a
  have hbsmul : b • bettiGeometricCommutator G E F = 0 := by
    simpa using hab
  have hb : b = 0 := (smul_eq_zero.mp hbsmul).resolve_right hcomm
  exact ⟨rfl, hb⟩

/-- The original projective spine and the *ACTUAL* geometric commutator
have two linearly independent Betti classes when the conserved charge
separates them. This certifies a strict rank gain from genuine geometry. -/
theorem actual_spine_and_commutator_linearIndependent
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge G)
    (E F : RealizedCorrespondenceExpr V H p)
    (hcomm : bettiGeometricCommutator G E F ≠ 0)
    (hcommcharge : D.cohomologyRead p
      (bettiGeometricCommutator G E F) = 0) :
    LinearIndependent ℚ
      ![(spineHodgeSeed G p).1, bettiGeometricCommutator G E F] := by
  exact (LinearIndependent.pair_iff).2
    (geometric_spine_commutator_coefficient_rigidity
      G D E F hcomm hcommcharge)

/-- Charge-eigenfunctional geometry removes the zero-charge condition:
nonvanishing of the actual commutator is now the ONLY additional condition
needed for a second independent algebraic Hodge class. -/
theorem actual_rank_gain_of_geometric_charge_eigenoperators
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge G)
    (E F : RealizedCorrespondenceExpr V H p)
    (a b : ℚ)
    (hE : ∀ x : RationalSingularCohomology H.analytification (2 * p),
      D.cohomologyRead p (E.cohomologyOperator x) =
        a * D.cohomologyRead p x)
    (hF : ∀ x : RationalSingularCohomology H.analytification (2 * p),
      D.cohomologyRead p (F.cohomologyOperator x) =
        b * D.cohomologyRead p x)
    (hcomm : bettiGeometricCommutator G E F ≠ 0) :
    LinearIndependent ℚ
      ![(spineHodgeSeed G p).1, bettiGeometricCommutator G E F] :=
  actual_spine_and_commutator_linearIndependent G D E F hcomm
    (geometric_commutator_charge_zero G D E F a b hE hF)

#check actualSpine_betti_charge_nonzero
#check geometric_commutator_charge_zero
#check actual_spine_and_commutator_linearIndependent
#check actual_rank_gain_of_geometric_charge_eigenoperators

#print axioms actualSpine_betti_charge_nonzero
#print axioms geometric_commutator_charge_zero
#print axioms actual_rank_gain_of_geometric_charge_eigenoperators

end GSTClassicalHodgeActualCommutatorRankGain
