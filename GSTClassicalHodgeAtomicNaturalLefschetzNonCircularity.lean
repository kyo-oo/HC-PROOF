import GSTClassicalHodgeAtomicDefectEquivariantIrreducibility
import GSTClassicalHodgeTwoSlotLefschetzCollapse
import GSTClassicalHodgeBareLefschetzNonCircularity

/-!
# GST CLASSICAL HODGE — ATOMIC-NATURAL TWO-SLOT LEFSCHETZ AUDIT

The atomic-defect equivariance splice compresses the remaining externalization
problem to ambient operators which preserve the genuine atomic cycle-class
span and whose Hodge restrictions are prescribed GST operators.

This file records the critical primitive-level firewall.  In the universal
two-slot window, bare `L^2` is already a nonzero scalar times the rank-free
matrix unit.  Therefore, once one algebraic Hodge source has a nonzero source
coordinate, an `AtomicNaturalHodgeOperator` whose Hodge restriction is that
bare two-slot Lefschetz primitive forces the target basis sheet itself to be
algebraic.

So the quotient-equivariant interface does not make the old bare-Lefschetz
obstruction disappear: atomic naturality of this primitive on a ghost crossing
is exactly Hodge-strength.  Any successful construction of the primitive must
come from genuinely new independent geometry and cannot be postulated as a
formal consequence of GST coordinates alone.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeAtomicNaturalLefschetzNonCircularity

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeRankFreePrimitiveGeneration
open GSTClassicalHodgeExplicitArsenalGeneration
open GSTClassicalHodgeUniversalTwoSlotNativeClosure
open GSTClassicalHodgeTwoSlotLefschetzCollapse
open GSTClassicalHodgeAtomicDefectEquivariantIrreducibility

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- The Hodge restriction used by the bare two-slot Lefschetz primitive. -/
noncomputable def bareTwoSlotLefschetzHodge
    (i j : ClassicalHodgeBasisIndex V H p) :
    Module.End ℚ (ClassicalHodgeFiber V H p) :=
  twoSlotHodgeOperator i j (diagonalLefschetzQ 2 2)

/-- Bare two-slot Lefschetz on the Hodge fiber is exactly the fixed nonzero
forward scalar times the rank-free matrix unit. -/
theorem bareTwoSlotLefschetzHodge_eq_scaled_matrixUnit
    (i j : ClassicalHodgeBasisIndex V H p) :
    bareTwoSlotLefschetzHodge (V := V) (H := H) i j =
      (forwardScalar sourceSlot targetSlot : ℚ) • hodgeMatrixUnit i j := by
  simpa [bareTwoSlotLefschetzHodge, twoSlotHodgeOperator] using
    (lifted_twoSlotLefschetz_eq_scaled_hodgeMatrixUnit
      (V := V) (H := H) i j)

/-- **ATOMIC-NATURAL L² FORCES TARGET ALGEBRAICITY.**

One live algebraic source plus atomic naturality of an ambient operator whose
Hodge restriction is bare two-slot `L²` already implies that the target basis
sheet is in the genuine atomic cycle-class span. -/
theorem targetBasis_algebraic_of_atomicNatural_bareLefschetz
    (i j : ClassicalHodgeBasisIndex V H p)
    (a : ClassicalHodgeFiber V H p)
    (haAlg : a ∈ AlgebraicHodgeSubspace V H p)
    (hi : hodgeCoordinate i a ≠ 0)
    (T : AtomicNaturalHodgeOperator V H p)
    (hT : T.hodge = bareTwoSlotLefschetzHodge (V := V) (H := H) i j) :
    (classicalHodgeBasis V H p j).1 ∈
      pointCycleClassSpan p (H.cycleClass p) := by
  have himage : T.hodge a ∈ AlgebraicHodgeSubspace V H p :=
    T.preserves_algebraicHodge haAlg
  have hL := bareTwoSlotLefschetzHodge_eq_scaled_matrixUnit
    (V := V) (H := H) i j
  change (T.hodge a).1 ∈ pointCycleClassSpan p (H.cycleClass p) at himage
  rw [hT, hL] at himage
  simp only [LinearMap.smul_apply, hodgeMatrixUnit_apply] at himage
  let c : ℚ :=
    (forwardScalar sourceSlot targetSlot : ℚ) * hodgeCoordinate i a
  have hc : c ≠ 0 :=
    mul_ne_zero twoSlot_forwardScalar_ne_zero hi
  have hscaled :=
    (pointCycleClassSpan p (H.cycleClass p)).smul_mem c⁻¹ himage
  simpa [c, hc, smul_smul] using hscaled

/-- If a separator ghost detects the target basis sheet, no atomic-natural
realization of bare two-slot Lefschetz can cross from a live algebraic source
to that sheet. -/
theorem no_atomicNatural_bareLefschetz_to_separatorSheet
    (i j : ClassicalHodgeBasisIndex V H p)
    (a : ClassicalHodgeFiber V H p)
    (haAlg : a ∈ AlgebraicHodgeSubspace V H p)
    (hi : hodgeCoordinate i a ≠ 0)
    (ell : RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ] ℚ)
    (hann :
      pointCycleClassSpan p (H.cycleClass p) ≤ LinearMap.ker ell)
    (hdetect : ell (classicalHodgeBasis V H p j).1 ≠ 0) :
    ¬ ∃ T : AtomicNaturalHodgeOperator V H p,
      T.hodge = bareTwoSlotLefschetzHodge (V := V) (H := H) i j := by
  rintro ⟨T, hT⟩
  have hj := targetBasis_algebraic_of_atomicNatural_bareLefschetz
    i j a haAlg hi T hT
  exact hdetect (hann hj)

#check bareTwoSlotLefschetzHodge
#check bareTwoSlotLefschetzHodge_eq_scaled_matrixUnit
#check targetBasis_algebraic_of_atomicNatural_bareLefschetz
#check no_atomicNatural_bareLefschetz_to_separatorSheet

#print axioms bareTwoSlotLefschetzHodge_eq_scaled_matrixUnit
#print axioms targetBasis_algebraic_of_atomicNatural_bareLefschetz
#print axioms no_atomicNatural_bareLefschetz_to_separatorSheet

end GSTClassicalHodgeAtomicNaturalLefschetzNonCircularity
