import GSTClassicalHodgePrimitiveQuotientDetector
import GSTClassicalHodgeLimitlessSeparatorGhost

/-!
# GST CLASSICAL HODGE — PRIMITIVE QUOTIENT / LIMITLESS BRIDGE

A minimal separator now has two exact incarnations:

* a linear detector on the primitive quotient obtained after dividing out all
  lower-weight verified geometric images;
* a completed limitless fibered probe obtained from the same ambient detector.

This file proves that those are not merely analogous.  On every genuine Hodge
vector the primitive quotient readout is exactly the limitless fibered pairing.
Thus the primitive quotient obstruction and the completed separator ghost are
one and the same functional seen through two coordinate systems.

We define the canonical probe directly from the separator detector rather than
relying on the optional/default `ghost` field of `MinimalPrimitiveGhost`.
-/

set_option maxHeartbeats 90000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgePrimitiveQuotientLimitlessBridge

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicDefectDuality
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeMinimalPrimitiveSeparatorGhost
open GSTClassicalHodgeLimitlessSeparatorGhost
open GSTClassicalHodgePrimitiveGeometricQuotient
open GSTClassicalHodgePrimitiveQuotientDetector

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Canonical completed probe attached to the separator contained in one
minimal primitive ghost. -/
noncomputable def canonicalPrimitiveProbe
    {G : GeometricCycleClassSpine V H}
    (M : MinimalPrimitiveGhost G) : FiberedCompletedAddress V H :=
  separatorFiberedProbe (V := V) (H := H)
    M.weight M.separator.detector

/-- Quotient the genuine Hodge fiber by all lower-weight verified geometric
images, using the ambient inclusion followed by the canonical quotient map. -/
noncomputable def hodgeToPrimitiveQuotient
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G) :
    ClassicalHodgeFiber V H M.weight →ₗ[ℚ]
      PrimitiveGeometricQuotient G M.weight :=
  (lowerGeometricImage G M.weight).mkQ.comp
    (rationalHodgeSubspace (H.hodgeBigrading M.weight)).subtype

/-- The descended quotient detector reads a Hodge vector exactly as the
original ambient separator does. -/
theorem primitiveDetector_hodge_exact
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    (alpha : ClassicalHodgeFiber V H M.weight) :
    primitiveQuotientDetector G M
        (hodgeToPrimitiveQuotient G M alpha) =
      M.separator.detector alpha.1 := by
  rfl

/-- **PRIMITIVE/LIMITLESS COMMUTING TRIANGLE.**
For every genuine Hodge vector, quotient evaluation and limitless completed
pairing are exactly the same scalar. -/
theorem primitiveDetector_eq_limitlessPairing
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    (alpha : ClassicalHodgeFiber V H M.weight) :
    primitiveQuotientDetector G M
        (hodgeToPrimitiveQuotient G M alpha) =
      fiberedPairing
        (fiberedWeightCoordinates V H M.weight alpha)
        (canonicalPrimitiveProbe M) := by
  rw [primitiveDetector_hodge_exact]
  symm
  exact fiberedPairing_separatorProbe
    M.weight M.separator.detector alpha

/-- On the detected sheet, the quotient/limitless common readout is nonzero. -/
theorem primitive_basis_limitless_pairing_nonzero
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G) :
    fiberedPairing
      (fiberedWeightCoordinates V H M.weight
        (classicalHodgeBasis V H M.weight M.sheet))
      (canonicalPrimitiveProbe M) ≠ 0 := by
  rw [fiberedPairing_separatorProbe]
  exact M.separator.detects_basis

/-- Hence the canonical primitive completed probe is nonzero. -/
theorem canonicalPrimitiveProbe_ne_zero
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G) :
    canonicalPrimitiveProbe M ≠ 0 := by
  exact basisSeparator_ghost_ne_zero M.separator

/-- Every Stage-2G failure therefore yields one exact obstruction seen
simultaneously as a nonzero primitive quotient class/detector pair and as a
nonzero completed limitless probe with identical Hodge readout. -/
theorem not_hodge_yields_primitive_limitless_common_obstruction
    (G : GeometricCycleClassSpine V H)
    (hnot : ¬ BigradedBettiHodgeStatement V H) :
    ∃ M : MinimalPrimitiveGhost G,
      primitiveBasisClass G M ≠ 0 ∧
      primitiveQuotientDetector G M (primitiveBasisClass G M) ≠ 0 ∧
      canonicalPrimitiveProbe M ≠ 0 ∧
      fiberedPairing
        (fiberedWeightCoordinates V H M.weight
          (classicalHodgeBasis V H M.weight M.sheet))
        (canonicalPrimitiveProbe M) ≠ 0 := by
  let M := minimalPrimitiveGhostOfFailure G hnot
  exact ⟨M,
    primitiveBasisClass_ne_zero G M,
    primitive_primal_dual_pairing_nonzero G M,
    canonicalPrimitiveProbe_ne_zero G M,
    primitive_basis_limitless_pairing_nonzero G M⟩

#check canonicalPrimitiveProbe
#check hodgeToPrimitiveQuotient
#check primitiveDetector_hodge_exact
#check primitiveDetector_eq_limitlessPairing
#check primitive_basis_limitless_pairing_nonzero
#check canonicalPrimitiveProbe_ne_zero
#check not_hodge_yields_primitive_limitless_common_obstruction

#print axioms primitiveDetector_eq_limitlessPairing
#print axioms primitive_basis_limitless_pairing_nonzero
#print axioms not_hodge_yields_primitive_limitless_common_obstruction

end GSTClassicalHodgePrimitiveQuotientLimitlessBridge
