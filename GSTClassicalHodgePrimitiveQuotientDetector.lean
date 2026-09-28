import GSTClassicalHodgePrimitiveGeometricQuotient

/-!
# GST CLASSICAL HODGE — PRIMITIVE QUOTIENT DETECTOR

The minimal separator annihilates the complete lower-weight geometric image.
Therefore it descends canonically through the primitive geometric quotient.
The detected Hodge sheet has a nonzero quotient class, and the descended
functional evaluates on that class by exactly the original nonzero separator
value.

Thus a Stage-2G failure produces a genuine primal/dual primitive obstruction:
a nonzero quotient class together with a nonzero quotient detector.  No new
functional is chosen and no abstract matrix-unit naturality is introduced.
-/

set_option maxHeartbeats 90000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgePrimitiveQuotientDetector

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeMinimalPrimitiveSeparatorGhost
open GSTClassicalHodgePrimitiveGeometricQuotient

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- The minimal separator descended through the quotient by all lower-weight
verified geometric images. -/
noncomputable def primitiveQuotientDetector
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G) :
    PrimitiveGeometricQuotient G M.weight →ₗ[ℚ] ℚ :=
  (lowerGeometricImage G M.weight).liftQ M.separator.detector
    (minimalGhost_lowerGeometricImage_le_ker G M)

/-- Quotient class of the genuine Hodge basis sheet detected by the minimal
ghost. -/
noncomputable def primitiveBasisClass
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G) :
    PrimitiveGeometricQuotient G M.weight :=
  Submodule.Quotient.mk
    (classicalHodgeBasis V H M.weight M.sheet).1

/-- The descended detector reads the primitive basis class by exactly the
original separator value. -/
theorem primitiveQuotientDetector_basis
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G) :
    primitiveQuotientDetector G M (primitiveBasisClass G M) =
      M.separator.detector
        (classicalHodgeBasis V H M.weight M.sheet).1 := by
  rfl

/-- The primitive quotient basis class is genuinely nonzero. -/
theorem primitiveBasisClass_ne_zero
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G) :
    primitiveBasisClass G M ≠ 0 := by
  intro hz
  have hmem :
      (classicalHodgeBasis V H M.weight M.sheet).1 ∈
        lowerGeometricImage G M.weight :=
    (Submodule.Quotient.mk_eq_zero
      (lowerGeometricImage G M.weight)).mp hz
  exact minimalGhost_basis_not_mem_lowerGeometricImage G M hmem

/-- The descended primitive detector is nonzero. -/
theorem primitiveQuotientDetector_ne_zero
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G) :
    primitiveQuotientDetector G M ≠ 0 := by
  intro hz
  have hread := LinearMap.congr_fun hz (primitiveBasisClass G M)
  rw [primitiveQuotientDetector_basis] at hread
  simp only [LinearMap.zero_apply] at hread
  exact M.separator.detects_basis hread

/-- Exact nonzero primal/dual pairing carried by the primitive remainder. -/
theorem primitive_primal_dual_pairing_nonzero
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G) :
    primitiveQuotientDetector G M (primitiveBasisClass G M) ≠ 0 := by
  rw [primitiveQuotientDetector_basis]
  exact M.separator.detects_basis

/-- Every Stage-2G failure produces a nonzero class in the quotient by all
lower-weight verified geometry together with a descended detector that reads
that class nontrivially. -/
theorem not_hodge_yields_primitive_primal_dual_obstruction
    (G : GeometricCycleClassSpine V H)
    (hnot : ¬ BigradedBettiHodgeStatement V H) :
    ∃ M : MinimalPrimitiveGhost G,
      primitiveBasisClass G M ≠ 0 ∧
      primitiveQuotientDetector G M ≠ 0 ∧
      primitiveQuotientDetector G M (primitiveBasisClass G M) ≠ 0 := by
  let M := minimalPrimitiveGhostOfFailure G hnot
  exact ⟨M,
    primitiveBasisClass_ne_zero G M,
    primitiveQuotientDetector_ne_zero G M,
    primitive_primal_dual_pairing_nonzero G M⟩

#check primitiveQuotientDetector
#check primitiveBasisClass
#check primitiveQuotientDetector_basis
#check primitiveBasisClass_ne_zero
#check primitiveQuotientDetector_ne_zero
#check primitive_primal_dual_pairing_nonzero
#check not_hodge_yields_primitive_primal_dual_obstruction

#print axioms primitiveQuotientDetector_basis
#print axioms primitiveBasisClass_ne_zero
#print axioms primitiveQuotientDetector_ne_zero
#print axioms not_hodge_yields_primitive_primal_dual_obstruction

end GSTClassicalHodgePrimitiveQuotientDetector
