import GSTClassicalHodgePrimitiveAtomicDefectReduction
import GSTClassicalHodgeAtomicAnnihilator
import GSTClassicalHodgeAtomicDefectDuality
import GSTClassicalHodgeMultiplicityForgettingKernel

/-!
# GST CLASSICAL HODGE — PRIMITIVE DEFECT TOMOGRAPHY GHOST

The previous reduction proves that, after ordinary Lefschetz propagation is
removed, every genuinely new Hodge obstruction lives in the primitive atomic
defect.  This file transforms a nonzero primitive defect into a multiplicity-
faithful GST packet.

A surviving primitive defect yields:

* a genuine primitive Hodge vector gamma;
* a nonzero class in the quotient by all genuine point-cycle classes;
* an ambient rational detector annihilating every atomic cycle class but
  detecting gamma;
* a nonzero finite-support fibered Hodge address of gamma;
* an explicit completed probe with nonzero fibered pairing against that
  address.

Crucially the final address remains in the full fibered multiplicity universe.
We do not pass through `forgetMultiplicityToGST`, whose nontrivial kernel is
already formalized and can erase precisely the same-weight information at
issue.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgePrimitiveDefectTomographyGhost

open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeAtomicDefectDuality
open GSTClassicalHodgeAtomicAnnihilator
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgePrimitiveAtomicDefectReduction

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {G : GeometricCycleClassSpine V H}
variable {D : LefschetzPrimitiveDecomposition G}
variable {p : Nat}

/-- Primitive-only separator packet extracted from a nonzero primitive atomic
defect. -/
structure PrimitiveAtomicSeparator
    (D : LefschetzPrimitiveDecomposition G)
    (p : Nat) where
  primitiveClass : D.primitive p
  defect_ne_zero :
    atomicDefectLinearMap V H p primitiveClass.1 ≠ 0
  detector :
    RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ] ℚ
  annihilates_atoms :
    AnnihilatesPointCycleClasses p (H.cycleClass p) detector
  detects_primitive : detector primitiveClass.1.1 ≠ 0

namespace PrimitiveAtomicSeparator

/-- The detected primitive Hodge vector is genuinely nonzero. -/
theorem primitiveClass_ne_zero
    (E : PrimitiveAtomicSeparator D p) :
    E.primitiveClass.1 ≠ 0 := by
  intro hz
  apply E.detects_primitive
  rw [hz]
  exact E.detector.map_zero

/-- Its full fibered Hodge address is nonzero; no multiplicity information has
been forgotten. -/
theorem fiberedAddress_ne_zero
    (E : PrimitiveAtomicSeparator D p) :
    fiberedWeightCoordinates V H p E.primitiveClass.1 ≠ 0 := by
  intro hzero
  have hzero0 :
      fiberedWeightCoordinates V H p
          (0 : ClassicalHodgeFiber V H p) = 0 := by
    simp [fiberedWeightCoordinates]
  have heq : E.primitiveClass.1 = 0 :=
    fiberedWeightCoordinates_injective V H p
      (hzero.trans hzero0.symm)
  exact E.primitiveClass_ne_zero heq

/-- A nonzero primitive fibered address has an explicit completed tomography
probe with nonzero pairing. -/
theorem exists_fiberedProbe_detecting
    (E : PrimitiveAtomicSeparator D p) :
    ∃ s : FiberedHodgeIndex V H,
      fiberedPairing
          (fiberedWeightCoordinates V H p E.primitiveClass.1)
          (fiberedProbe s) ≠ 0 := by
  let a := fiberedWeightCoordinates V H p E.primitiveClass.1
  have ha : a ≠ 0 := E.fiberedAddress_ne_zero
  have hsupp : a.support.Nonempty := Finsupp.support_nonempty_iff.mpr ha
  let s := hsupp.choose
  have hs : a s ≠ 0 := Finsupp.mem_support_iff.mp hsupp.choose_spec
  refine ⟨s, ?_⟩
  simpa [a] using hs

end PrimitiveAtomicSeparator

/-- **NONZERO PRIMITIVE DEFECT -> PRIMITIVE ATOMIC SEPARATOR.** -/
theorem exists_primitiveAtomicSeparator_of_defect_ne_zero
    (hdef : D.primitiveDefectMap p ≠ 0) :
    Nonempty (PrimitiveAtomicSeparator D p) := by
  have hex :
      ∃ gamma : D.primitive p,
        D.primitiveDefectMap p gamma ≠ 0 := by
    by_contra h
    push_neg at h
    apply hdef
    apply LinearMap.ext
    intro gamma
    exact h gamma
  rcases hex with ⟨gamma, hgammaDef⟩
  have hnotmem :
      gamma.1.1 ∉ pointCycleClassSpan p (H.cycleClass p) := by
    intro hmem
    apply hgammaDef
    change Submodule.Quotient.mk gamma.1.1 = 0
    exact (Submodule.Quotient.mk_eq_zero
      (pointCycleClassSpan p (H.cycleClass p))).2 hmem
  obtain ⟨ell, hellSpan, hellGamma⟩ :=
    exists_linearFunctional_separating_submodule
      (pointCycleClassSpan p (H.cycleClass p)) gamma.1.1 hnotmem
  refine ⟨{
    primitiveClass := gamma
    defect_ne_zero := hgammaDef
    detector := ell
    annihilates_atoms := ?_
    detects_primitive := hellGamma
  }⟩
  intro x
  apply hellSpan
  exact Submodule.subset_span ⟨x, rfl⟩

/-- **PRIMITIVE TOMOGRAPHY GHOST.**
Every surviving primitive atomic defect produces, simultaneously, an atomic
separator and a nonzero completed fibered tomography read. -/
theorem primitiveDefect_yields_separator_and_tomography
    (hdef : D.primitiveDefectMap p ≠ 0) :
    ∃ E : PrimitiveAtomicSeparator D p,
    ∃ s : FiberedHodgeIndex V H,
      fiberedPairing
          (fiberedWeightCoordinates V H p E.primitiveClass.1)
          (fiberedProbe s) ≠ 0 := by
  let E := Classical.choice
    (exists_primitiveAtomicSeparator_of_defect_ne_zero
      (D := D) (p := p) hdef)
  rcases E.exists_fiberedProbe_detecting with ⟨s, hs⟩
  exact ⟨E, s, hs⟩

/-- First-failure form: once the lower weight has zero defect, any nonzero next
weight produces a primitive separator with a multiplicity-faithful tomography
moment. -/
theorem nextWeightFailure_yields_primitive_tomography
    (p : Nat)
    (hsource : atomicDefectLinearMap V H p = 0)
    (htarget : atomicDefectLinearMap V H (p + 1) ≠ 0) :
    ∃ E : PrimitiveAtomicSeparator D (p + 1),
    ∃ s : FiberedHodgeIndex V H,
      fiberedPairing
          (fiberedWeightCoordinates V H (p + 1) E.primitiveClass.1)
          (fiberedProbe s) ≠ 0 := by
  have hprim := D.primitiveDefect_ne_zero_of_target_ne_zero
    p hsource htarget
  exact primitiveDefect_yields_separator_and_tomography
    (D := D) (p := p + 1) hprim

#check PrimitiveAtomicSeparator
#check PrimitiveAtomicSeparator.primitiveClass_ne_zero
#check PrimitiveAtomicSeparator.fiberedAddress_ne_zero
#check PrimitiveAtomicSeparator.exists_fiberedProbe_detecting
#check exists_primitiveAtomicSeparator_of_defect_ne_zero
#check primitiveDefect_yields_separator_and_tomography
#check nextWeightFailure_yields_primitive_tomography

#print axioms PrimitiveAtomicSeparator.fiberedAddress_ne_zero
#print axioms PrimitiveAtomicSeparator.exists_fiberedProbe_detecting
#print axioms exists_primitiveAtomicSeparator_of_defect_ne_zero
#print axioms primitiveDefect_yields_separator_and_tomography
#print axioms nextWeightFailure_yields_primitive_tomography

end GSTClassicalHodgePrimitiveDefectTomographyGhost
