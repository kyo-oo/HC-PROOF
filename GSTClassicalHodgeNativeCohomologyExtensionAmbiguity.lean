import GSTClassicalHodgeCrossWeightNativePropagation
import GSTClassicalHodgeAtomicDefectDuality

/-!
# GST CLASSICAL HODGE — NATIVE / COHOMOLOGY EXTENSION AMBIGUITY

A native algebraic-cycle operator does not, by cycle-class naturality alone,
determine its action on non-algebraic cohomology classes.  This is the precise
logical gap exposed by the principal-cut flag round-trip construction.

This module makes that gap into an exact quotient theorem.

Suppose two graded cycle-class-natural operator pairs have the SAME native
cycle operator.  Their cohomological difference vanishes on every actual cycle
class, hence on the complete atomic point-cycle span.  Therefore that
difference factors canonically through the atomic-defect quotient.

So the freedom in extending one native operator to all cohomology is neither
mysterious nor spread across the ambient vector space.  It is exactly one
linear map

    AtomicDefectSpace(source weight) -> target cohomology.

Killing this quotient map is equivalent to uniqueness of the cohomological
extension.  This is the correct place for a new GST Poincare/worldtrace law to
act: not on native cycles (where the geometry is already fixed), but on the
residual primitive defect quotient invisible to ordinary cycle-class
naturality.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeNativeCohomologyExtensionAmbiguity

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTGeometricRealizationStage2D
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeAtomicDefectDuality
open GSTClassicalHodgeCrossWeightNativePropagation

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p q : Nat}

abbrev SourceCoh :=
  RationalSingularCohomology H.analytification (2 * p)

abbrev TargetCoh :=
  RationalSingularCohomology H.analytification (2 * q)

/-- Difference of the cohomological faces of two graded realizations. -/
noncomputable def cohomologyDifference
    (A B : GradedCycleClassOperatorPair V H p q) :
    SourceCoh (H := H) (p := p) →ₗ[ℚ] TargetCoh (H := H) (q := q) :=
  A.cohomologyOperator - B.cohomologyOperator

/-- If the native cycle operators agree, the cohomological difference vanishes
on every genuine cycle-class value. -/
theorem cohomologyDifference_cycleClass_eq_zero
    (A B : GradedCycleClassOperatorPair V H p q)
    (hnative : A.cycleOperator = B.cycleOperator)
    (Z : codimensionCycles V.X p) :
    cohomologyDifference A B (H.cycleClass p Z) = 0 := by
  unfold cohomologyDifference
  simp only [LinearMap.sub_apply]
  rw [← A.cycleClass_natural Z, ← B.cycleClass_natural Z, hnative]
  exact sub_self _

/-- Therefore the complete atomic source span lies in the kernel of the
extension difference. -/
theorem atomicSpan_le_difference_kernel
    (A B : GradedCycleClassOperatorPair V H p q)
    (hnative : A.cycleOperator = B.cycleOperator) :
    pointCycleClassSpan p (H.cycleClass p) ≤
      LinearMap.ker (cohomologyDifference A B) := by
  intro alpha halpha
  rw [← smoothProjective_cycleClass_range_eq_atomic_span V H p] at halpha
  rcases halpha with ⟨Z, rfl⟩
  exact cohomologyDifference_cycleClass_eq_zero A B hnative Z

/-- **CANONICAL DEFECT-QUOTIENT AMBIGUITY MAP.**
All freedom between two cohomological extensions of the same native operator
factors through the source atomic-defect quotient. -/
noncomputable def extensionAmbiguity
    (A B : GradedCycleClassOperatorPair V H p q)
    (hnative : A.cycleOperator = B.cycleOperator) :
    AtomicDefectSpace V H p →ₗ[ℚ] TargetCoh (H := H) (q := q) :=
  Submodule.liftQ
    (pointCycleClassSpan p (H.cycleClass p))
    (cohomologyDifference A B)
    (atomicSpan_le_difference_kernel A B hnative)

/-- Representative formula: the quotient ambiguity is literally the
cohomological difference. -/
@[simp]
theorem extensionAmbiguity_mk
    (A B : GradedCycleClassOperatorPair V H p q)
    (hnative : A.cycleOperator = B.cycleOperator)
    (alpha : SourceCoh (H := H) (p := p)) :
    extensionAmbiguity A B hnative (Submodule.Quotient.mk alpha) =
      A.cohomologyOperator alpha - B.cohomologyOperator alpha := by
  rfl

/-- Vanishing quotient ambiguity forces the two cohomological extensions to
agree on every ambient cohomology class. -/
theorem cohomologyOperator_eq_of_extensionAmbiguity_eq_zero
    (A B : GradedCycleClassOperatorPair V H p q)
    (hnative : A.cycleOperator = B.cycleOperator)
    (hamb : extensionAmbiguity A B hnative = 0) :
    A.cohomologyOperator = B.cohomologyOperator := by
  apply LinearMap.ext
  intro alpha
  have h := LinearMap.congr_fun hamb (Submodule.Quotient.mk alpha)
  rw [extensionAmbiguity_mk] at h
  simp only [LinearMap.zero_apply] at h
  exact sub_eq_zero.mp h

/-- Conversely equal cohomological extensions have zero defect ambiguity. -/
theorem extensionAmbiguity_eq_zero_of_cohomologyOperator_eq
    (A B : GradedCycleClassOperatorPair V H p q)
    (hnative : A.cycleOperator = B.cycleOperator)
    (hcoh : A.cohomologyOperator = B.cohomologyOperator) :
    extensionAmbiguity A B hnative = 0 := by
  apply LinearMap.ext
  intro z
  refine Submodule.Quotient.induction_on _ z ?_
  intro alpha
  rw [extensionAmbiguity_mk]
  rw [hcoh]
  simp

/-- **UNIQUENESS IFF DEFECT AMBIGUITY VANISHES.** -/
theorem cohomologyExtension_unique_iff
    (A B : GradedCycleClassOperatorPair V H p q)
    (hnative : A.cycleOperator = B.cycleOperator) :
    A.cohomologyOperator = B.cohomologyOperator ↔
      extensionAmbiguity A B hnative = 0 := by
  constructor
  · exact extensionAmbiguity_eq_zero_of_cohomologyOperator_eq A B hnative
  · exact cohomologyOperator_eq_of_extensionAmbiguity_eq_zero A B hnative

/-- A nonzero discrepancy between two extensions is witnessed by a nonzero
atomic-defect class.  Hence no further search on actual cycle classes can
resolve it: one must probe the quotient sector itself. -/
theorem exists_defect_witness_of_cohomologyOperator_ne
    (A B : GradedCycleClassOperatorPair V H p q)
    (hnative : A.cycleOperator = B.cycleOperator)
    (hne : A.cohomologyOperator ≠ B.cohomologyOperator) :
    ∃ z : AtomicDefectSpace V H p,
      extensionAmbiguity A B hnative z ≠ 0 := by
  by_contra hnone
  push_neg at hnone
  apply hne
  apply cohomologyOperator_eq_of_extensionAmbiguity_eq_zero A B hnative
  apply LinearMap.ext
  intro z
  simpa using hnone z

#check cohomologyDifference
#check cohomologyDifference_cycleClass_eq_zero
#check atomicSpan_le_difference_kernel
#check extensionAmbiguity
#check extensionAmbiguity_mk
#check cohomologyExtension_unique_iff
#check exists_defect_witness_of_cohomologyOperator_ne

#print axioms cohomologyDifference_cycleClass_eq_zero
#print axioms atomicSpan_le_difference_kernel
#print axioms extensionAmbiguity_mk
#print axioms cohomologyExtension_unique_iff
#print axioms exists_defect_witness_of_cohomologyOperator_ne

end GSTClassicalHodgeNativeCohomologyExtensionAmbiguity
