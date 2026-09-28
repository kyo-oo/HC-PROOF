import GSTClassicalHodgeMinimalPrimitiveSeparatorGhost
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# GST CLASSICAL HODGE — GEOMETRIC PRIMITIVE QUOTIENT

A minimal separator ghost is stronger than ordinary Lefschetz primitivity.
It annihilates the image of **every** verified mixed geometric program arriving
from every strictly smaller Hodge weight.

This file packages that entire lower-weight geometry into one canonical
submodule of the ambient target cohomology.  Quotienting by it isolates the
part of the target weight which cannot be generated from lower weights by any
combination of genuine projective self-transports, principal cuts, rational
linear combinations and compositions already certified by the graded program
algebra.

The key point is that this construction introduces no new geometric
hypothesis:

* the lower image is generated only by existing verified graded programs;
* every same-weight verified program preserves it, simply by post-composition;
* a minimal separator vanishes on the whole lower image by minimality;
* therefore the separator descends to a nonzero functional on the quotient;
* the detected Hodge basis sheet is nonzero in that quotient.

Thus any Stage-2G failure yields an honest nonzero **geometric primitive
quotient class** and a nonzero dual detector on the same quotient.  The
remaining extinction problem may therefore be attacked entirely inside this
primitive quotient, after all lower-weight geometric contamination has been
removed.
-/

set_option maxHeartbeats 90000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeGeometricPrimitiveQuotient

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeGradedGeometricProgramOrbit
open GSTClassicalHodgeMinimalPrimitiveSeparatorGhost

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Ambient rational cohomology in the target Hodge degree. -/
abbrev AmbientWeightCohomology
    (H : HodgeBigradedBettiData V) (p : Nat) :=
  RationalSingularCohomology H.analytification (2 * p)

/-- One state belongs to the raw lower-weight geometric image when it is the
cohomological image of a genuine Hodge state in some strictly smaller weight
under one verified mixed geometric program. -/
def lowerProgramImageSet
    (G : GeometricCycleClassSpine V H)
    (p : Nat) : Set (AmbientWeightCohomology H p) :=
  { x | ∃ q : Nat, q < p ∧
      ∃ P : GradedGeometricProgram V q p,
      ∃ alpha : ClassicalHodgeFiber V H q,
        x = P.cohomologyEval G alpha.1 }

/-- Linear closure of all verified lower-weight geometric images in weight p. -/
noncomputable def lowerProgramImageModule
    (G : GeometricCycleClassSpine V H)
    (p : Nat) : Submodule ℚ (AmbientWeightCohomology H p) :=
  Submodule.span ℚ (lowerProgramImageSet G p)

/-- Every raw lower-weight program image is in the lower geometric module. -/
theorem lowerProgramImageSet_subset_module
    (G : GeometricCycleClassSpine V H)
    (p : Nat) :
    lowerProgramImageSet G p ⊆ lowerProgramImageModule G p := by
  intro x hx
  exact Submodule.subset_span hx

/-- Post-composition by a same-weight verified geometric program preserves the
raw lower image.  This is the fundamental reason the primitive quotient has a
genuine horizontal geometry action. -/
theorem lowerProgramImageSet_stable_sameWeight
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (Q : GradedGeometricProgram V p p)
    {x : AmbientWeightCohomology H p}
    (hx : x ∈ lowerProgramImageSet G p) :
    Q.cohomologyEval G x ∈ lowerProgramImageSet G p := by
  rcases hx with ⟨q, hq, P, alpha, rfl⟩
  refine ⟨q, hq, GradedGeometricProgram.comp P Q, alpha, ?_⟩
  rfl

/-- Hence every same-weight verified program preserves the entire linear lower
image, not only its generators. -/
theorem lowerProgramImageModule_stable_sameWeight
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (Q : GradedGeometricProgram V p p) :
    ∀ x ∈ lowerProgramImageModule G p,
      Q.cohomologyEval G x ∈ lowerProgramImageModule G p := by
  intro x hx
  refine Submodule.span_induction hx ?generator ?zero ?add ?smul
  · intro y hy
    exact lowerProgramImageSet_subset_module G p
      (lowerProgramImageSet_stable_sameWeight G p Q hy)
  · simpa using (lowerProgramImageModule G p).zero_mem
  · intro y z hy hz
    simpa using (lowerProgramImageModule G p).add_mem hy hz
  · intro c y hy
    simpa using (lowerProgramImageModule G p).smul_mem c hy

/-- The lower geometric image is contained in the kernel of every minimal
primitive separator.  This is the global form of the pointwise minimality law:
the separator kills arbitrary rational superpositions of lower-weight program
images. -/
theorem minimalGhost_lowerProgramImage_le_kernel
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G) :
    lowerProgramImageModule G M.weight ≤
      LinearMap.ker M.separator.detector := by
  apply Submodule.span_le.mpr
  intro x hx
  rcases hx with ⟨q, hq, P, alpha, rfl⟩
  exact M.primitive q hq P alpha

/-- The detected basis sheet of a minimal ghost cannot lie in the lower
geometric image. -/
theorem minimalGhost_sheet_not_mem_lowerProgramImage
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G) :
    (classicalHodgeBasis V H M.weight M.sheet).1 ∉
      lowerProgramImageModule G M.weight := by
  intro hmem
  have hker := minimalGhost_lowerProgramImage_le_kernel G M hmem
  exact M.separator.detects_basis hker

/-- Quotient of target cohomology by everything generated from strictly lower
weights through the verified graded geometry. -/
abbrev GeometricPrimitiveQuotient
    (G : GeometricCycleClassSpine V H)
    (p : Nat) :=
  AmbientWeightCohomology H p ⧸ lowerProgramImageModule G p

/-- Canonical class of an ambient target state in the geometric primitive
quotient. -/
noncomputable def primitiveClass
    (G : GeometricCycleClassSpine V H)
    (p : Nat) :
    AmbientWeightCohomology H p →ₗ[ℚ] GeometricPrimitiveQuotient G p :=
  (lowerProgramImageModule G p).mkQ

/-- The detected minimal Hodge sheet survives nontrivially in the quotient. -/
theorem minimalGhost_primitiveClass_ne_zero
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G) :
    primitiveClass G M.weight
        (classicalHodgeBasis V H M.weight M.sheet).1 ≠ 0 := by
  intro hz
  have hmem :
      (classicalHodgeBasis V H M.weight M.sheet).1 ∈
        lowerProgramImageModule G M.weight := by
    exact (Submodule.Quotient.mk_eq_zero
      (lowerProgramImageModule G M.weight)).mp hz
  exact minimalGhost_sheet_not_mem_lowerProgramImage G M hmem

/-- The minimal separator descends canonically to the geometric primitive
quotient because it annihilates the complete lower image. -/
noncomputable def minimalGhostQuotientDetector
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G) :
    GeometricPrimitiveQuotient G M.weight →ₗ[ℚ] ℚ :=
  (lowerProgramImageModule G M.weight).liftQ
    M.separator.detector
    (minimalGhost_lowerProgramImage_le_kernel G M)

/-- On a quotient class the descended detector is exactly the original
separator detector. -/
@[simp]
theorem minimalGhostQuotientDetector_primitiveClass
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    (x : AmbientWeightCohomology H M.weight) :
    minimalGhostQuotientDetector G M (primitiveClass G M.weight x) =
      M.separator.detector x := by
  exact Submodule.liftQ_apply
    (lowerProgramImageModule G M.weight)
    M.separator.detector x

/-- The quotient detector is genuinely nonzero: it still detects the surviving
minimal Hodge sheet. -/
theorem minimalGhostQuotientDetector_ne_zero
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G) :
    minimalGhostQuotientDetector G M ≠ 0 := by
  intro hz
  have hval := LinearMap.congr_fun hz
    (primitiveClass G M.weight
      (classicalHodgeBasis V H M.weight M.sheet).1)
  simp [minimalGhostQuotientDetector_primitiveClass] at hval
  exact M.separator.detects_basis hval

/-- Same-weight verified geometric programs descend to the primitive quotient,
because the lower image is invariant under post-composition. -/
noncomputable def sameWeightPrimitiveAction
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (Q : GradedGeometricProgram V p p) :
    GeometricPrimitiveQuotient G p →ₗ[ℚ]
      GeometricPrimitiveQuotient G p :=
  (lowerProgramImageModule G p).mapQ
    (lowerProgramImageModule G p)
    (Q.cohomologyEval G)
    (by
      intro x hx
      exact lowerProgramImageModule_stable_sameWeight G p Q x hx)

/-- Exact action formula on representatives. -/
@[simp]
theorem sameWeightPrimitiveAction_primitiveClass
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (Q : GradedGeometricProgram V p p)
    (x : AmbientWeightCohomology H p) :
    sameWeightPrimitiveAction G p Q (primitiveClass G p x) =
      primitiveClass G p (Q.cohomologyEval G x) := by
  exact Submodule.mapQ_apply
    (lowerProgramImageModule G p)
    (lowerProgramImageModule G p)
    (Q.cohomologyEval G) x

/-- Dual pullback action on primitive quotient detectors. -/
noncomputable def primitiveDetectorPullback
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (Q : GradedGeometricProgram V p p)
    (ell : GeometricPrimitiveQuotient G p →ₗ[ℚ] ℚ) :
    GeometricPrimitiveQuotient G p →ₗ[ℚ] ℚ :=
  ell.comp (sameWeightPrimitiveAction G p Q)

/-- Pullback evaluation can be computed upstairs before quotienting. -/
@[simp]
theorem primitiveDetectorPullback_primitiveClass
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (Q : GradedGeometricProgram V p p)
    (ell : GeometricPrimitiveQuotient G p →ₗ[ℚ] ℚ)
    (x : AmbientWeightCohomology H p) :
    primitiveDetectorPullback G p Q ell (primitiveClass G p x) =
      ell (primitiveClass G p (Q.cohomologyEval G x)) := by
  rfl

/-- **GEOMETRIC PRIMITIVE FAILURE PACKET.**
Every Stage-2G failure produces a nonzero class and a nonzero detector on one
geometric primitive quotient, while every verified same-weight program acts
canonically on that quotient.  No externalization or algebraicity hypothesis
is introduced. -/
theorem not_hodge_yields_nontrivial_geometricPrimitiveQuotient
    (G : GeometricCycleClassSpine V H)
    (hnot : ¬ BigradedBettiHodgeStatement V H) :
    ∃ M : MinimalPrimitiveGhost G,
      primitiveClass G M.weight
          (classicalHodgeBasis V H M.weight M.sheet).1 ≠ 0
      ∧ minimalGhostQuotientDetector G M ≠ 0 := by
  let M := minimalPrimitiveGhostOfFailure G hnot
  exact ⟨M,
    minimalGhost_primitiveClass_ne_zero G M,
    minimalGhostQuotientDetector_ne_zero G M⟩

#check lowerProgramImageSet
#check lowerProgramImageModule
#check lowerProgramImageSet_stable_sameWeight
#check lowerProgramImageModule_stable_sameWeight
#check minimalGhost_lowerProgramImage_le_kernel
#check minimalGhost_sheet_not_mem_lowerProgramImage
#check GeometricPrimitiveQuotient
#check primitiveClass
#check minimalGhost_primitiveClass_ne_zero
#check minimalGhostQuotientDetector
#check minimalGhostQuotientDetector_ne_zero
#check sameWeightPrimitiveAction
#check primitiveDetectorPullback
#check not_hodge_yields_nontrivial_geometricPrimitiveQuotient

#print axioms lowerProgramImageModule_stable_sameWeight
#print axioms minimalGhost_lowerProgramImage_le_kernel
#print axioms minimalGhost_primitiveClass_ne_zero
#print axioms minimalGhostQuotientDetector_ne_zero
#print axioms sameWeightPrimitiveAction
#print axioms not_hodge_yields_nontrivial_geometricPrimitiveQuotient

end GSTClassicalHodgeGeometricPrimitiveQuotient
