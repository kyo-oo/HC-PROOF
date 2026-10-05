import GSTClassicalHodgeCommonClassPlaneRealization

/-!
# GST CLASSICAL HODGE — COMMON-CLASS PLANE EQUIVALENCE AUDIT

This file closes a logical ambiguity in the ghost-adaptive plane formulation.

`GhostAdaptiveCommonClassPlaneCompleteness G` says that every hypothetical
omniversal separator ghost admits one common-class strict plane strike aimed at
its detected Hodge sheet.  The forward implication to the exact Stage-2G Hodge
statement was already proved in `GSTClassicalHodgeCommonClassPlaneRealization`.

The converse is immediate but mathematically important: if the Hodge statement
already holds, there are no omniversal separator ghosts, so the ghost-adaptive
plane-completeness proposition is vacuously true.  Consequently the
*ghost-adaptive* common-class plane law is not an independent theorem stronger
than the current development; it is an exact reformulation of Hodge.

This audit prevents a conditional realization package from being mistaken for
an unconditional derivation.  Any independent proof must construct the
geometric plane/carrier data from assumptions that do not already collapse to
this ghost-adaptive proposition.
-/

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeCommonClassPlaneEquivalence

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeOmniversalSeparatorGhostCrown
open GSTClassicalHodgeCommonClassPlaneRealization
open GSTClassicalHodgeOmniversalGhostBranchClosure

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Exact Hodge implies ghost-adaptive common-class plane completeness
vacuously, because exact Hodge eliminates every omniversal separator ghost. -/
theorem commonClassPlanes_of_hodge
    (G : GeometricCycleClassSpine V H)
    (hHodge : BigradedBettiHodgeStatement V H) :
    GhostAdaptiveCommonClassPlaneCompleteness G := by
  have hnone : IsEmpty (OmniversalSeparatorGhost G) :=
    (hodge_iff_no_omniversalSeparatorGhost G).1 hHodge
  intro E
  exact False.elim (isEmpty_iff.mp hnone E)

/-- **EXACT LOGICAL STATUS OF THE GHOST-ADAPTIVE PLANE LAW.**
The current ghost-adaptive common-class plane completeness statement is
logically equivalent to the exact Stage-2G Hodge statement. -/
theorem commonClassPlaneCompleteness_iff_hodge
    (G : GeometricCycleClassSpine V H) :
    GhostAdaptiveCommonClassPlaneCompleteness G ↔
      BigradedBettiHodgeStatement V H := by
  constructor
  · exact hodge_of_commonClassPlanes G
  · exact commonClassPlanes_of_hodge G

/-- The branch-level survival-plus-common-class package is likewise automatic
once Hodge already holds: both factors quantify only over hypothetical ghosts,
so both are vacuous when the ghost type is empty. -/
theorem survival_and_commonClassClosure_of_hodge
    (G : GeometricCycleClassSpine V H)
    (hHodge : BigradedBettiHodgeStatement V H) :
    GhostWeightNativeSeedSurvival G ∧
      GhostWeightPrimitiveCommonClassClosure G := by
  have hnone : IsEmpty (OmniversalSeparatorGhost G) :=
    (hodge_iff_no_omniversalSeparatorGhost G).1 hHodge
  constructor
  · intro E
    exact False.elim (isEmpty_iff.mp hnone E)
  · intro E
    exact False.elim (isEmpty_iff.mp hnone E)

/-- **BRANCH PACKAGE EQUIVALENCE.**
The full ghost-indexed survival/common-class closure package is also exactly
equivalent to Hodge, not an independent unconditional proof. -/
theorem survival_commonClassClosure_iff_hodge
    (G : GeometricCycleClassSpine V H) :
    (GhostWeightNativeSeedSurvival G ∧
      GhostWeightPrimitiveCommonClassClosure G) ↔
      BigradedBettiHodgeStatement V H := by
  constructor
  · rintro ⟨hsurvive, hclose⟩
    exact hodge_of_survival_and_commonClassPlaneClosure G hsurvive hclose
  · exact survival_and_commonClassClosure_of_hodge G

#check commonClassPlanes_of_hodge
#check commonClassPlaneCompleteness_iff_hodge
#check survival_and_commonClassClosure_of_hodge
#check survival_commonClassClosure_iff_hodge

#print axioms commonClassPlaneCompleteness_iff_hodge
#print axioms survival_commonClassClosure_iff_hodge

end GSTClassicalHodgeCommonClassPlaneEquivalence
