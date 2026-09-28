import GSTClassicalHodgeGenuineSemanticClosure
import GSTClassicalHodgeVisibilityEquivalenceAudit

/-!
# GST CLASSICAL HODGE — PROJECTIVE ORBIT IRREDUCIBILITY AUDIT

This file prevents a subtle circularity from re-entering the two-burst route.

`ProjectiveOrbitIrreducibility` is a useful exact description of the missing
horizontal coupling, but it is not yet an independently derived theorem of the
projective geometry.  Indeed, once the native-mass spine is available it
specializes to projective detector visibility for every omniversal ghost, and
the existing visibility-equivalence audit proves that this is Hodge-strength.

Consequently downstream work may use this structure as a *conditional closure
certificate* or as a target for a genuinely independent construction, but must
not install it as a free field of the semantic geometry package.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeProjectiveOrbitIrreducibilityAudit

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeSynchronizedDefectOrbit
open GSTClassicalHodgeOmniversalSeparatorGhostCrown
open GSTClassicalHodgeProjectiveDetectorVisibility
open GSTClassicalHodgeVisibilityEquivalenceAudit
open GSTClassicalHodgeGenuineCycleClassGeometry
open GSTClassicalHodgeProjectiveVisibilitySeparation
open GSTClassicalHodgeGenuineSemanticClosure
open GSTClassicalHodgeLimitlessSpinePropagation

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Orbit irreducibility immediately gives the universal visibility predicate
which the existing audit identifies with the Hodge target. -/
theorem projectiveOrbitIrreducibility_implies_visibilityForAllGhosts
    (J : GenuineCycleClassGeometry V H)
    (R : ProjectiveOrbitIrreducibility V H J)
    (M : NativeMassCycleClassBridge V H) :
    ∀ E : OmniversalSeparatorGhost J.spine,
      Nonempty (ProjectiveDetectorVisible J.spine M E) := by
  intro E
  exact exists_projectiveDetectorVisible J R M E

/-- Machine-visible circularity guard: under the native-mass bridge, a complete
projective-orbit irreducibility certificate is already strong enough to prove
the full Stage-2G Hodge statement. -/
theorem projectiveOrbitIrreducibility_implies_hodge
    (J : GenuineCycleClassGeometry V H)
    (R : ProjectiveOrbitIrreducibility V H J)
    (M : NativeMassCycleClassBridge V H) :
    BigradedBettiHodgeStatement V H := by
  exact
    (hodge_iff_projectiveDetectorVisibility J.spine M).2
      (projectiveOrbitIrreducibility_implies_visibilityForAllGhosts J R M)

/-- The conditional closure theorem and the visibility-equivalence audit land
on the same target, providing an independent consistency check on the new
source organization. -/
theorem conditional_closure_agrees_with_visibility_audit
    (J : GenuineCycleClassGeometry V H)
    (R : ProjectiveOrbitIrreducibility V H J)
    (M : NativeMassCycleClassBridge V H) :
    bigradedBettiHodge_of_projectiveOrbitIrreducibility J R M =
      projectiveOrbitIrreducibility_implies_hodge J R M := by
  apply proof_irrel

#check projectiveOrbitIrreducibility_implies_visibilityForAllGhosts
#check projectiveOrbitIrreducibility_implies_hodge
#check conditional_closure_agrees_with_visibility_audit

#print axioms projectiveOrbitIrreducibility_implies_visibilityForAllGhosts
#print axioms projectiveOrbitIrreducibility_implies_hodge
#print axioms conditional_closure_agrees_with_visibility_audit

end GSTClassicalHodgeProjectiveOrbitIrreducibilityAudit
