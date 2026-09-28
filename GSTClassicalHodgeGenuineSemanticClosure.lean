import GSTClassicalHodgeTomographyVisibilityCrown
import GSTClassicalHodgeOmniversalSeparatorGhostCrown

/-!
# GST CLASSICAL HODGE — GENUINE SEMANTIC CLOSURE

This is the Burst-2 semantic landing for the strengthened cycle-class package.
It is intentionally *not* a theorem over arbitrary `HodgeBigradedBettiData`:
the Stage-2G semantic-rigidity audit proves that such a theorem is impossible
because the raw carrier admits the zero cycle-class countermodel.

Instead, once a Stage-2G package is certified by `GenuineCycleClassGeometry`
and carries the already-developed native-mass bridge, the projective tomography
visibility crown eliminates every omniversal separator ghost.  The existing
single-sheet/omniversal equivalence then gives the full rational `(p,p)`
cycle-class landing.

The logical route is therefore exactly:

  genuine cycle-class geometry
    + native nonzero spine
    -> projective orbit visibility
    -> nonzero finite GST tomography hit
    -> no omniversal separator ghost
    -> `BigradedBettiHodgeStatement`.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeGenuineSemanticClosure

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeSynchronizedDefectOrbit
open GSTClassicalHodgeOmniversalSeparatorGhostCrown
open GSTClassicalHodgeGenuineCycleClassGeometry
open GSTClassicalHodgeTomographyVisibilityCrown

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Any negation of the Hodge target contradicts the genuine projective
visibility/tomography crown. -/
theorem not_hodge_impossible
    (J : GenuineCycleClassGeometry V H)
    (M : NativeMassCycleClassBridge V H)
    (hnot : ¬ BigradedBettiHodgeStatement V H) : False := by
  rcases
      (not_hodge_iff_nonempty_omniversalSeparatorGhost J.spine).mp hnot with
    ⟨E⟩
  exact omniversalGhost_false J M E

/--
**GENUINE SEMANTIC HODGE CLOSURE.**

The full Stage-2G rational `(p,p)` cycle-class landing follows from the
strengthened genuine cycle-class geometry plus the native-mass bridge.
-/
theorem bigradedBettiHodge_of_genuineCycleClassGeometry
    (J : GenuineCycleClassGeometry V H)
    (M : NativeMassCycleClassBridge V H) :
    BigradedBettiHodgeStatement V H := by
  exact
    (hodge_iff_no_omniversalSeparatorGhost J.spine).2
      (no_omniversalSeparatorGhost J M)

/-- Direct contradiction form exposing the terminal projective-tomography
collision selected by any alleged counterexample. -/
theorem counterexample_yields_projective_tomography_contradiction
    (J : GenuineCycleClassGeometry V H)
    (M : NativeMassCycleClassBridge V H)
    (hnot : ¬ BigradedBettiHodgeStatement V H) :
    ∃ E : OmniversalSeparatorGhost J.spine,
      Nonempty
        (GSTClassicalHodgeProjectiveDetectorMomentCollision.ProjectiveDetectorMomentHit
          J.spine M E)
      ∧ IsEmpty
        (GSTClassicalHodgeProjectiveDetectorMomentCollision.ProjectiveDetectorMomentHit
          J.spine M E) := by
  rcases
      (not_hodge_iff_nonempty_omniversalSeparatorGhost J.spine).mp hnot with
    ⟨E⟩
  refine ⟨E, omniversalGhost_has_tomography_moment_hit J M E, ?_⟩
  exact
    GSTClassicalHodgeProjectiveDetectorMomentCollision.no_projectiveDetectorMomentHit
      J.spine M E

/-- Public Burst-2 crown: Hodge closure and extinction of the exact
omniversal obstruction are obtained simultaneously. -/
theorem genuine_semantic_closure_crown
    (J : GenuineCycleClassGeometry V H)
    (M : NativeMassCycleClassBridge V H) :
    BigradedBettiHodgeStatement V H
    ∧ IsEmpty (OmniversalSeparatorGhost J.spine) := by
  exact ⟨
    bigradedBettiHodge_of_genuineCycleClassGeometry J M,
    no_omniversalSeparatorGhost J M⟩

#check not_hodge_impossible
#check bigradedBettiHodge_of_genuineCycleClassGeometry
#check counterexample_yields_projective_tomography_contradiction
#check genuine_semantic_closure_crown

#print axioms not_hodge_impossible
#print axioms bigradedBettiHodge_of_genuineCycleClassGeometry
#print axioms counterexample_yields_projective_tomography_contradiction
#print axioms genuine_semantic_closure_crown

end GSTClassicalHodgeGenuineSemanticClosure
