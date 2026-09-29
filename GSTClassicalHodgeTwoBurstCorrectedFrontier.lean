import GSTClassicalHodgeGenuineCycleClassGeometry
import GSTClassicalHodgeTomographySynchronizationAudit
import GSTClassicalHodgeProjectiveVisibilityNoGo
import GSTClassicalHodgeMultiplicityForgettingKernel
import GSTClassicalHodgeLimitlessSpinePropagation

/-!
# GST CLASSICAL HODGE — CORRECTED TWO-BURST FRONTIER

This is the stable mathematical receipt of the two-burst reconstruction.

The original route mixed three logically different questions:

1. whether the Stage-2G cycle-class field was genuinely geometric;
2. whether GST tomography detects arbitrary classical multiplicity;
3. whether a native/projective operator can move an algebraic source into the
   ghost direction.

The upgraded files separate them completely.

* `GenuineCycleClassGeometry` excludes the zero-cycle-class semantic
  countermodel using positive projective degree.
* Fibered GST tomography retains every classical multiplicity sheet, and a
  Hodge failure is exactly equivalent to a synchronized nonzero atomic defect
  plus nonzero GST tomography moment.
* Ordinary cycle-natural/projective images of an algebraic ghost-spine source
  remain algebraic and therefore have zero separator readout.  They cannot be
  used as the missing horizontal motion.
* Forgetting multiplicity back to the one-generator-per-weight GST base is
  noninjective whenever two sheets occur.

Thus the only remaining legitimate mathematical task is an independently
geometric extinction theorem for the synchronized atomic-defect/tomography
packet.  That theorem must act on the quotient/pairing obstruction itself; it
cannot be obtained by renaming projective-orbit irreducibility, basis-cycle
realization, or exact cycle-natural GST matrix units.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeTwoBurstCorrectedFrontier

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeGenuineCycleClassGeometry
open GSTClassicalHodgeTomographySynchronizationAudit
open GSTClassicalHodgeAtomicDefectTomographySynchronization
open GSTClassicalHodgeProjectiveVisibilityNoGo
open GSTClassicalHodgeProjectiveDetectorVisibility
open GSTClassicalHodgeOmniversalSeparatorGhostCrown
open GSTClassicalHodgeLimitlessSpinePropagation
open GSTClassicalHodgeMultiplicityForgettingKernel

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Genuine geometry gives nonzero cycle class to every native codimension
point.  This is the semantic zero-map exclusion component of the final
frontier. -/
theorem genuine_point_cycleClass_nonzero
    (J : GenuineCycleClassGeometry V H)
    (q : Nat)
    (x : CodimensionPoint V.X q) :
    H.cycleClass q (codimensionPointCycle V.X q x) ≠ 0 :=
  J.point_cycleClass_ne_zero q x

/-- Failure has the exact synchronized quotient/tomography normal form under
any genuine geometry package; no extra horizontal certificate is needed for
this equivalence. -/
theorem failure_iff_synchronized_defect_tomography
    (J : GenuineCycleClassGeometry V H) :
    ¬ BigradedBettiHodgeStatement V H ↔
      Nonempty (SynchronizedAtomicDefectGhost J.spine) :=
  not_hodge_iff_nonempty_synchronizedAtomicDefectGhost J.spine

/-- A surviving ghost cannot be made visible by an ordinary genuine projective
kernel on the canonical algebraic spine source. -/
theorem projective_visibility_blocked
    (J : GenuineCycleClassGeometry V H)
    (M : NativeMassCycleClassBridge V H)
    (E : OmniversalSeparatorGhost J.spine) :
    IsEmpty (ProjectiveDetectorVisible J.spine M E) :=
  no_projectiveDetectorVisible J.spine M E

/-- Multiplicity cannot be discarded when a weight has two distinct sheets. -/
theorem baseGST_forgetting_not_injective
    (p : Nat)
    (i j : GSTClassicalHodgeFiberedCosmology.ClassicalHodgeBasisIndex V H p)
    (hij : i ≠ j) :
    ¬ Function.Injective
      (@GSTClassicalHodgeFiberedCosmology.forgetMultiplicityToGST V H) :=
  forgetMultiplicityToGST_not_injective_of_two_sheets i j hij

/-- **CORRECTED TWO-BURST CROWN.**

The theorem packages the semantically genuine nonvanishing, exact transformed
failure normal form, and projective visibility no-go in one place.  It is a
frontier theorem, not a false unconditional Hodge claim. -/
theorem corrected_two_burst_crown
    (J : GenuineCycleClassGeometry V H)
    (M : NativeMassCycleClassBridge V H) :
    (∀ q : Nat, ∀ x : CodimensionPoint V.X q,
      H.cycleClass q (codimensionPointCycle V.X q x) ≠ 0)
    ∧ (¬ BigradedBettiHodgeStatement V H ↔
        Nonempty (SynchronizedAtomicDefectGhost J.spine))
    ∧ (∀ E : OmniversalSeparatorGhost J.spine,
        IsEmpty (ProjectiveDetectorVisible J.spine M E)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro q x
    exact genuine_point_cycleClass_nonzero J q x
  · exact failure_iff_synchronized_defect_tomography J
  · intro E
    exact projective_visibility_blocked J M E

#check genuine_point_cycleClass_nonzero
#check failure_iff_synchronized_defect_tomography
#check projective_visibility_blocked
#check baseGST_forgetting_not_injective
#check corrected_two_burst_crown

#print axioms genuine_point_cycleClass_nonzero
#print axioms failure_iff_synchronized_defect_tomography
#print axioms projective_visibility_blocked
#print axioms corrected_two_burst_crown

end GSTClassicalHodgeTwoBurstCorrectedFrontier
