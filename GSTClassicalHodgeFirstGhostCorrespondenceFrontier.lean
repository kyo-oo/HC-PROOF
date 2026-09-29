import GSTClassicalHodgeFirstGhostCorrespondenceCollision
import GSTClassicalHodgePrimitiveProjectiveFailureCrown
import GSTClassicalHodgeFirstPrimitiveProjectiveFailure

/-!
# GST CLASSICAL HODGE — FIRST GHOST CORRESPONDENCE FRONTIER

This file packages the current noncircular reduction as one global theorem.

Given the genuine Hodge-functorial projective semantics, projective degree
trace semantics, a Lefschetz primitive decomposition, trace anchors, and the
weight-zero base case, any failure of the Stage-2G Hodge statement determines:

* a least bad successor weight `p+1`;
* zero Hodge defect at every weight `q <= p`;
* a canonical trace-zero primitive tomography ghost `E` at `p+1`;
* and the impossibility of a one-state finite-correspondence return for `E`
  through the predecessor weight.

Therefore the remaining geometry has a precise target.  To refute the
counterexample, construct one actual finite closed correspondence from
codimension `p+1` to `p` satisfying only:

1. Hodge preservation on `E.traceZeroClass`;
2. principal-cut return to a nonzero scalar multiple of `E.traceZeroClass`
   modulo the atomic cycle-class span.

No whole-fiber matrix units or global correspondence irreducibility occur.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeFirstGhostCorrespondenceFrontier

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeAtomicDefectDuality
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeProjectiveDegreeTrace
open GSTClassicalHodgePrimitiveAtomicDefectReduction
open GSTClassicalHodgeTraceZeroPrimitiveTomographyGhost
open GSTClassicalHodgeHodgeFunctorialProjectiveDynamics
open GSTClassicalHodgePrimitiveProjectiveFailureCrown
open GSTClassicalHodgeFirstPrimitiveProjectiveFailure
open GSTClassicalHodgeFiniteClosedCorrespondence
open GSTClassicalHodgeFirstGhostCorrespondenceCollision

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- **GLOBAL FIRST-GHOST CORRESPONDENCE FRONTIER.**
Every Hodge failure has a least primitive trace-zero ghost for which the
single-state predecessor correspondence return is forbidden. -/
theorem failure_yields_forbidden_firstGhostCorrespondenceReturn
    (R : HodgeFunctorialGeometricSemantics V H)
    (T : ProjectiveDegreeTraceSemantics V H)
    (D : LefschetzPrimitiveDecomposition R.spine)
    (anchor : ∀ q : Nat,
      GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor R.spine T q)
    (hzero : atomicDefectLinearMap V H 0 = 0)
    (hnot : ¬ BigradedBettiHodgeStatement V H) :
    ∃ p : Nat,
    ∃ E : TraceZeroPrimitiveTomographyGhost (anchor (p + 1)) D,
      (∀ q : Nat, q ≤ p → atomicDefectLinearMap V H q = 0)
      ∧ E.defectState ≠ 0
      ∧ (∀ K : FiniteClosedCorrespondence V,
          ¬ Nonempty
            (FirstGhostCorrespondenceReturn
              (G := R.spine) (D := D) (T := T) (p := p)
              (anchor (p + 1)) E K)) := by
  let F := firstAtomicDefectWeightOfFailure (V := V) (H := H) hzero hnot
  obtain ⟨p, hp⟩ := firstAtomicDefectWeight_eq_succ F
  have hlower : ∀ q : Nat, q ≤ p → atomicDefectLinearMap V H q = 0 :=
    firstAtomicDefect_all_lower_zero F hp
  have hsource : atomicDefectLinearMap V H p = 0 := hlower p (by rfl)
  have htarget : atomicDefectLinearMap V H (p + 1) ≠ 0 := by
    rw [← hp]
    exact F.defect_ne_zero
  let P := packetOfNextWeightFailure R T D (anchor (p + 1)) hsource htarget
  refine ⟨p, P.ghost, hlower, P.ghost.defectState_ne_zero, ?_⟩
  intro K hReturn
  let C := Classical.choice hReturn
  exact C.firstFailure_forbids_ghost_correspondence_return F hp

/-- Contrapositive closure criterion in the new minimal interface: if every
candidate first primitive ghost admits one genuine predecessor correspondence
return, then the full Stage-2G Hodge statement follows. -/
theorem bigradedBettiHodge_of_firstGhostCorrespondenceReturns
    (R : HodgeFunctorialGeometricSemantics V H)
    (T : ProjectiveDegreeTraceSemantics V H)
    (D : LefschetzPrimitiveDecomposition R.spine)
    (anchor : ∀ q : Nat,
      GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor R.spine T q)
    (hzero : atomicDefectLinearMap V H 0 = 0)
    (returns :
      ∀ p : Nat,
      ∀ hsource : atomicDefectLinearMap V H p = 0,
      ∀ htarget : atomicDefectLinearMap V H (p + 1) ≠ 0,
        let P := packetOfNextWeightFailure R T D (anchor (p + 1)) hsource htarget
        ∃ K : FiniteClosedCorrespondence V,
          Nonempty
            (FirstGhostCorrespondenceReturn
              (G := R.spine) (D := D) (T := T) (p := p)
              (anchor (p + 1)) P.ghost K)) :
    BigradedBettiHodgeStatement V H := by
  by_contra hnot
  let F := firstAtomicDefectWeightOfFailure (V := V) (H := H) hzero hnot
  obtain ⟨p, hp⟩ := firstAtomicDefectWeight_eq_succ F
  have hsource : atomicDefectLinearMap V H p = 0 :=
    firstAtomicDefect_predecessor_zero F hp
  have htarget : atomicDefectLinearMap V H (p + 1) ≠ 0 := by
    rw [← hp]
    exact F.defect_ne_zero
  let P := packetOfNextWeightFailure R T D (anchor (p + 1)) hsource htarget
  rcases returns p hsource htarget with ⟨K, hK⟩
  let C := Classical.choice hK
  exact C.firstFailure_forbids_ghost_correspondence_return F hp

#check failure_yields_forbidden_firstGhostCorrespondenceReturn
#check bigradedBettiHodge_of_firstGhostCorrespondenceReturns

#print axioms failure_yields_forbidden_firstGhostCorrespondenceReturn
#print axioms bigradedBettiHodge_of_firstGhostCorrespondenceReturns

end GSTClassicalHodgeFirstGhostCorrespondenceFrontier
