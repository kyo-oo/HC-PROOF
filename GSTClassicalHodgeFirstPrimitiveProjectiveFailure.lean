import GSTClassicalHodgePrimitiveProjectiveDualOrbit

/-!
# GST CLASSICAL HODGE — FIRST PRIMITIVE PROJECTIVE FAILURE

The preceding files convert a *local* first step

  defect(p) = 0,   defect(p+1) != 0

into a trace-zero primitive projective primal/dual packet.  This file removes
the local hypothesis from the counterexample analysis by well-ordering the
natural weights.

Assuming the already available weight-zero base case, any failure of the full
Stage-2G Hodge statement has a least weight with nonzero atomic defect.  That
least weight is positive, hence is `p+1`; every weight `q <= p` is defect-free.
The local primitive reduction therefore applies canonically at this first
failure.

The result is a global noncircular counterexample normal form:

* all lower weights have zero atomic defect;
* the first bad weight has a trace-zero primitive tomography ghost;
* its genuine projective defect orbit module is nonzero;
* its dual algebraic annihilator is nonzero;
* the identity projective matrix coefficient is nonzero.

No geometric irreducibility or multiplicity matrix-unit externalization is
inserted.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeFirstPrimitiveProjectiveFailure

open GSTGeometricRealizationStage2G
open GSTClassicalHodgeAtomicDefectDuality
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeProjectiveDegreeTrace
open GSTClassicalHodgePrimitiveAtomicDefectReduction
open GSTClassicalHodgeHodgeFunctorialProjectiveDynamics
open GSTClassicalHodgePrimitiveProjectiveFailureCrown
open GSTClassicalHodgePrimitiveProjectiveMomentProfile
open GSTClassicalHodgePrimitiveProjectiveDualOrbit

variable {V : GSTProjectiveOverC.SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- A least positive atomic-defect weight, recorded together with vanishing of
all earlier weights. -/
structure FirstAtomicDefectWeight
    (V : GSTProjectiveOverC.SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) where
  weight : Nat
  positive : 0 < weight
  defect_ne_zero : atomicDefectLinearMap V H weight ≠ 0
  lower_zero : ∀ q : Nat, q < weight → atomicDefectLinearMap V H q = 0

/-- If weight zero is defect-free and the full Hodge statement fails, a least
positive defect weight exists. -/
noncomputable def firstAtomicDefectWeightOfFailure
    (hzero : atomicDefectLinearMap V H 0 = 0)
    (hnot : ¬ BigradedBettiHodgeStatement V H) :
    FirstAtomicDefectWeight V H := by
  have hex : ∃ q : Nat, atomicDefectLinearMap V H q ≠ 0 := by
    by_contra hnone
    push_neg at hnone
    apply hnot
    exact (bigradedBettiHodgeStatement_iff_atomicDefect_zero V H).2 hnone
  let n := Nat.find hex
  have hn_bad : atomicDefectLinearMap V H n ≠ 0 := Nat.find_spec hex
  have hn_pos : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := by omega
    subst n
    exact hn_bad hzero
  refine {
    weight := n
    positive := hn_pos
    defect_ne_zero := hn_bad
    lower_zero := ?_
  }
  intro q hq
  by_contra hqbad
  exact (Nat.find_min' hex hq) hqbad

/-- The least positive defect weight is canonically a successor. -/
theorem firstAtomicDefectWeight_eq_succ
    (F : FirstAtomicDefectWeight V H) :
    ∃ p : Nat, F.weight = p + 1 := by
  cases F.weight with
  | zero => omega
  | succ p => exact ⟨p, by omega⟩

/-- At the predecessor of the first bad weight the atomic defect vanishes. -/
theorem firstAtomicDefect_predecessor_zero
    (F : FirstAtomicDefectWeight V H)
    {p : Nat}
    (hp : F.weight = p + 1) :
    atomicDefectLinearMap V H p = 0 := by
  apply F.lower_zero p
  omega

/-- In fact every weight at or below that predecessor is defect-free. -/
theorem firstAtomicDefect_all_lower_zero
    (F : FirstAtomicDefectWeight V H)
    {p : Nat}
    (hp : F.weight = p + 1) :
    ∀ q : Nat, q ≤ p → atomicDefectLinearMap V H q = 0 := by
  intro q hq
  apply F.lower_zero q
  omega

/-- **GLOBAL FIRST-FAILURE PRIMITIVE PROJECTIVE PACKET.**
Any Stage-2G failure, after the weight-zero base case, canonically yields a
first bad successor weight and the paired primitive projective representation
packet constructed in the preceding layers. -/
theorem failure_yields_firstPrimitiveProjectiveDualPacket
    (R : HodgeFunctorialGeometricSemantics V H)
    (T : ProjectiveDegreeTraceSemantics V H)
    (D : LefschetzPrimitiveDecomposition R.spine)
    (anchor : ∀ q : Nat, TraceAnchor R.spine T q)
    (hzero : atomicDefectLinearMap V H 0 = 0)
    (hnot : ¬ BigradedBettiHodgeStatement V H) :
    ∃ p : Nat,
      (∀ q : Nat, q ≤ p → atomicDefectLinearMap V H q = 0)
      ∧ Nonempty
        (PrimitiveProjectiveDualPacket R T D (anchor (p + 1))) := by
  let F := firstAtomicDefectWeightOfFailure (V := V) (H := H) hzero hnot
  obtain ⟨p, hp⟩ := firstAtomicDefectWeight_eq_succ F
  have hlower :
      ∀ q : Nat, q ≤ p → atomicDefectLinearMap V H q = 0 :=
    firstAtomicDefect_all_lower_zero F hp
  have hsource : atomicDefectLinearMap V H p = 0 := hlower p (by rfl)
  have htarget : atomicDefectLinearMap V H (p + 1) ≠ 0 := by
    simpa [hp] using F.defect_ne_zero
  refine ⟨p, hlower, ?_⟩
  exact ⟨dualPacketOfNextWeightFailure R T D (anchor (p + 1)) hsource htarget⟩

/-- Scalar form of the global first-failure normal form: every Hodge failure
produces a first bad weight carrying a trace-zero primitive ghost and a genuine
projective word with nonzero moment and nonzero defect action. -/
theorem failure_yields_firstNonzeroProjectiveMoment
    (R : HodgeFunctorialGeometricSemantics V H)
    (T : ProjectiveDegreeTraceSemantics V H)
    (D : LefschetzPrimitiveDecomposition R.spine)
    (anchor : ∀ q : Nat, TraceAnchor R.spine T q)
    (hzero : atomicDefectLinearMap V H 0 = 0)
    (hnot : ¬ BigradedBettiHodgeStatement V H) :
    ∃ p : Nat,
    ∃ E : GSTClassicalHodgeTraceZeroPrimitiveTomographyGhost.TraceZeroPrimitiveTomographyGhost
      (anchor (p + 1)) D,
    ∃ w : HodgeFunctorialGeometricSemantics.ProjectiveHodgeWord R (p + 1),
      (∀ q : Nat, q ≤ p → atomicDefectLinearMap V H q = 0)
      ∧ projectiveGhostMoment E w ≠ 0
      ∧ w.defectOperator E.defectState ≠ 0 := by
  obtain ⟨p, hlower, hpacket⟩ :=
    failure_yields_firstPrimitiveProjectiveDualPacket R T D anchor hzero hnot
  let P := Classical.choice hpacket
  let w : HodgeFunctorialGeometricSemantics.ProjectiveHodgeWord R (p + 1) :=
    HodgeFunctorialGeometricSemantics.ProjectiveHodgeWord.id
  have hm : projectiveGhostMoment P.ghost w ≠ 0 := by
    simpa [w] using projectiveGhostMoment_id_ne_zero P.ghost
  have hd : w.defectOperator P.ghost.defectState ≠ 0 :=
    defect_ne_zero_of_projectiveGhostMoment_ne_zero P.ghost w hm
  exact ⟨p, P.ghost, w, hlower, hm, hd⟩

#check FirstAtomicDefectWeight
#check firstAtomicDefectWeightOfFailure
#check firstAtomicDefectWeight_eq_succ
#check firstAtomicDefect_predecessor_zero
#check firstAtomicDefect_all_lower_zero
#check failure_yields_firstPrimitiveProjectiveDualPacket
#check failure_yields_firstNonzeroProjectiveMoment

#print axioms firstAtomicDefectWeightOfFailure
#print axioms firstAtomicDefect_all_lower_zero
#print axioms failure_yields_firstPrimitiveProjectiveDualPacket
#print axioms failure_yields_firstNonzeroProjectiveMoment

end GSTClassicalHodgeFirstPrimitiveProjectiveFailure
