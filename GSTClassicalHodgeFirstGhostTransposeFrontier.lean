import GSTClassicalHodgeUniversalFirstGhostTransposeClosure

/-!
# GST CLASSICAL HODGE — FIRST GHOST TRANSPOSE FRONTIER

The correspondence frontier already proves that a hypothetical Hodge failure
selects a least trace-zero primitive ghost for which **every** one-state finite
correspondence return is forbidden.  The newer transpose/mod-atomic route is a
strictly more geometric packet: one actual bi-finite closed correspondence,
its transpose/adjoint geometry, and a nonzero-scaled round trip modulo the
full algebraic cycle-class span.

This file projects the global failure theorem directly onto that latest packet.
It gives the repair layer one canonical frontier statement: at the least bad
successor, no choice of bi-finite correspondence and no choice of perfect
pairings can support the required transpose/mod-atomic return on the selected
first ghost.

Conversely, the already-established universal transpose-return theorem is
re-exported through a named principle.  Thus the active mathematical burden is
not an unrestricted operator-realization problem: it is exactly the existence
of this one-state geometric packet at each hypothetical first failure.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeFirstGhostTransposeFrontier

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeAtomicDefectDuality
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeProjectiveDegreeTrace
open GSTClassicalHodgePrimitiveAtomicDefectReduction
open GSTClassicalHodgeTraceZeroPrimitiveTomographyGhost
open GSTClassicalHodgeHodgeFunctorialProjectiveDynamics
open GSTClassicalHodgeFirstPrimitiveProjectiveFailure
open GSTClassicalHodgeFiniteClosedCorrespondence
open GSTClassicalHodgeFiniteClosedCorrespondenceTranspose
open GSTClassicalHodgeFirstGhostCorrespondenceFrontier
open GSTClassicalHodgePolarizedHodgeGhost
open GSTClassicalHodgeFirstGhostTransposeModAtomicClosure
open GSTClassicalHodgeUniversalFirstGhostTransposeClosure

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- **GLOBAL FIRST-GHOST TRANSPOSE FRONTIER.**
Every failure of the Stage-2G Hodge statement produces a least successor ghost
for which the latest genuine bi-finite transpose/mod-atomic packet is
impossible, uniformly over every correspondence and every pair of perfect
Hodge-fiber pairings. -/
theorem failure_yields_forbidden_firstGhostTransposeModAtomic
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
      ∧ (∀ K : BiFiniteClosedCorrespondence V,
          ∀ P : PerfectHodgeFiberPairing (V := V) (H := H) (p + 1),
          ∀ Q : PerfectHodgeFiberPairing (V := V) (H := H) p,
            ¬ Nonempty
              (FirstGhostTransposeModAtomicGeometry
                (G := R.spine) (D := D) (T := T) (p := p)
                (anchor (p + 1)) E K P Q)) := by
  rcases failure_yields_forbidden_firstGhostCorrespondenceReturn
      R T D anchor hzero hnot with
    ⟨p, E, hlower, hE, hforbid⟩
  refine ⟨p, E, hlower, hE, ?_⟩
  intro K P Q hpacket
  let S := Classical.choice hpacket
  apply hforbid K.toFiniteClosedCorrespondence
  exact ⟨S.toFirstGhostCorrespondenceReturn⟩

/-- The exact universal geometric principle consumed by the latest closure
route.  It is local to the canonical ghost extracted from a predecessor-zero /
successor-nonzero defect pair. -/
def UniversalFirstGhostTransposeModAtomicReturnPrinciple
    (R : HodgeFunctorialGeometricSemantics V H)
    (T : ProjectiveDegreeTraceSemantics V H)
    (D : LefschetzPrimitiveDecomposition R.spine)
    (anchor : ∀ q : Nat,
      GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor R.spine T q)
    (pairing : ∀ q : Nat,
      PerfectHodgeFiberPairing (V := V) (H := H) q) : Prop :=
  ∀ p : Nat,
  ∀ hsource : atomicDefectLinearMap V H p = 0,
  ∀ htarget : atomicDefectLinearMap V H (p + 1) ≠ 0,
    let P0 := packetOfNextWeightFailure
      R T D (anchor (p + 1)) hsource htarget
    ∃ K : BiFiniteClosedCorrespondence V,
      Nonempty
        (FirstGhostTransposeModAtomicGeometry
          (G := R.spine) (D := D) (T := T) (p := p)
          (anchor (p + 1)) P0.ghost K
          (pairing (p + 1)) (pairing p))

/-- The named universal principle closes the complete Stage-2G Hodge statement
by the established first-ghost transpose theorem. -/
theorem bigradedBettiHodge_of_universalFirstGhostTransposeModAtomicReturnPrinciple
    (R : HodgeFunctorialGeometricSemantics V H)
    (T : ProjectiveDegreeTraceSemantics V H)
    (D : LefschetzPrimitiveDecomposition R.spine)
    (anchor : ∀ q : Nat,
      GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor R.spine T q)
    (pairing : ∀ q : Nat,
      PerfectHodgeFiberPairing (V := V) (H := H) q)
    (hzero : atomicDefectLinearMap V H 0 = 0)
    (hReturn : UniversalFirstGhostTransposeModAtomicReturnPrinciple
      R T D anchor pairing) :
    BigradedBettiHodgeStatement V H := by
  exact bigradedBettiHodge_of_firstGhostTransposeModAtomicReturns
    R T D anchor pairing hzero hReturn

/-- A genuine Hodge failure and the universal first-ghost transpose-return
principle are incompatible.  This is the global obstruction form of the same
frontier. -/
theorem failure_forbids_universalFirstGhostTransposeModAtomicReturnPrinciple
    (R : HodgeFunctorialGeometricSemantics V H)
    (T : ProjectiveDegreeTraceSemantics V H)
    (D : LefschetzPrimitiveDecomposition R.spine)
    (anchor : ∀ q : Nat,
      GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor R.spine T q)
    (pairing : ∀ q : Nat,
      PerfectHodgeFiberPairing (V := V) (H := H) q)
    (hzero : atomicDefectLinearMap V H 0 = 0)
    (hnot : ¬ BigradedBettiHodgeStatement V H) :
    ¬ UniversalFirstGhostTransposeModAtomicReturnPrinciple
      R T D anchor pairing := by
  intro hReturn
  exact hnot
    (bigradedBettiHodge_of_universalFirstGhostTransposeModAtomicReturnPrinciple
      R T D anchor pairing hzero hReturn)

#check failure_yields_forbidden_firstGhostTransposeModAtomic
#check UniversalFirstGhostTransposeModAtomicReturnPrinciple
#check bigradedBettiHodge_of_universalFirstGhostTransposeModAtomicReturnPrinciple
#check failure_forbids_universalFirstGhostTransposeModAtomicReturnPrinciple

#print axioms failure_yields_forbidden_firstGhostTransposeModAtomic
#print axioms bigradedBettiHodge_of_universalFirstGhostTransposeModAtomicReturnPrinciple
#print axioms failure_forbids_universalFirstGhostTransposeModAtomicReturnPrinciple

end GSTClassicalHodgeFirstGhostTransposeFrontier
