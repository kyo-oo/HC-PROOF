import GSTClassicalHodgePrimitiveProjectiveMomentProfile

/-!
# GST CLASSICAL HODGE — PRIMITIVE PROJECTIVE DUAL ORBIT

The primitive projective moment profile is a matrix coefficient of the genuine
projective word representation.  This file packages the contragredient side
explicitly.

A rational Hodge functional is called algebraically annihilating when it
vanishes on the actual algebraic Hodge subspace.  Every genuine projective word
preserves that property, because the corresponding projective pushforward is
atomic-natural and therefore preserves the algebraic Hodge subspace.

The primitive ghost functional is a nonzero element of this invariant dual
sector.  Its projective moment is exactly the evaluation of the dual-transformed
functional on the fixed primitive ghost state.

Thus a first Hodge failure has now been transformed into a paired nonzero
primal/dual representation object for the actual projective operator algebra:

* a nonzero projective defect orbit module;
* a nonzero algebraically-annihilating dual functional;
* a nonzero matrix coefficient between them.

No matrix-unit externalization, target-basis algebraicity, or projective
irreducibility is assumed.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgePrimitiveProjectiveDualOrbit

open GSTGeometricRealizationStage2G
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeAtomicDefectDuality
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeProjectiveDegreeTrace
open GSTClassicalHodgePrimitiveAtomicDefectReduction
open GSTClassicalHodgeTraceZeroPrimitiveTomographyGhost
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeHodgeFunctorialProjectiveDynamics
open GSTClassicalHodgePrimitiveProjectiveDefectModule
open GSTClassicalHodgePrimitiveProjectiveFailureCrown
open GSTClassicalHodgePrimitiveProjectiveMomentProfile

variable {V : GSTProjectiveOverC.SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- A Hodge functional lies in the dual algebraic annihilator when it kills
all genuinely algebraic Hodge classes. -/
def AnnihilatesAlgebraicHodge
    (ell : ClassicalHodgeFiber V H p →ₗ[ℚ] ℚ) : Prop :=
  ∀ alpha : ClassicalHodgeFiber V H p,
    alpha ∈ AlgebraicHodgeSubspace V H p → ell alpha = 0

/-- Contragredient action of one genuine projective word on Hodge functionals. -/
noncomputable def projectiveDualAction
    {R : HodgeFunctorialGeometricSemantics V H}
    {p : Nat}
    (w : HodgeFunctorialGeometricSemantics.ProjectiveHodgeWord R p)
    (ell : ClassicalHodgeFiber V H p →ₗ[ℚ] ℚ) :
    ClassicalHodgeFiber V H p →ₗ[ℚ] ℚ :=
  ell.comp
    (HodgeFunctorialGeometricSemantics.ProjectiveHodgeWord.eval w).hodge

/-- The dual algebraic annihilator is invariant under every actual projective
word. -/
theorem projectiveDualAction_preserves_annihilator
    {R : HodgeFunctorialGeometricSemantics V H}
    {p : Nat}
    (w : HodgeFunctorialGeometricSemantics.ProjectiveHodgeWord R p)
    (ell : ClassicalHodgeFiber V H p →ₗ[ℚ] ℚ)
    (hell : AnnihilatesAlgebraicHodge ell) :
    AnnihilatesAlgebraicHodge (projectiveDualAction w ell) := by
  intro alpha halpha
  apply hell
  exact
    HodgeFunctorialGeometricSemantics.ProjectiveHodgeWord.preserves_algebraicHodge
      w halpha

/-- Identity projective word acts trivially on the dual. -/
theorem projectiveDualAction_id
    {R : HodgeFunctorialGeometricSemantics V H}
    {p : Nat}
    (ell : ClassicalHodgeFiber V H p →ₗ[ℚ] ℚ) :
    projectiveDualAction
      (HodgeFunctorialGeometricSemantics.ProjectiveHodgeWord.id (R := R) (p := p))
      ell = ell := by
  ext alpha
  rfl

/-- Composition reverses on the dual, as expected for a contragredient
representation. -/
theorem projectiveDualAction_comp
    {R : HodgeFunctorialGeometricSemantics V H}
    {p : Nat}
    (u v : HodgeFunctorialGeometricSemantics.ProjectiveHodgeWord R p)
    (ell : ClassicalHodgeFiber V H p →ₗ[ℚ] ℚ) :
    projectiveDualAction
      (HodgeFunctorialGeometricSemantics.ProjectiveHodgeWord.comp u v) ell =
      projectiveDualAction v (projectiveDualAction u ell) := by
  ext alpha
  rfl

/-- The primitive ghost functional belongs to the invariant dual algebraic
annihilator. -/
theorem primitiveGhostFunctional_annihilatesAlgebraicHodge
    {G : GeometricCycleClassSpine V H}
    {D : LefschetzPrimitiveDecomposition G}
    {T : ProjectiveDegreeTraceSemantics V H}
    {A : TraceAnchor G T p}
    (E : TraceZeroPrimitiveTomographyGhost A D) :
    AnnihilatesAlgebraicHodge (primitiveGhostFunctional E) := by
  intro alpha halpha
  exact primitiveGhostFunctional_kills_atomic E alpha
    ((mem_AlgebraicHodgeSubspace_iff alpha).mp halpha)

/-- The primitive ghost functional is nonzero. -/
theorem primitiveGhostFunctional_ne_zero
    {G : GeometricCycleClassSpine V H}
    {D : LefschetzPrimitiveDecomposition G}
    {T : ProjectiveDegreeTraceSemantics V H}
    {A : TraceAnchor G T p}
    (E : TraceZeroPrimitiveTomographyGhost A D) :
    primitiveGhostFunctional E ≠ 0 := by
  intro hzero
  have hfun : primitiveGhostFunctional E E.traceZeroClass = 0 := by
    rw [hzero]
    rfl
  exact (primitiveGhostFunctional_detects E) hfun

/-- The projective ghost moment is exactly the primal/dual matrix coefficient. -/
theorem projectiveGhostMoment_eq_dual_pairing
    {R : HodgeFunctorialGeometricSemantics V H}
    {T : ProjectiveDegreeTraceSemantics V H}
    {D : LefschetzPrimitiveDecomposition R.spine}
    {A : TraceAnchor R.spine T p}
    (E : TraceZeroPrimitiveTomographyGhost A D)
    (w : HodgeFunctorialGeometricSemantics.ProjectiveHodgeWord R p) :
    projectiveGhostMoment E w =
      projectiveDualAction w (primitiveGhostFunctional E) E.traceZeroClass := by
  rfl

/-- Every dual transform of the ghost functional remains algebraically
annihilating. -/
theorem primitiveGhost_dualOrbit_annihilatesAlgebraicHodge
    {R : HodgeFunctorialGeometricSemantics V H}
    {T : ProjectiveDegreeTraceSemantics V H}
    {D : LefschetzPrimitiveDecomposition R.spine}
    {A : TraceAnchor R.spine T p}
    (E : TraceZeroPrimitiveTomographyGhost A D)
    (w : HodgeFunctorialGeometricSemantics.ProjectiveHodgeWord R p) :
    AnnihilatesAlgebraicHodge
      (projectiveDualAction w (primitiveGhostFunctional E)) :=
  projectiveDualAction_preserves_annihilator w (primitiveGhostFunctional E)
    (primitiveGhostFunctional_annihilatesAlgebraicHodge E)

/-- Complete primal/dual residual packet for one primitive projective failure. -/
structure PrimitiveProjectiveDualPacket
    (R : HodgeFunctorialGeometricSemantics V H)
    (T : ProjectiveDegreeTraceSemantics V H)
    (D : LefschetzPrimitiveDecomposition R.spine)
    (A : TraceAnchor R.spine T p) where
  ghost : TraceZeroPrimitiveTomographyGhost A D
  dual : ClassicalHodgeFiber V H p →ₗ[ℚ] ℚ
  dual_eq : dual = primitiveGhostFunctional ghost
  dual_nonzero : dual ≠ 0
  dual_annihilates_algebraic : AnnihilatesAlgebraicHodge dual
  primalModuleNonzero :
    HodgeFunctorialGeometricSemantics.ProjectiveHodgeWord.defectOrbitModule
      (R := R) ghost.defectState ≠ ⊥
  identity_pairing_nonzero :
    projectiveGhostMoment ghost
      (HodgeFunctorialGeometricSemantics.ProjectiveHodgeWord.id) ≠ 0

/-- Every primitive projective failure packet upgrades canonically to the
paired primal/dual representation packet. -/
noncomputable def PrimitiveProjectiveFailurePacket.toDualPacket
    {R : HodgeFunctorialGeometricSemantics V H}
    {T : ProjectiveDegreeTraceSemantics V H}
    {D : LefschetzPrimitiveDecomposition R.spine}
    {A : TraceAnchor R.spine T p}
    (P : PrimitiveProjectiveFailurePacket R T D A) :
    PrimitiveProjectiveDualPacket R T D A := by
  refine {
    ghost := P.ghost
    dual := primitiveGhostFunctional P.ghost
    dual_eq := rfl
    dual_nonzero := primitiveGhostFunctional_ne_zero P.ghost
    dual_annihilates_algebraic :=
      primitiveGhostFunctional_annihilatesAlgebraicHodge P.ghost
    primalModuleNonzero := P.projectiveModuleNonzero
    identity_pairing_nonzero := projectiveGhostMoment_id_ne_zero P.ghost
  }

/-- First positive-weight Hodge failure produces a nonzero paired primal/dual
projective representation object. -/
noncomputable def dualPacketOfNextWeightFailure
    {p : Nat}
    (R : HodgeFunctorialGeometricSemantics V H)
    (T : ProjectiveDegreeTraceSemantics V H)
    (D : LefschetzPrimitiveDecomposition R.spine)
    (A : TraceAnchor R.spine T (p + 1))
    (hsource : atomicDefectLinearMap V H p = 0)
    (htarget : atomicDefectLinearMap V H (p + 1) ≠ 0) :
    PrimitiveProjectiveDualPacket R T D A :=
  (packetOfNextWeightFailure R T D A hsource htarget).toDualPacket

#check AnnihilatesAlgebraicHodge
#check projectiveDualAction
#check projectiveDualAction_preserves_annihilator
#check projectiveDualAction_comp
#check primitiveGhostFunctional_annihilatesAlgebraicHodge
#check primitiveGhostFunctional_ne_zero
#check projectiveGhostMoment_eq_dual_pairing
#check PrimitiveProjectiveDualPacket
#check PrimitiveProjectiveFailurePacket.toDualPacket
#check dualPacketOfNextWeightFailure

#print axioms projectiveDualAction_preserves_annihilator
#print axioms primitiveGhostFunctional_ne_zero
#print axioms projectiveGhostMoment_eq_dual_pairing
#print axioms PrimitiveProjectiveFailurePacket.toDualPacket
#print axioms dualPacketOfNextWeightFailure

end GSTClassicalHodgePrimitiveProjectiveDualOrbit
