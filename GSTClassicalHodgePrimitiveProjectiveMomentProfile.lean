import GSTClassicalHodgePrimitiveProjectiveFailureCrown

/-!
# GST CLASSICAL HODGE — PRIMITIVE PROJECTIVE MOMENT PROFILE

A first primitive Hodge failure has already been converted into a nonzero
atomic-defect module for the genuine projective word algebra.  This file adds
its dual observable without externalizing any GST matrix unit.

For a trace-zero primitive tomography ghost `E`, its atomic separator restricts
to a rational functional on the genuine Hodge fiber.  It kills every Hodge
class whose underlying cohomology class lies in the atomic cycle-class span,
but it is nonzero on `E.traceZeroClass`.

Evaluating this functional after any actual projective/Hodge word gives a
scalar matrix coefficient

  m_E(w) = ell_E (w · E.traceZeroClass).

The coefficient factors through the atomic-defect dynamics in the only sense
needed here: if the descended defect state is zero, then the coefficient is
zero.  Hence any nonzero coefficient certifies a nonzero state in the genuine
projective defect orbit.

This is deliberately weaker than projective irreducibility or a prescribed
basis action.  It produces a concrete nonzero scalar observable of the actual
geometric representation, suitable for the next GST/worldtrace collision.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgePrimitiveProjectiveMomentProfile

open GSTGeometricRealizationStage2G
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeAtomicDefectDuality
open GSTClassicalHodgeAtomicAnnihilator
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeProjectiveDegreeTrace
open GSTClassicalHodgePrimitiveAtomicDefectReduction
open GSTClassicalHodgeTraceZeroPrimitiveTomographyGhost
open GSTClassicalHodgePrimitiveProjectiveDefectModule
open GSTClassicalHodgeHodgeFunctorialProjectiveDynamics
open GSTClassicalHodgePrimitiveProjectiveFailureCrown

variable {V : GSTProjectiveOverC.SmoothProjectiveComplexScheme}
variable {H : GSTGeometricRealizationStage2G.HodgeBigradedBettiData V}
variable {p : Nat}

/-- The primitive separator restricted to the rational `(p,p)` Hodge fiber. -/
noncomputable def primitiveGhostFunctional
    {G : GeometricCycleClassSpine V H}
    {D : LefschetzPrimitiveDecomposition G}
    {T : ProjectiveDegreeTraceSemantics V H}
    {A : TraceAnchor G T p}
    (E : TraceZeroPrimitiveTomographyGhost A D) :
    ClassicalHodgeFiber V H p →ₗ[ℚ] ℚ :=
  E.source.detector.comp
    (rationalHodgeSubspace (H.hodgeBigrading p)).subtype

/-- The ghost functional vanishes on every Hodge class already lying in the
atomic cycle-class span. -/
theorem primitiveGhostFunctional_kills_atomic
    {G : GeometricCycleClassSpine V H}
    {D : LefschetzPrimitiveDecomposition G}
    {T : ProjectiveDegreeTraceSemantics V H}
    {A : TraceAnchor G T p}
    (E : TraceZeroPrimitiveTomographyGhost A D)
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha.1 ∈ pointCycleClassSpan p (H.cycleClass p)) :
    primitiveGhostFunctional E alpha = 0 := by
  have hker :
      pointCycleClassSpan p (H.cycleClass p) ≤
        LinearMap.ker E.source.detector :=
    (annihilatesPointCycles_iff_atomicSpan_le_ker
      p (H.cycleClass p) E.source.detector).mp
      E.source.annihilates_atoms
  exact hker halpha

/-- The functional is genuinely nonzero on the normalized primitive failure
state. -/
theorem primitiveGhostFunctional_detects
    {G : GeometricCycleClassSpine V H}
    {D : LefschetzPrimitiveDecomposition G}
    {T : ProjectiveDegreeTraceSemantics V H}
    {A : TraceAnchor G T p}
    (E : TraceZeroPrimitiveTomographyGhost A D) :
    primitiveGhostFunctional E E.traceZeroClass ≠ 0 := by
  simpa [primitiveGhostFunctional] using E.separator_detects

/-- Scalar projective matrix coefficient of a primitive failure. -/
noncomputable def projectiveGhostMoment
    {R : HodgeFunctorialGeometricSemantics V H}
    {T : ProjectiveDegreeTraceSemantics V H}
    {D : LefschetzPrimitiveDecomposition R.spine}
    {A : TraceAnchor R.spine T p}
    (E : TraceZeroPrimitiveTomographyGhost A D)
    (w : HodgeFunctorialGeometricSemantics.ProjectiveHodgeWord R p) : ℚ :=
  primitiveGhostFunctional E
    ((HodgeFunctorialGeometricSemantics.ProjectiveHodgeWord.eval w).hodge
      E.traceZeroClass)

/-- The identity projective word already has a nonzero matrix coefficient. -/
theorem projectiveGhostMoment_id_ne_zero
    {R : HodgeFunctorialGeometricSemantics V H}
    {T : ProjectiveDegreeTraceSemantics V H}
    {D : LefschetzPrimitiveDecomposition R.spine}
    {A : TraceAnchor R.spine T p}
    (E : TraceZeroPrimitiveTomographyGhost A D) :
    projectiveGhostMoment E
      (HodgeFunctorialGeometricSemantics.ProjectiveHodgeWord.id) ≠ 0 := by
  simpa [projectiveGhostMoment,
    HodgeFunctorialGeometricSemantics.ProjectiveHodgeWord.eval,
    GSTClassicalHodgeAtomicDefectEquivariantIrreducibility.AtomicNaturalHodgeOperator.id]
    using primitiveGhostFunctional_detects E

/-- Additivity of the genuine projective moment profile. -/
theorem projectiveGhostMoment_add
    {R : HodgeFunctorialGeometricSemantics V H}
    {T : ProjectiveDegreeTraceSemantics V H}
    {D : LefschetzPrimitiveDecomposition R.spine}
    {A : TraceAnchor R.spine T p}
    (E : TraceZeroPrimitiveTomographyGhost A D)
    (u v : HodgeFunctorialGeometricSemantics.ProjectiveHodgeWord R p) :
    projectiveGhostMoment E
        (HodgeFunctorialGeometricSemantics.ProjectiveHodgeWord.add u v) =
      projectiveGhostMoment E u + projectiveGhostMoment E v := by
  simp [projectiveGhostMoment,
    HodgeFunctorialGeometricSemantics.ProjectiveHodgeWord.eval,
    GSTClassicalHodgeAtomicDefectEquivariantIrreducibility.AtomicNaturalHodgeOperator.add]

/-- Rational homogeneity of the genuine projective moment profile. -/
theorem projectiveGhostMoment_smul
    {R : HodgeFunctorialGeometricSemantics V H}
    {T : ProjectiveDegreeTraceSemantics V H}
    {D : LefschetzPrimitiveDecomposition R.spine}
    {A : TraceAnchor R.spine T p}
    (E : TraceZeroPrimitiveTomographyGhost A D)
    (q : ℚ)
    (u : HodgeFunctorialGeometricSemantics.ProjectiveHodgeWord R p) :
    projectiveGhostMoment E
        (HodgeFunctorialGeometricSemantics.ProjectiveHodgeWord.smul q u) =
      q * projectiveGhostMoment E u := by
  simp [projectiveGhostMoment,
    HodgeFunctorialGeometricSemantics.ProjectiveHodgeWord.eval,
    GSTClassicalHodgeAtomicDefectEquivariantIrreducibility.AtomicNaturalHodgeOperator.smul]

/-- A vanishing descended defect state forces the corresponding projective
matrix coefficient to vanish.  Thus the scalar observable really sees only
nontrivial quotient dynamics, not an algebraic representative artifact. -/
theorem projectiveGhostMoment_eq_zero_of_defect_eq_zero
    {R : HodgeFunctorialGeometricSemantics V H}
    {T : ProjectiveDegreeTraceSemantics V H}
    {D : LefschetzPrimitiveDecomposition R.spine}
    {A : TraceAnchor R.spine T p}
    (E : TraceZeroPrimitiveTomographyGhost A D)
    (w : HodgeFunctorialGeometricSemantics.ProjectiveHodgeWord R p)
    (hzero : w.defectOperator E.defectState = 0) :
    projectiveGhostMoment E w = 0 := by
  let beta : ClassicalHodgeFiber V H p :=
    (HodgeFunctorialGeometricSemantics.ProjectiveHodgeWord.eval w).hodge
      E.traceZeroClass
  have heq :=
    HodgeFunctorialGeometricSemantics.ProjectiveHodgeWord.defect_equivariant
      w E.traceZeroClass
  rw [hzero] at heq
  have hmem : beta.1 ∈ pointCycleClassSpan p (H.cycleClass p) := by
    change Submodule.Quotient.mk beta.1 = 0 at heq
    exact (Submodule.Quotient.mk_eq_zero
      (pointCycleClassSpan p (H.cycleClass p))).mp heq
  exact primitiveGhostFunctional_kills_atomic E beta hmem

/-- Therefore every nonzero projective ghost moment certifies a nonzero state
in the genuine projective defect representation. -/
theorem defect_ne_zero_of_projectiveGhostMoment_ne_zero
    {R : HodgeFunctorialGeometricSemantics V H}
    {T : ProjectiveDegreeTraceSemantics V H}
    {D : LefschetzPrimitiveDecomposition R.spine}
    {A : TraceAnchor R.spine T p}
    (E : TraceZeroPrimitiveTomographyGhost A D)
    (w : HodgeFunctorialGeometricSemantics.ProjectiveHodgeWord R p)
    (hmoment : projectiveGhostMoment E w ≠ 0) :
    w.defectOperator E.defectState ≠ 0 := by
  intro hzero
  exact hmoment (projectiveGhostMoment_eq_zero_of_defect_eq_zero E w hzero)

/-- **FIRST-FAILURE PROJECTIVE MATRIX COEFFICIENT.**
Every first positive-weight atomic defect supplies a trace-zero primitive ghost
and a genuine projective word with simultaneously nonzero scalar moment and
nonzero descended defect state.  The witness word may already be the identity;
subsequent worldtrace arguments can now act on this concrete observable rather
than on an assumed matrix-unit realization. -/
theorem nextWeightFailure_yields_nonzero_projectiveMoment
    {p : Nat}
    (R : HodgeFunctorialGeometricSemantics V H)
    (T : ProjectiveDegreeTraceSemantics V H)
    (D : LefschetzPrimitiveDecomposition R.spine)
    (A : TraceAnchor R.spine T (p + 1))
    (hsource : atomicDefectLinearMap V H p = 0)
    (htarget : atomicDefectLinearMap V H (p + 1) ≠ 0) :
    ∃ E : TraceZeroPrimitiveTomographyGhost A D,
    ∃ w : HodgeFunctorialGeometricSemantics.ProjectiveHodgeWord R (p + 1),
      projectiveGhostMoment E w ≠ 0 ∧
      w.defectOperator E.defectState ≠ 0 := by
  let P := packetOfNextWeightFailure R T D A hsource htarget
  let w : HodgeFunctorialGeometricSemantics.ProjectiveHodgeWord R (p + 1) :=
    HodgeFunctorialGeometricSemantics.ProjectiveHodgeWord.id
  have hm : projectiveGhostMoment P.ghost w ≠ 0 := by
    simpa [w] using projectiveGhostMoment_id_ne_zero P.ghost
  exact ⟨P.ghost, w, hm,
    defect_ne_zero_of_projectiveGhostMoment_ne_zero P.ghost w hm⟩

#check primitiveGhostFunctional
#check primitiveGhostFunctional_kills_atomic
#check primitiveGhostFunctional_detects
#check projectiveGhostMoment
#check projectiveGhostMoment_id_ne_zero
#check projectiveGhostMoment_add
#check projectiveGhostMoment_smul
#check projectiveGhostMoment_eq_zero_of_defect_eq_zero
#check defect_ne_zero_of_projectiveGhostMoment_ne_zero
#check nextWeightFailure_yields_nonzero_projectiveMoment

#print axioms primitiveGhostFunctional_kills_atomic
#print axioms primitiveGhostFunctional_detects
#print axioms projectiveGhostMoment_eq_zero_of_defect_eq_zero
#print axioms defect_ne_zero_of_projectiveGhostMoment_ne_zero
#print axioms nextWeightFailure_yields_nonzero_projectiveMoment

end GSTClassicalHodgePrimitiveProjectiveMomentProfile
