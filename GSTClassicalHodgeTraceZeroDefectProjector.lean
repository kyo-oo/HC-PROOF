import GSTClassicalHodgeAtomicDefectTraceNormalization
import GSTClassicalHodgeAtomicDefectOperatorDescent

/-!
# GST CLASSICAL HODGE — TRACE-ZERO DEFECT PROJECTOR

Projective-degree normalization is linear.  This file promotes the pointwise
normalization from the preceding module to a canonical rank-one correction
operator on the full rational Hodge fiber.

For one nonzero-trace algebraic anchor A define

  Pi(alpha) = alpha - trace(alpha) * A_norm.

Then:

* Pi is Q-linear;
* trace(Pi alpha) = 0;
* Pi fixes every trace-zero Hodge class;
* Pi is idempotent;
* alpha - Pi alpha is algebraic;
* the atomic defect map is unchanged by Pi.

Hence Pi induces the identity transformation on the Hodge atomic-defect
quotient.  In particular every defect dynamics may be normalized back into the
trace-zero sector after each step without changing its quotient action.

This removes the projective-degree direction from subsequent GST dynamics
without adding any Hodge-algebraicity assumption.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeTraceZeroDefectProjector

open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeAtomicDefectDuality
open GSTClassicalHodgeAtomicDefectOperatorDescent
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeProjectiveDegreeTrace
open GSTClassicalHodgeAtomicDefectTraceNormalization

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Linear trace-zero normalization projector. -/
noncomputable def traceZeroProjector
    {G : GeometricCycleClassSpine V H}
    {D : ProjectiveDegreeTraceSemantics V H}
    (A : TraceAnchor G D p) :
    ClassicalHodgeFiber V H p →ₗ[ℚ] ClassicalHodgeFiber V H p where
  toFun alpha := A.traceZeroRepresentative alpha
  map_add' := by
    intro alpha beta
    apply Subtype.ext
    simp [TraceAnchor.traceZeroRepresentative, add_smul]
  map_smul' := by
    intro c alpha
    apply Subtype.ext
    simp [TraceAnchor.traceZeroRepresentative, mul_smul]

@[simp]
theorem traceZeroProjector_apply
    {G : GeometricCycleClassSpine V H}
    {D : ProjectiveDegreeTraceSemantics V H}
    (A : TraceAnchor G D p)
    (alpha : ClassicalHodgeFiber V H p) :
    traceZeroProjector A alpha = A.traceZeroRepresentative alpha :=
  rfl

/-- The projector lands in the trace-zero hyperplane. -/
theorem trace_traceZeroProjector
    {G : GeometricCycleClassSpine V H}
    {D : ProjectiveDegreeTraceSemantics V H}
    (A : TraceAnchor G D p)
    (alpha : ClassicalHodgeFiber V H p) :
    D.trace p (traceZeroProjector A alpha).1 = 0 :=
  A.trace_traceZeroRepresentative alpha

/-- Trace-zero vectors are fixed exactly. -/
theorem traceZeroProjector_eq_self_of_trace_zero
    {G : GeometricCycleClassSpine V H}
    {D : ProjectiveDegreeTraceSemantics V H}
    (A : TraceAnchor G D p)
    (alpha : ClassicalHodgeFiber V H p)
    (htrace : D.trace p alpha.1 = 0) :
    traceZeroProjector A alpha = alpha := by
  apply Subtype.ext
  simp [traceZeroProjector, TraceAnchor.traceZeroRepresentative, htrace]

/-- The trace-zero projector is idempotent. -/
theorem traceZeroProjector_idempotent
    {G : GeometricCycleClassSpine V H}
    {D : ProjectiveDegreeTraceSemantics V H}
    (A : TraceAnchor G D p) :
    (traceZeroProjector A).comp (traceZeroProjector A) =
      traceZeroProjector A := by
  apply LinearMap.ext
  intro alpha
  exact traceZeroProjector_eq_self_of_trace_zero A _
    (trace_traceZeroProjector A alpha)

/-- The correction removed by the projector is a scalar multiple of one
known algebraic Hodge class. -/
theorem sub_traceZeroProjector_eq_algebraic_correction
    {G : GeometricCycleClassSpine V H}
    {D : ProjectiveDegreeTraceSemantics V H}
    (A : TraceAnchor G D p)
    (alpha : ClassicalHodgeFiber V H p) :
    alpha - traceZeroProjector A alpha =
      (D.trace p alpha.1) • A.normalizedHodgeClass := by
  apply Subtype.ext
  simp [traceZeroProjector, TraceAnchor.traceZeroRepresentative]

/-- **THE PROJECTOR IS THE IDENTITY ON ATOMIC DEFECT.** -/
theorem atomicDefect_traceZeroProjector
    {G : GeometricCycleClassSpine V H}
    {D : ProjectiveDegreeTraceSemantics V H}
    (A : TraceAnchor G D p) :
    (atomicDefectLinearMap V H p).comp (traceZeroProjector A) =
      atomicDefectLinearMap V H p := by
  apply LinearMap.ext
  intro alpha
  exact A.atomicDefect_traceZeroRepresentative alpha

/-- Pointwise form of defect invariance. -/
theorem atomicDefect_traceZeroProjector_apply
    {G : GeometricCycleClassSpine V H}
    {D : ProjectiveDegreeTraceSemantics V H}
    (A : TraceAnchor G D p)
    (alpha : ClassicalHodgeFiber V H p) :
    atomicDefectLinearMap V H p (traceZeroProjector A alpha) =
      atomicDefectLinearMap V H p alpha := by
  exact LinearMap.congr_fun (atomicDefect_traceZeroProjector A) alpha

/-- Normalize an arbitrary Hodge-fiber endomorphism after every step. -/
noncomputable def traceZeroNormalizeOperator
    {G : GeometricCycleClassSpine V H}
    {D : ProjectiveDegreeTraceSemantics V H}
    (A : TraceAnchor G D p)
    (T : Module.End ℚ (ClassicalHodgeFiber V H p)) :
    Module.End ℚ (ClassicalHodgeFiber V H p) :=
  (traceZeroProjector A).comp T

/-- The normalized operator always lands in the trace-zero sector. -/
theorem trace_traceZeroNormalizeOperator
    {G : GeometricCycleClassSpine V H}
    {D : ProjectiveDegreeTraceSemantics V H}
    (A : TraceAnchor G D p)
    (T : Module.End ℚ (ClassicalHodgeFiber V H p))
    (alpha : ClassicalHodgeFiber V H p) :
    D.trace p (traceZeroNormalizeOperator A T alpha).1 = 0 :=
  trace_traceZeroProjector A (T alpha)

/-- Normalizing the output of an operator does not change the resulting atomic
defect. -/
theorem atomicDefect_traceZeroNormalizeOperator
    {G : GeometricCycleClassSpine V H}
    {D : ProjectiveDegreeTraceSemantics V H}
    (A : TraceAnchor G D p)
    (T : Module.End ℚ (ClassicalHodgeFiber V H p))
    (alpha : ClassicalHodgeFiber V H p) :
    atomicDefectLinearMap V H p (traceZeroNormalizeOperator A T alpha) =
      atomicDefectLinearMap V H p (T alpha) := by
  exact atomicDefect_traceZeroProjector_apply A (T alpha)

/-- On the trace-zero sector the projector is a genuine retraction. -/
noncomputable def traceZeroRetraction
    {G : GeometricCycleClassSpine V H}
    {D : ProjectiveDegreeTraceSemantics V H}
    (A : TraceAnchor G D p) :
    ClassicalHodgeFiber V H p →ₗ[ℚ] TraceZeroHodgeFiber D p where
  toFun alpha := A.traceZeroRepresentativeSubtype alpha
  map_add' := by
    intro alpha beta
    apply Subtype.ext
    exact (traceZeroProjector A).map_add alpha beta
  map_smul' := by
    intro c alpha
    apply Subtype.ext
    exact (traceZeroProjector A).map_smul c alpha

/-- Retraction followed by inclusion is exactly the trace-zero projector. -/
theorem traceZeroSubtype_comp_retraction
    {G : GeometricCycleClassSpine V H}
    {D : ProjectiveDegreeTraceSemantics V H}
    (A : TraceAnchor G D p) :
    (TraceZeroHodgeFiber D p).subtype.comp (traceZeroRetraction A) =
      traceZeroProjector A := by
  rfl

#check traceZeroProjector
#check traceZeroProjector_idempotent
#check atomicDefect_traceZeroProjector
#check traceZeroNormalizeOperator
#check atomicDefect_traceZeroNormalizeOperator
#check traceZeroRetraction
#check traceZeroSubtype_comp_retraction

#print axioms traceZeroProjector_idempotent
#print axioms atomicDefect_traceZeroProjector
#print axioms atomicDefect_traceZeroNormalizeOperator
#print axioms traceZeroSubtype_comp_retraction

end GSTClassicalHodgeTraceZeroDefectProjector
