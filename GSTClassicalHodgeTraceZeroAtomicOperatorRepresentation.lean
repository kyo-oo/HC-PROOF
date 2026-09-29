import GSTClassicalHodgeTraceZeroDefectProjector
import GSTClassicalHodgeAtomicDefectEquivariantIrreducibility

/-!
# GST CLASSICAL HODGE — TRACE-ZERO ATOMIC OPERATOR REPRESENTATION

The trace-zero projector induces the identity on atomic defect.  Therefore any
atomic-natural Hodge operator can be followed by trace normalization without
changing its quotient dynamics.

This file constructs the resulting operator directly on the trace-zero Hodge
sector.  For an atomic-natural operator T define

  T^0 = Pi o T |_(ker trace),

where Pi is the projective-degree trace-zero projector associated to one known
algebraic trace anchor.

Although repeated trace normalization can change Hodge representatives by
algebraic correction terms, those corrections vanish in atomic defect.  Thus
atomic defect remains exactly equivariant for the trace-zero dynamics.

This is the correct carrier for the primitive residual: all projective trace
directions are removed, but every genuine atomic-natural operator keeps its
full action on the obstruction quotient.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeTraceZeroAtomicOperatorRepresentation

open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicDefectDuality
open GSTClassicalHodgeAtomicDefectEquivariantIrreducibility
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeProjectiveDegreeTrace
open GSTClassicalHodgeAtomicDefectTraceNormalization
open GSTClassicalHodgeTraceZeroDefectProjector

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Restrict an atomic-natural Hodge operator to the trace-zero sector and
normalize its output back into that sector. -/
noncomputable def traceZeroOperator
    {G : GeometricCycleClassSpine V H}
    {D : ProjectiveDegreeTraceSemantics V H}
    (A : TraceAnchor G D p)
    (T : AtomicNaturalHodgeOperator V H p) :
    Module.End ℚ (TraceZeroHodgeFiber D p) :=
  (traceZeroRetraction A).comp
    (T.hodge.comp (TraceZeroHodgeFiber D p).subtype)

/-- The underlying Hodge vector of the normalized action is exactly the
trace-zero projection of the original Hodge action. -/
theorem traceZeroOperator_coe
    {G : GeometricCycleClassSpine V H}
    {D : ProjectiveDegreeTraceSemantics V H}
    (A : TraceAnchor G D p)
    (T : AtomicNaturalHodgeOperator V H p)
    (alpha : TraceZeroHodgeFiber D p) :
    (traceZeroOperator A T alpha).1 =
      (traceZeroProjector A (T.hodge alpha.1)).1 := by
  rfl

/-- Atomic defect restricted to the trace-zero Hodge sector. -/
noncomputable def traceZeroDefectMap
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat) :
    TraceZeroHodgeFiber D p →ₗ[ℚ] AtomicDefectSpace V H p :=
  traceZeroAtomicDefectMap D p

/-- **TRACE-ZERO DEFECT EQUIVARIANCE.**
The normalized trace-zero operator acts on atomic defect exactly by the same
descended quotient operator as the original ambient geometry. -/
theorem traceZero_defect_equivariant
    {G : GeometricCycleClassSpine V H}
    {D : ProjectiveDegreeTraceSemantics V H}
    (A : TraceAnchor G D p)
    (T : AtomicNaturalHodgeOperator V H p)
    (alpha : TraceZeroHodgeFiber D p) :
    traceZeroDefectMap D p (traceZeroOperator A T alpha) =
      T.defectOperator (traceZeroDefectMap D p alpha) := by
  change
    atomicDefectLinearMap V H p
        (traceZeroProjector A (T.hodge alpha.1)) =
      T.defectOperator (atomicDefectLinearMap V H p alpha.1)
  rw [atomicDefect_traceZeroProjector_apply A]
  exact T.defect_equivariant alpha.1

/-- The normalized identity has identity action on atomic defect. -/
theorem traceZero_id_defect
    {G : GeometricCycleClassSpine V H}
    {D : ProjectiveDegreeTraceSemantics V H}
    (A : TraceAnchor G D p)
    (alpha : TraceZeroHodgeFiber D p) :
    traceZeroDefectMap D p
        (traceZeroOperator A
          (AtomicNaturalHodgeOperator.id (V := V) (H := H) (p := p)) alpha) =
      traceZeroDefectMap D p alpha := by
  rw [traceZero_defect_equivariant]
  exact LinearMap.congr_fun
    (atomicDefectOperator_id
      (V := V) (H := H) (p := p)
      (AtomicNaturalHodgeOperator.id (V := V) (H := H) (p := p)).atomicStable)
    _

/-- Composition of normalized trace-zero actions agrees with composition of the
original geometry on atomic defect, even though the Hodge representatives may
differ by algebraic correction terms between the two steps. -/
theorem traceZero_comp_defect
    {G : GeometricCycleClassSpine V H}
    {D : ProjectiveDegreeTraceSemantics V H}
    (A : TraceAnchor G D p)
    (T U : AtomicNaturalHodgeOperator V H p)
    (alpha : TraceZeroHodgeFiber D p) :
    traceZeroDefectMap D p
        (traceZeroOperator A T (traceZeroOperator A U alpha)) =
      (T.comp U).defectOperator (traceZeroDefectMap D p alpha) := by
  rw [traceZero_defect_equivariant A T]
  rw [traceZero_defect_equivariant A U]
  unfold AtomicNaturalHodgeOperator.defectOperator
  rw [← atomicDefectOperator_comp
    (V := V) (H := H) (p := p)
    T.ambient U.ambient T.atomicStable U.atomicStable (T.comp U).atomicStable]
  rfl

/-- Rational scaling is also represented correctly on atomic defect after
trace normalization. -/
theorem traceZero_smul_defect
    {G : GeometricCycleClassSpine V H}
    {D : ProjectiveDegreeTraceSemantics V H}
    (A : TraceAnchor G D p)
    (c : ℚ)
    (T : AtomicNaturalHodgeOperator V H p)
    (alpha : TraceZeroHodgeFiber D p) :
    traceZeroDefectMap D p
        (traceZeroOperator A (T.smul c) alpha) =
      (T.smul c).defectOperator (traceZeroDefectMap D p alpha) :=
  traceZero_defect_equivariant A (T.smul c) alpha

/-- Sums are represented correctly on atomic defect after trace normalization. -/
theorem traceZero_add_defect
    {G : GeometricCycleClassSpine V H}
    {D : ProjectiveDegreeTraceSemantics V H}
    (A : TraceAnchor G D p)
    (T U : AtomicNaturalHodgeOperator V H p)
    (alpha : TraceZeroHodgeFiber D p) :
    traceZeroDefectMap D p
        (traceZeroOperator A (T.add U) alpha) =
      (T.add U).defectOperator (traceZeroDefectMap D p alpha) :=
  traceZero_defect_equivariant A (T.add U) alpha

/-- If the quotient action of T is injective, a nonzero trace-zero defect
cannot be erased by applying T and renormalizing. -/
theorem traceZero_defect_ne_zero_of_injective
    {G : GeometricCycleClassSpine V H}
    {D : ProjectiveDegreeTraceSemantics V H}
    (A : TraceAnchor G D p)
    (T : AtomicNaturalHodgeOperator V H p)
    (hinj : Function.Injective T.defectOperator)
    (alpha : TraceZeroHodgeFiber D p)
    (hdef : traceZeroDefectMap D p alpha ≠ 0) :
    traceZeroDefectMap D p (traceZeroOperator A T alpha) ≠ 0 := by
  rw [traceZero_defect_equivariant]
  intro hz
  apply hdef
  apply hinj
  simpa using hz

#check traceZeroOperator
#check traceZero_defect_equivariant
#check traceZero_id_defect
#check traceZero_comp_defect
#check traceZero_smul_defect
#check traceZero_add_defect
#check traceZero_defect_ne_zero_of_injective

#print axioms traceZero_defect_equivariant
#print axioms traceZero_comp_defect
#print axioms traceZero_defect_ne_zero_of_injective

end GSTClassicalHodgeTraceZeroAtomicOperatorRepresentation
