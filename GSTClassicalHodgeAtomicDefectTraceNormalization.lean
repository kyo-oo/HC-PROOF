import GSTClassicalHodgeProjectiveDegreeTrace
import GSTClassicalHodgeAtomicDefectDuality
import GSTClassicalHodgePrimitiveDefectTomographyGhost

/-!
# GST CLASSICAL HODGE — ATOMIC DEFECT TRACE NORMALIZATION

The fibered multiplicity obstruction cannot be solved by forgetting labels or
by attaching arbitrary labels to native point cycles.  This file changes the
scalar glue to a genuinely geometric invariant already present in the repo:
the projective-degree Betti trace.

Fix one actual algebraic cycle whose Betti trace is nonzero.  Its normalized
cycle class has trace one and zero atomic defect.  Therefore every rational
Hodge class alpha admits the canonical replacement

  alpha^0 = alpha - trace(alpha) * anchor,

with three exact properties:

* alpha^0 is still a genuine Hodge class;
* trace(alpha^0) = 0;
* alpha^0 has exactly the same atomic defect as alpha.

Thus, whenever one nonzero-trace algebraic anchor exists, the entire Hodge
atomic-defect problem is equivalent to its restriction to the trace-zero Hodge
sector.  A projective codimension-p point supplies such an anchor immediately,
because its degree is strictly positive.

This is noncircular: only a known algebraic class is subtracted.  No cycle is
constructed for the unknown Hodge class and no multiplicity sheet is declared
algebraic.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeAtomicDefectTraceNormalization

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeAtomicDefectDuality
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeProjectiveDegreeTrace

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- A genuine algebraic cycle with nonzero projective Betti trace. -/
structure TraceAnchor
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat) where
  cycle : codimensionCycles V.X p
  trace_ne_zero : D.trace p (H.cycleClass p cycle) ≠ 0

namespace TraceAnchor

/-- Raw Hodge class of the algebraic anchor. -/
noncomputable def hodgeClass
    {G : GeometricCycleClassSpine V H}
    {D : ProjectiveDegreeTraceSemantics V H}
    (A : TraceAnchor G D p) : ClassicalHodgeFiber V H p :=
  ⟨H.cycleClass p A.cycle, G.algebraic_is_hodge p A.cycle⟩

/-- Normalize the anchor to projective trace one. -/
noncomputable def normalizedHodgeClass
    {G : GeometricCycleClassSpine V H}
    {D : ProjectiveDegreeTraceSemantics V H}
    (A : TraceAnchor G D p) : ClassicalHodgeFiber V H p :=
  (D.trace p (H.cycleClass p A.cycle))⁻¹ • A.hodgeClass

/-- The normalized algebraic anchor has trace exactly one. -/
theorem trace_normalizedHodgeClass
    {G : GeometricCycleClassSpine V H}
    {D : ProjectiveDegreeTraceSemantics V H}
    (A : TraceAnchor G D p) :
    D.trace p (A.normalizedHodgeClass.1) = 1 := by
  simp [normalizedHodgeClass, hodgeClass, A.trace_ne_zero]

/-- Every algebraic anchor, normalized or not, has zero atomic defect. -/
theorem atomicDefect_hodgeClass_zero
    {G : GeometricCycleClassSpine V H}
    {D : ProjectiveDegreeTraceSemantics V H}
    (A : TraceAnchor G D p) :
    atomicDefectLinearMap V H p A.hodgeClass = 0 := by
  apply (Submodule.Quotient.mk_eq_zero
    (pointCycleClassSpan p (H.cycleClass p))).2
  rw [← smoothProjective_cycleClass_range_eq_atomic_span V H p]
  exact ⟨A.cycle, rfl⟩

/-- The trace-one normalization also vanishes in the atomic quotient. -/
theorem atomicDefect_normalizedHodgeClass_zero
    {G : GeometricCycleClassSpine V H}
    {D : ProjectiveDegreeTraceSemantics V H}
    (A : TraceAnchor G D p) :
    atomicDefectLinearMap V H p A.normalizedHodgeClass = 0 := by
  rw [normalizedHodgeClass, map_smul, A.atomicDefect_hodgeClass_zero]
  exact smul_zero _

/-- Subtract the geometric trace component of an arbitrary Hodge class. -/
noncomputable def traceZeroRepresentative
    {G : GeometricCycleClassSpine V H}
    {D : ProjectiveDegreeTraceSemantics V H}
    (A : TraceAnchor G D p)
    (alpha : ClassicalHodgeFiber V H p) :
    ClassicalHodgeFiber V H p :=
  alpha - (D.trace p alpha.1) • A.normalizedHodgeClass

/-- The representative is exactly trace zero. -/
theorem trace_traceZeroRepresentative
    {G : GeometricCycleClassSpine V H}
    {D : ProjectiveDegreeTraceSemantics V H}
    (A : TraceAnchor G D p)
    (alpha : ClassicalHodgeFiber V H p) :
    D.trace p (A.traceZeroRepresentative alpha).1 = 0 := by
  simp [traceZeroRepresentative, A.trace_normalizedHodgeClass]

/-- **DEFECT IS UNCHANGED BY TRACE NORMALIZATION.** -/
theorem atomicDefect_traceZeroRepresentative
    {G : GeometricCycleClassSpine V H}
    {D : ProjectiveDegreeTraceSemantics V H}
    (A : TraceAnchor G D p)
    (alpha : ClassicalHodgeFiber V H p) :
    atomicDefectLinearMap V H p (A.traceZeroRepresentative alpha) =
      atomicDefectLinearMap V H p alpha := by
  rw [traceZeroRepresentative, map_sub, map_smul,
    A.atomicDefect_normalizedHodgeClass_zero]
  simp

/-- Nonzero defect survives trace normalization. -/
theorem traceZeroRepresentative_defect_ne_zero
    {G : GeometricCycleClassSpine V H}
    {D : ProjectiveDegreeTraceSemantics V H}
    (A : TraceAnchor G D p)
    (alpha : ClassicalHodgeFiber V H p)
    (hdef : atomicDefectLinearMap V H p alpha ≠ 0) :
    atomicDefectLinearMap V H p (A.traceZeroRepresentative alpha) ≠ 0 := by
  rw [A.atomicDefect_traceZeroRepresentative alpha]
  exact hdef

end TraceAnchor

/-- Restriction of the projective trace to the genuine rational Hodge fiber. -/
noncomputable def hodgeTrace
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat) : ClassicalHodgeFiber V H p →ₗ[ℚ] ℚ :=
  (D.trace p).comp (rationalHodgeSubspace (H.hodgeBigrading p)).subtype

/-- Trace-zero Hodge sector. -/
abbrev TraceZeroHodgeFiber
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat) := LinearMap.ker (hodgeTrace D p)

/-- Atomic defect restricted to the trace-zero Hodge sector. -/
noncomputable def traceZeroAtomicDefectMap
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat) :
    TraceZeroHodgeFiber D p →ₗ[ℚ] AtomicDefectSpace V H p :=
  (atomicDefectLinearMap V H p).comp (TraceZeroHodgeFiber D p).subtype

/-- Every normalized representative belongs to the trace-zero Hodge sector. -/
noncomputable def TraceAnchor.traceZeroRepresentativeSubtype
    {G : GeometricCycleClassSpine V H}
    {D : ProjectiveDegreeTraceSemantics V H}
    (A : TraceAnchor G D p)
    (alpha : ClassicalHodgeFiber V H p) : TraceZeroHodgeFiber D p :=
  ⟨A.traceZeroRepresentative alpha, by
    change D.trace p (A.traceZeroRepresentative alpha).1 = 0
    exact A.trace_traceZeroRepresentative alpha⟩

/-- Every full atomic defect has a trace-zero Hodge representative with exactly
the same quotient class. -/
theorem TraceAnchor.exists_traceZero_same_defect
    {G : GeometricCycleClassSpine V H}
    {D : ProjectiveDegreeTraceSemantics V H}
    (A : TraceAnchor G D p)
    (alpha : ClassicalHodgeFiber V H p) :
    ∃ beta : TraceZeroHodgeFiber D p,
      traceZeroAtomicDefectMap D p beta =
        atomicDefectLinearMap V H p alpha := by
  refine ⟨A.traceZeroRepresentativeSubtype alpha, ?_⟩
  exact A.atomicDefect_traceZeroRepresentative alpha

/-- **TRACE-ZERO REDUCTION.**  Once one nonzero-trace algebraic anchor exists,
vanishing of the full Hodge defect is equivalent to vanishing on the
trace-zero Hodge sector. -/
theorem TraceAnchor.atomicDefect_zero_iff_traceZeroDefect_zero
    {G : GeometricCycleClassSpine V H}
    {D : ProjectiveDegreeTraceSemantics V H}
    (A : TraceAnchor G D p) :
    atomicDefectLinearMap V H p = 0 ↔
      traceZeroAtomicDefectMap D p = 0 := by
  constructor
  · intro hfull
    rw [traceZeroAtomicDefectMap, hfull]
    exact LinearMap.zero_comp
  · intro hzero
    apply LinearMap.ext
    intro alpha
    rcases A.exists_traceZero_same_defect alpha with ⟨beta, hbeta⟩
    rw [← hbeta, hzero]
    rfl

/-- Every genuine codimension-p projective point supplies a trace anchor,
because projective degree is strictly positive. -/
noncomputable def TraceAnchor.ofPoint
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (x : CodimensionPoint V.X p) : TraceAnchor G D p where
  cycle := codimensionPointCycle V.X p x
  trace_ne_zero := by
    rw [D.trace_point_cycleClass]
    exact ne_of_gt (D.pointDegree_pos p x)

/-- Point-anchored specialization of the trace-zero reduction. -/
theorem atomicDefect_zero_iff_traceZeroDefect_zero_of_point
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (x : CodimensionPoint V.X p) :
    atomicDefectLinearMap V H p = 0 ↔
      traceZeroAtomicDefectMap D p = 0 :=
  (TraceAnchor.ofPoint G D x).atomicDefect_zero_iff_traceZeroDefect_zero

#check TraceAnchor
#check TraceAnchor.hodgeClass
#check TraceAnchor.normalizedHodgeClass
#check TraceAnchor.trace_normalizedHodgeClass
#check TraceAnchor.traceZeroRepresentative
#check TraceAnchor.atomicDefect_traceZeroRepresentative
#check hodgeTrace
#check TraceZeroHodgeFiber
#check traceZeroAtomicDefectMap
#check TraceAnchor.exists_traceZero_same_defect
#check TraceAnchor.atomicDefect_zero_iff_traceZeroDefect_zero
#check TraceAnchor.ofPoint
#check atomicDefect_zero_iff_traceZeroDefect_zero_of_point

#print axioms TraceAnchor.trace_normalizedHodgeClass
#print axioms TraceAnchor.atomicDefect_traceZeroRepresentative
#print axioms TraceAnchor.exists_traceZero_same_defect
#print axioms TraceAnchor.atomicDefect_zero_iff_traceZeroDefect_zero
#print axioms atomicDefect_zero_iff_traceZeroDefect_zero_of_point

end GSTClassicalHodgeAtomicDefectTraceNormalization
