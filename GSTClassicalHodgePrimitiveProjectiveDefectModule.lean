import GSTClassicalHodgeHodgeFunctorialProjectiveDynamics
import GSTClassicalHodgeTraceZeroPrimitiveTomographyGhost

/-!
# GST CLASSICAL HODGE — PRIMITIVE PROJECTIVE DEFECT MODULE

After trace normalization, every actual projective self-map acts on the same
atomic-defect quotient that carries the primitive tomography ghost.  This file
packages the orbit of one defect under the genuine projective word algebra as
a rational submodule.

The construction is representation-theoretic and noncircular:

* the generators are actual scheme endomorphisms;
* cycle-class functoriality gives atomic stability;
* Hodge functoriality restricts the action to the Hodge fiber;
* trace normalization changes representatives only by algebraic classes;
* no projective word is required to act as a chosen matrix unit.

A nonzero primitive trace-zero ghost therefore generates a nonzero projective
defect module.  The module is stable under every genuine projective word by
composition.  This is the correct residual object for subsequent GST/world
representation arguments: a Hodge counterexample is now a nonzero module for
the actual geometric operator algebra, not merely one unexplained basis sheet.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicGeometry

namespace GSTClassicalHodgePrimitiveProjectiveDefectModule

open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicDefectOperatorDescent
open GSTClassicalHodgeAtomicDefectDuality
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeProjectiveDegreeTrace
open GSTClassicalHodgeAtomicDefectTraceNormalization
open GSTClassicalHodgeTraceZeroPrimitiveTomographyGhost
open GSTClassicalHodgeTraceZeroAtomicOperatorRepresentation
open GSTClassicalHodgeHodgeFunctorialProjectiveDynamics

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

namespace HodgeFunctorialGeometricSemantics.ProjectiveHodgeWord

/-- Orbit set of one atomic defect under the genuine projective word algebra. -/
def defectOrbitSet
    {R : HodgeFunctorialGeometricSemantics V H}
    {p : Nat}
    (z : AtomicDefectSpace V H p) : Set (AtomicDefectSpace V H p) :=
  { y | ∃ w : ProjectiveHodgeWord R p, w.defectOperator z = y }

/-- Rational span of the genuine projective defect orbit. -/
noncomputable def defectOrbitModule
    {R : HodgeFunctorialGeometricSemantics V H}
    {p : Nat}
    (z : AtomicDefectSpace V H p) :
    Submodule ℚ (AtomicDefectSpace V H p) :=
  Submodule.span ℚ (defectOrbitSet (R := R) z)

/-- The starting defect lies in its own projective orbit via the identity word. -/
theorem mem_defectOrbitSet_self
    {R : HodgeFunctorialGeometricSemantics V H}
    {p : Nat}
    (z : AtomicDefectSpace V H p) :
    z ∈ defectOrbitSet (R := R) z := by
  refine ⟨ProjectiveHodgeWord.id, ?_⟩
  unfold defectOperator
  have hid :=
    GSTClassicalHodgeAtomicDefectOperatorDescent.atomicDefectOperator_id
      (V := V) (H := H) (p := p)
      (AtomicNaturalHodgeOperator.id (V := V) (H := H) (p := p)).atomicStable
  exact LinearMap.congr_fun hid z

/-- Hence every starting defect belongs to its orbit module. -/
theorem mem_defectOrbitModule_self
    {R : HodgeFunctorialGeometricSemantics V H}
    {p : Nat}
    (z : AtomicDefectSpace V H p) :
    z ∈ defectOrbitModule (R := R) z :=
  Submodule.subset_span (mem_defectOrbitSet_self (R := R) z)

/-- A nonzero defect generates a nonzero genuine projective defect module. -/
theorem defectOrbitModule_ne_bot
    {R : HodgeFunctorialGeometricSemantics V H}
    {p : Nat}
    {z : AtomicDefectSpace V H p}
    (hz : z ≠ 0) :
    defectOrbitModule (R := R) z ≠ ⊥ := by
  intro hbot
  have hzmem := mem_defectOrbitModule_self (R := R) z
  rw [hbot] at hzmem
  simpa using hz hzmem

/-- Every genuine projective word sends every orbit generator back into the
same orbit set, by word composition. -/
theorem defectOperator_mem_orbitSet_of_mem_orbitSet
    {R : HodgeFunctorialGeometricSemantics V H}
    {p : Nat}
    (w : ProjectiveHodgeWord R p)
    (z y : AtomicDefectSpace V H p)
    (hy : y ∈ defectOrbitSet (R := R) z) :
    w.defectOperator y ∈ defectOrbitSet (R := R) z := by
  rcases hy with ⟨v, rfl⟩
  refine ⟨ProjectiveHodgeWord.comp w v, ?_⟩
  unfold defectOperator
  change (eval w).defectOperator ((eval v).defectOperator z) =
    (eval (ProjectiveHodgeWord.comp w v)).defectOperator z
  unfold ProjectiveHodgeWord.eval
  unfold AtomicNaturalHodgeOperator.defectOperator
  rw [← GSTClassicalHodgeAtomicDefectOperatorDescent.atomicDefectOperator_comp
    (V := V) (H := H) (p := p)
    (eval w).ambient (eval v).ambient
    (eval w).atomicStable (eval v).atomicStable
    ((eval w).comp (eval v)).atomicStable]
  rfl

/-- **GENUINE PROJECTIVE DEFECT MODULE INVARIANCE.**
Every actual projective word preserves the rational span of the orbit. -/
theorem defectOrbitModule_invariant
    {R : HodgeFunctorialGeometricSemantics V H}
    {p : Nat}
    (w : ProjectiveHodgeWord R p)
    (z : AtomicDefectSpace V H p) :
    ∀ y ∈ defectOrbitModule (R := R) z,
      w.defectOperator y ∈ defectOrbitModule (R := R) z := by
  intro y hy
  refine Submodule.span_induction hy ?gen ?zero ?add ?smul
  · intro y hyOrbit
    exact Submodule.subset_span
      (defectOperator_mem_orbitSet_of_mem_orbitSet w z y hyOrbit)
  · exact (defectOrbitModule (R := R) z).zero_mem
  · intro x y hx hy
    exact (defectOrbitModule (R := R) z).add_mem hx hy
  · intro c y hy
    exact (defectOrbitModule (R := R) z).smul_mem c hy

end HodgeFunctorialGeometricSemantics.ProjectiveHodgeWord

/-- One trace-zero primitive tomography ghost gives a distinguished nonzero
state in the atomic-defect quotient. -/
noncomputable def TraceZeroPrimitiveTomographyGhost.defectState
    {G : GeometricCycleClassSpine V H}
    {D : GSTClassicalHodgePrimitiveAtomicDefectReduction.LefschetzPrimitiveDecomposition G}
    {T : ProjectiveDegreeTraceSemantics V H}
    {A : TraceAnchor G T p}
    (E : TraceZeroPrimitiveTomographyGhost A D) :
    AtomicDefectSpace V H p :=
  atomicDefectLinearMap V H p E.traceZeroClass

/-- Its distinguished defect state is nonzero. -/
theorem TraceZeroPrimitiveTomographyGhost.defectState_ne_zero
    {G : GeometricCycleClassSpine V H}
    {D : GSTClassicalHodgePrimitiveAtomicDefectReduction.LefschetzPrimitiveDecomposition G}
    {T : ProjectiveDegreeTraceSemantics V H}
    {A : TraceAnchor G T p}
    (E : TraceZeroPrimitiveTomographyGhost A D) :
    E.defectState ≠ 0 :=
  E.defect_ne_zero

/-- **PRIMITIVE FAILURE PRODUCES A NONZERO GENUINE PROJECTIVE DEFECT MODULE.** -/
theorem primitiveGhost_projectiveDefectModule_ne_bot
    {R : HodgeFunctorialGeometricSemantics V H}
    {D : GSTClassicalHodgePrimitiveAtomicDefectReduction.LefschetzPrimitiveDecomposition R.spine}
    {T : ProjectiveDegreeTraceSemantics V H}
    {A : TraceAnchor R.spine T p}
    (E : TraceZeroPrimitiveTomographyGhost A D) :
    HodgeFunctorialGeometricSemantics.ProjectiveHodgeWord.defectOrbitModule
        (R := R) E.defectState ≠ ⊥ :=
  HodgeFunctorialGeometricSemantics.ProjectiveHodgeWord.defectOrbitModule_ne_bot
    E.defectState_ne_zero

#check HodgeFunctorialGeometricSemantics.ProjectiveHodgeWord.defectOrbitSet
#check HodgeFunctorialGeometricSemantics.ProjectiveHodgeWord.defectOrbitModule
#check HodgeFunctorialGeometricSemantics.ProjectiveHodgeWord.mem_defectOrbitModule_self
#check HodgeFunctorialGeometricSemantics.ProjectiveHodgeWord.defectOrbitModule_ne_bot
#check HodgeFunctorialGeometricSemantics.ProjectiveHodgeWord.defectOrbitModule_invariant
#check TraceZeroPrimitiveTomographyGhost.defectState
#check TraceZeroPrimitiveTomographyGhost.defectState_ne_zero
#check primitiveGhost_projectiveDefectModule_ne_bot

#print axioms HodgeFunctorialGeometricSemantics.ProjectiveHodgeWord.defectOrbitModule_ne_bot
#print axioms HodgeFunctorialGeometricSemantics.ProjectiveHodgeWord.defectOrbitModule_invariant
#print axioms primitiveGhost_projectiveDefectModule_ne_bot

end GSTClassicalHodgePrimitiveProjectiveDefectModule
