import GSTClassicalHodgeCorrespondenceGhostGaugeFreedom
import GSTClassicalHodgeAtomicSpan
import GSTClassicalHodgeAtomicDefectDuality

/-!
# GST CLASSICAL HODGE — CORRESPONDENCE RANGE RIGIDITY / FIRST-GHOST FRONTIER

The previous module exhibits gauge freedom in the ambient cohomological action
stored by `GradedCorrespondencePointNaturality`.  This file identifies exactly
where that freedom disappears.

For one fixed genuine finite closed correspondence K, ANY two pointwise-natural
cohomological actions agree on the entire actual cycle-class range, because on
a class `cl(Z)` both are forced to equal the cycle class of the same native
correspondence image of Z.

The canonical trace-zero first ghost, however, is provably outside that range:
its atomic defect is nonzero, while for smooth projective X the cycle-class
range is exactly the atomic point-cycle span.

Thus the formal boundary is exact:

* algebraic inputs: correspondence action is rigid from native geometry;
* first ghost: point-cycle naturality does not determine the action.

Any airtight first-ghost return packet must therefore import an independently
constructed geometric Betti action of the correspondence (or an equivalent
geometric theorem determining its value on the ghost).  It cannot be obtained
merely by extending the native cycle action linearly off the algebraic range.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeCorrespondenceRangeRigidityFrontier

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeAtomicDefectDuality
open GSTClassicalHodgeGradedFiniteClosedCorrespondence
open GSTClassicalHodgeCorrespondenceGhostGaugeFreedom
open GSTClassicalHodgeTraceZeroPrimitiveTomographyGhost
open GSTClassicalHodgePrimitiveAtomicDefectReduction
open GSTClassicalHodgeAtomicDefectTraceNormalization
open GSTClassicalHodgeProjectiveDegreeTrace
open GSTClassicalHodgeGeometricCycleClassSpine

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p q : Nat}

/-- Two pointwise-natural cohomological realizations of the SAME actual closed
correspondence agree on every honest native cycle class. -/
theorem pointNaturality_agree_on_cycleClass
    {K : GSTClassicalHodgeFiniteClosedCorrespondence.FiniteClosedCorrespondence V}
    (N₁ N₂ : GradedCorrespondencePointNaturality K H p q)
    (Z : codimensionCycles V.X p) :
    N₁.cohomologyOperator (H.cycleClass p Z) =
      N₂.cohomologyOperator (H.cycleClass p Z) := by
  calc
    N₁.cohomologyOperator (H.cycleClass p Z) =
        H.cycleClass q (K.gradedNativeCycleOperator p q Z) :=
      (N₁.cycleClass_natural Z).symm
    _ = N₂.cohomologyOperator (H.cycleClass p Z) :=
      N₂.cycleClass_natural Z

/-- Range form: pointwise naturality completely fixes the cohomological action
on the actual cycle-class range. -/
theorem pointNaturality_agree_on_cycleClassRange
    {K : GSTClassicalHodgeFiniteClosedCorrespondence.FiniteClosedCorrespondence V}
    (N₁ N₂ : GradedCorrespondencePointNaturality K H p q)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha : alpha ∈ LinearMap.range (H.cycleClass p)) :
    N₁.cohomologyOperator alpha = N₂.cohomologyOperator alpha := by
  rcases halpha with ⟨Z, rfl⟩
  exact pointNaturality_agree_on_cycleClass N₁ N₂ Z

/-- A trace-zero primitive tomography ghost is not the cycle class of any
native codimension-p algebraic cycle.  This is an immediate but crucial
consequence of its nonzero atomic defect. -/
theorem firstGhost_not_mem_cycleClassRange
    {G : GeometricCycleClassSpine V H}
    {D : LefschetzPrimitiveDecomposition G}
    {T : ProjectiveDegreeTraceSemantics V H}
    {A : TraceAnchor G T p}
    (E : TraceZeroPrimitiveTomographyGhost A D) :
    E.traceZeroClass.1 ∉ LinearMap.range (H.cycleClass p) := by
  intro hrange
  have hspan :
      E.traceZeroClass.1 ∈ pointCycleClassSpan p (H.cycleClass p) := by
    rw [← smoothProjective_cycleClass_range_eq_atomic_span V H p]
    exact hrange
  have hzero : atomicDefectLinearMap V H p E.traceZeroClass = 0 := by
    rw [atomicDefectLinearMap_apply]
    exact (Submodule.Quotient.mk_eq_zero
      (pointCycleClassSpan p (H.cycleClass p))).2 hspan
  exact E.defect_ne_zero hzero

/-- Consequently the standard cycle-class commuting square determines every
algebraic input but supplies no range-rigidity theorem at the first ghost. -/
theorem firstGhost_outside_pointNaturality_rigid_domain
    {G : GeometricCycleClassSpine V H}
    {D : LefschetzPrimitiveDecomposition G}
    {T : ProjectiveDegreeTraceSemantics V H}
    {A : TraceAnchor G T p}
    (E : TraceZeroPrimitiveTomographyGhost A D) :
    ¬ E.traceZeroClass.1 ∈ LinearMap.range (H.cycleClass p) :=
  firstGhost_not_mem_cycleClassRange E

/-- Explicit sharpness of the boundary.  If the target cohomology has one
nonzero vector, then for every pointwise-natural action N there is another
pointwise-natural action for the SAME actual correspondence which agrees with N
on the entire cycle-class range but differs on the canonical first ghost. -/
theorem exists_same_range_different_firstGhost_action
    {G : GeometricCycleClassSpine V H}
    {D : LefschetzPrimitiveDecomposition G}
    {T : ProjectiveDegreeTraceSemantics V H}
    {A : TraceAnchor G T p}
    (E : TraceZeroPrimitiveTomographyGhost A D)
    {K : GSTClassicalHodgeFiniteClosedCorrespondence.FiniteClosedCorrespondence V}
    (N : GradedCorrespondencePointNaturality K H p q)
    (v : RationalSingularCohomology H.analytification (2 * q))
    (hv : v ≠ 0) :
    ∃ N' : GradedCorrespondencePointNaturality K H p q,
      (∀ alpha,
        alpha ∈ LinearMap.range (H.cycleClass p) →
          N'.cohomologyOperator alpha = N.cohomologyOperator alpha)
      ∧ N'.cohomologyOperator E.traceZeroClass.1 ≠
          N.cohomologyOperator E.traceZeroClass.1 := by
  let d := E.source.detector
  have hd : AnnihilatesPointCycleClasses p (H.cycleClass p) d :=
    E.source.annihilates_atoms
  let N' := perturbPointNaturality N d hd v
  refine ⟨N', ?_, ?_⟩
  · intro alpha halpha
    exact pointNaturality_agree_on_cycleClassRange N' N alpha halpha
  · exact perturbPointNaturality_changes_detected_class
      N d hd v hv E.traceZeroClass.1 E.separator_detects

#check pointNaturality_agree_on_cycleClass
#check pointNaturality_agree_on_cycleClassRange
#check firstGhost_not_mem_cycleClassRange
#check exists_same_range_different_firstGhost_action

#print axioms pointNaturality_agree_on_cycleClassRange
#print axioms firstGhost_not_mem_cycleClassRange
#print axioms exists_same_range_different_firstGhost_action

end GSTClassicalHodgeCorrespondenceRangeRigidityFrontier
