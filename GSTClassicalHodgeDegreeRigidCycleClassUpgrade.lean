import GSTClassicalHodgeProjectiveDegreeTrace
import GSTClassicalHodgeStage2GSemanticRigidity
import GSTClassicalHodgeZeroDefectCoupledSector

/-!
# GST CLASSICAL HODGE — DEGREE-RIGID CYCLE-CLASS UPGRADE

The Stage-2G semantic countermodel exists only because the stored cycle-class
map is unconstrained.  Projective-degree trace semantics is the first native
geometric law already present in the repository which the zero map cannot
satisfy.

This module records that fact at the exact level needed by the coupled-sector
and tomography attack:

* every genuine codimension point has nonzero Betti cycle class;
* every weight containing a codimension point has a nonzero cycle-class map;
* the zero-cycle-class Stage-2G countermodel admits no projective-degree trace;
* therefore the degree-rigid package is a strict semantic strengthening of the
  old geometric spine, not a renamed Hodge-surjectivity assumption.

No Hodge basis vector is assumed algebraic and no horizontal multiplicity
motion is postulated here.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeDegreeRigidCycleClassUpgrade

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeProjectiveDegreeTrace
open GSTClassicalHodgeStage2GSemanticRigidity
open GSTClassicalHodgeZeroDefectCoupledSector
open GSTClassicalHodgeFiberedNativePullback
open GSTClassicalHodgeFiberedCycleClassDefect

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Positive projective degree forces the genuine Betti class of every native
codimension point to be nonzero. -/
theorem point_cycleClass_ne_zero
    (D : ProjectiveDegreeTraceSemantics V H)
    (q : Nat)
    (x : CodimensionPoint V.X q) :
    H.cycleClass q (codimensionPointCycle V.X q x) ≠ 0 := by
  intro hzero
  have htrace := D.trace_point_cycleClass q x
  rw [hzero, map_zero] at htrace
  exact (ne_of_gt (D.pointDegree_pos q x)) htrace.symm

/-- Hence the whole cycle-class operator in any inhabited codimension cannot
be the zero linear map. -/
theorem cycleClass_ne_zero_of_point
    (D : ProjectiveDegreeTraceSemantics V H)
    (q : Nat)
    (x : CodimensionPoint V.X q) :
    H.cycleClass q ≠ 0 := by
  intro hzero
  have hx := point_cycleClass_ne_zero D q x
  rw [hzero] at hx
  exact hx (by simp)

/-- The exact zero-map semantic countermodel from Stage 2G cannot carry the
projective-degree trace law as soon as one native codimension point exists. -/
theorem zeroCycleClassData_has_no_projectiveDegreeTrace
    (H0 : HodgeBigradedBettiData V)
    (q : Nat)
    (x : CodimensionPoint V.X q) :
    IsEmpty
      (ProjectiveDegreeTraceSemantics V
        (zeroCycleClassData H0)) := by
  refine ⟨?_⟩
  intro D
  have htrace := D.trace_point_cycleClass q x
  change D.trace q
      ((zeroCycleClassData H0).cycleClass q
        (codimensionPointCycle V.X q x)) = D.pointDegree q x at htrace
  rw [zeroCycleClassData_cycleClass, LinearMap.zero_apply, map_zero] at htrace
  exact (ne_of_gt (D.pointDegree_pos q x)) htrace.symm

/-- Degree-rigid classical geometry: the existing geometric spine together
with the independent projective-degree trace artery.  This package excludes
the formal zero-map model but contains no Hodge-surjectivity field. -/
structure DegreeRigidGeometricSemantics
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) where
  spine : GeometricCycleClassSpine V H
  degree : ProjectiveDegreeTraceSemantics V H

namespace DegreeRigidGeometricSemantics

/-- Every native point is homologically visible in degree-rigid geometry. -/
theorem point_visible
    (R : DegreeRigidGeometricSemantics V H)
    (q : Nat)
    (x : CodimensionPoint V.X q) :
    H.cycleClass q (codimensionPointCycle V.X q x) ≠ 0 :=
  point_cycleClass_ne_zero R.degree q x

/-- The cycle-class operator itself is nontrivial in every inhabited
codimension. -/
theorem cycleClass_nontrivial
    (R : DegreeRigidGeometricSemantics V H)
    (q : Nat)
    (x : CodimensionPoint V.X q) :
    H.cycleClass q ≠ 0 :=
  cycleClass_ne_zero_of_point R.degree q x

/-- Any zero-defect common-refinement atom is simultaneously a genuine point
class and its labelled Hodge basis vector; projective degree then certifies
that this common class is nonzero. -/
theorem zeroDefect_atom_common_class_ne_zero
    {p : Nat}
    (R : DegreeRigidGeometricSemantics V H)
    (i : ClassicalHodgeBasisIndex V H p)
    (x : CodimensionPoint V.X p)
    (hzero :
      atom V H p i x ∈
        zeroDefectSector (V := V) (H := H) (p := p)) :
    (classicalHodgeBasis V H p i).1 ≠ 0 := by
  have hagree :=
    (mem_zeroDefectSector_iff (V := V) (H := H)
      (p := p) (atom V H p i x)).mp hzero
  have hagree' :
      H.cycleClass p (codimensionPointCycle V.X p x) =
        (classicalHodgeBasis V H p i).1 := by
    simpa using hagree
  intro hbasis
  have hpoint :
      H.cycleClass p (codimensionPointCycle V.X p x) = 0 := by
    rw [hagree', hbasis]
  exact R.point_visible p x hpoint

end DegreeRigidGeometricSemantics

#check point_cycleClass_ne_zero
#check cycleClass_ne_zero_of_point
#check zeroCycleClassData_has_no_projectiveDegreeTrace
#check DegreeRigidGeometricSemantics
#check DegreeRigidGeometricSemantics.point_visible
#check DegreeRigidGeometricSemantics.zeroDefect_atom_common_class_ne_zero

#print axioms point_cycleClass_ne_zero
#print axioms cycleClass_ne_zero_of_point
#print axioms zeroCycleClassData_has_no_projectiveDegreeTrace
#print axioms DegreeRigidGeometricSemantics.zeroDefect_atom_common_class_ne_zero

end GSTClassicalHodgeDegreeRigidCycleClassUpgrade
