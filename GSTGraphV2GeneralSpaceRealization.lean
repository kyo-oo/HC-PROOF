import GSTGeneralSpaceCohomology
import GSTGraphV2NonEuclidean
import GSTCausalFoldDefect

namespace GSTGraphV2GeneralSpaceRealization

open GSTGeneralSpace
open GSTGraphV2NonEuclidean

/-- Graph-V2's seven-axis states form a General Space whose paths are finite
reflexive/transitive chains of genuine Graph-V2 forward edges. -/
def graphV2GeneralSpace : GeneralSpace where
  Point := SevenAxes
  Path := Relation.ReflTransGen ForwardEdge
  idPath := fun x => Relation.ReflTransGen.refl
  compPath := fun α β => α.trans β
  comp_id_left := by intros; apply Subsingleton.elim
  comp_id_right := by intros; apply Subsingleton.elim
  comp_assoc := by intros; apply Subsingleton.elim

/-- The seven-axis packet itself is a chart of the General Space sector. -/
def sevenAxesChart : GeneralSpace.Chart graphV2GeneralSpace where
  Coord := SevenAxes
  observe := id

@[simp] theorem sevenAxesChart_exact (a : SevenAxes) :
    sevenAxesChart.observe a = a := rfl

/-- The historical forward edge embeds as a one-step General Space path. -/
def forwardEdgePath {u v : SevenAxes} (h : ForwardEdge u v) :
    graphV2GeneralSpace.Path u v :=
  Relation.ReflTransGen.single h

/-- Every canonical Graph-V2 forward-path step is a General Space path. -/
def canonicalStepPath (R N start L i : Nat) :
    graphV2GeneralSpace.Path
      ((forwardPath R N start L).node i)
      ((forwardPath R N start L).node (i+1)) :=
  forwardEdgePath (forwardPath_edge_exact R N start L i)

/-- The old three-space label becomes an observable of the General Space
sector, not a restriction on the ontology. -/
def spaceObservable : GeneralSpace.Observable graphV2GeneralSpace Space :=
  fun a => a.yPrime

/-- Digit content is another chart observable. -/
def digitObservable : GeneralSpace.Observable graphV2GeneralSpace Nat :=
  fun a => a.z

/-- Carry content is another chart observable. -/
def carryObservable : GeneralSpace.Observable graphV2GeneralSpace Nat :=
  fun a => a.y

/-- Witnesshood is now an intrinsic predicate on this Graph-V2 realization. -/
def witnessPredicate : GeneralSpace.Predicate graphV2GeneralSpace := WitnessAt

/-- The historical arithmetic projection is explicitly a realization into the
General Space sector. -/
def physicalPointRealization (E N t p : Nat) : graphV2GeneralSpace.Point :=
  physicalProjection E N t p

#check graphV2GeneralSpace
#check sevenAxesChart
#check forwardEdgePath
#check canonicalStepPath
#check spaceObservable
#check digitObservable
#check carryObservable
#check witnessPredicate
#check physicalPointRealization

/-! Realized causal fold defects. Forward reachability by itself does not
assert Hodge preservation; the operator square must actually commute. -/
section OperatorDefect
open GSTCausalFoldDefect
variable {R : Type*} [Ring R]

theorem forward_pair_defect
    (P : OperatorRealization graphV2GeneralSpace R)
    {u v w : SevenAxes} (huv : ForwardEdge u v) (hvw : ForwardEdge v w)
    (J K L : R) :
    defect J L (P.operator (graphV2GeneralSpace.compPath
      (forwardEdgePath huv) (forwardEdgePath hvw))) =
      defect K L (P.operator (forwardEdgePath hvw)) *
        P.operator (forwardEdgePath huv) +
      P.operator (forwardEdgePath hvw) *
        defect J K (P.operator (forwardEdgePath huv)) := by
  exact causal_path_defect P (forwardEdgePath huv) (forwardEdgePath hvw) J K L

theorem safe_forward_pair
    (P : OperatorRealization graphV2GeneralSpace R)
    {u v w : SevenAxes} (huv : ForwardEdge u v) (hvw : ForwardEdge v w)
    (J K L : R)
    (hFirst : defect J K (P.operator (forwardEdgePath huv)) = 0)
    (hSecond : defect K L (P.operator (forwardEdgePath hvw)) = 0) :
    defect J L (P.operator (graphV2GeneralSpace.compPath
      (forwardEdgePath huv) (forwardEdgePath hvw))) = 0 := by
  rw [forward_pair_defect, hFirst, hSecond]
  simp

#print axioms forward_pair_defect
#print axioms safe_forward_pair
end OperatorDefect

end GSTGraphV2GeneralSpaceRealization
