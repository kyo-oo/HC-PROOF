import GSTGeneralSpaceCohomology
import GSTGraphV2NonEuclidean

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

end GSTGraphV2GeneralSpaceRealization
