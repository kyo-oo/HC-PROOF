import GSTGeneralSpaceCohomology
import GSTGraphV2NonEuclidean
import GSTGraphV2ScaleEquivariance

/-!
# GST GRAPH V2 — General Space realization

Graph V2 is now one exact realization of the carrier-independent General Space
ontology.  Its natural-number path parameter and seven-axis packet are charts;
they are not the ontology itself.
-/

namespace GSTGraphV2GeneralSpaceRealization

open GSTGeneralSpace
open GSTGraphV2NonEuclidean
open GSTGraphV2ScaleEquivariance

/-- Positions of one existing Graph-V2 world form a preorder-path realization
of General Space.  The use of `Nat` is local to this chart. -/
def graphPositionSpace (_G : Graph) : GeneralSpace :=
  ofPreorder Nat

/-- The full decorated Graph-V2 vertex is one chart of the General Space. -/
def vertexChart (G : Graph) : Chart (graphPositionSpace G) where
  Coord := Vertex
  observe := fun p => vertex G p

/-- The seven non-dimensional axes are another, coarser chart. -/
def sevenAxesChart (G : Graph) : Chart (graphPositionSpace G) where
  Coord := SevenAxes
  observe := fun p => (vertex G p).axes

/-- Graph overlay data are an independent observation face. -/
def overlayChart (G : Graph) : Chart (graphPositionSpace G) where
  Coord := Overlay
  observe := fun p => (vertex G p).overlay

/-- Every canonical next position is an actual General Space path. -/
def nextPath (G : Graph) (p : Nat) :
    (graphPositionSpace G).Path p (p + 1) := by
  exact Nat.le_succ p

/-- The seven-axis chart recovers the original exact forward-edge geometry on
canonical successive observations. -/
theorem sevenAxes_next_is_forwardEdge (G : Graph) (p : Nat) :
    ForwardEdge
      ((sevenAxesChart G).observe p)
      ((sevenAxesChart G).observe (p + 1)) := by
  rfl

/-- Existing U-cut packet transport is literally a chart-recoordination law:
the complete observable packet is unchanged after the cut/rebase. -/
theorem uCut_chart_recoordination
    (t n K x p : Nat) :
    physicalPacket (4^(3^t*n)) x p =
      physicalPacket (uTailEnergy t n K)
        (uPhaseShift t n K + x) p :=
  physicalPacket_u_cut_exact t n K x p

/-- Every observable of the Graph-V2 packet is automatically invariant under
that recoordination. -/
theorem uCut_intrinsic_observable
    {α : Type} (F : PhysicalPacket → α)
    (t n K x p : Nat) :
    F (physicalPacket (4^(3^t*n)) x p) =
      F (physicalPacket (uTailEnergy t n K)
        (uPhaseShift t n K + x) p) :=
  u_cut_observable_exact F t n K x p

/-- Every intrinsic predicate of the packet is recoordination invariant. -/
theorem uCut_intrinsic_predicate
    (P : PhysicalPacket → Prop)
    (t n K x p : Nat) :
    P (physicalPacket (4^(3^t*n)) x p) ↔
      P (physicalPacket (uTailEnergy t n K)
        (uPhaseShift t n K + x) p) :=
  u_cut_predicate_iff P t n K x p

#check graphPositionSpace
#check vertexChart
#check sevenAxesChart
#check nextPath
#check sevenAxes_next_is_forwardEdge
#check uCut_chart_recoordination
#check uCut_intrinsic_observable
#check uCut_intrinsic_predicate

#print axioms sevenAxes_next_is_forwardEdge
#print axioms uCut_chart_recoordination
#print axioms uCut_intrinsic_observable

end GSTGraphV2GeneralSpaceRealization
