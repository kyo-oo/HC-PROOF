import GSTGeneralSpaceCohomology
import GSTClassicalHodgeGeometricCycleClassPointRigidity
import GSTClassicalHodgeGradedGeometricProgramOrbit

/-!
# GST CLASSICAL HODGE — General Space realization

The classical Hodge layer is no longer treated as an unrelated coordinate
universe.  Actual native cycles, geometrically generated Betti classes, and
verified graded geometric programs are realizations/paths of General Space.

No algebraicity of arbitrary Hodge states is assumed here.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeGeneralSpaceRealization

open GSTGeneralSpace
open GSTGeneralSpaceTransport
open GSTGeneralSpaceRealization
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeGeometricCycleClassPointRigidity
open GSTClassicalHodgeGradedGeometricProgramOrbit

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Native codimension-p cycle states form one discrete General Space sector.
This says nothing about whether arbitrary Hodge states are algebraic. -/
def nativeCycleSpace (V : SmoothProjectiveComplexScheme) (p : Nat) :
    GeneralSpace :=
  discrete (codimensionCycles V.X p)

/-- Native face: observe a cycle as itself. -/
def nativeCycleRealization (V : SmoothProjectiveComplexScheme) (p : Nat) :
    Realization (nativeCycleSpace V p) where
  State := codimensionCycles V.X p
  realize := id

/-- Geometric Betti face generated from genuine point fundamental classes,
independent of the arbitrary Stage-2G linear-map presentation. -/
def geometricBettiCycleRealization
    (A : AnalytificationData V) (p : Nat)
    (pt : PointBettiClass (V := V) p A) :
    Realization (nativeCycleSpace V p) where
  State := RationalSingularCohomology A (2 * p)
  realize := fun Z =>
    cycleClassFromPointGeometry (V := V) p A pt Z

/-- Stage-2G supplied Betti face, retained so we can prove compatibility with
the geometric point-generated face instead of silently identifying them. -/
def suppliedBettiCycleRealization
    (H : HodgeBigradedBettiData V) (p : Nat) :
    Realization (nativeCycleSpace V p) where
  State := RationalSingularCohomology H.analytification (2 * p)
  realize := fun Z => H.cycleClass p Z

/-- Once point fundamental classes are identified, the supplied and geometric
Betti faces agree on every native cycle by the repo's point-normal-form
rigidity theorem. -/
theorem supplied_geometric_face_agree
    (H : HodgeBigradedBettiData V) (p : Nat)
    (pt : PointBettiClass (V := V) p H.analytification)
    (hpoint : ∀ x : CodimensionPoint V.X p,
      H.cycleClass p (codimensionPointCycle V.X p x) = pt x)
    (Z : codimensionCycles V.X p) :
    (suppliedBettiCycleRealization H p).realize Z =
      (geometricBettiCycleRealization H.analytification p pt).realize Z := by
  change H.cycleClass p Z =
    cycleClassFromPointGeometry (V := V) p H.analytification pt Z
  rw [suppliedCycleClass_eq_geometric (V := V) p H pt hpoint]

/-- The full graded geometric-program syntax is itself a General Space path
calculus: points are codimensions/weights, paths are genuine finite geometry
programs, identity is `.id`, and composition is ordered program composition. -/
def gradedProgramSpace (V : SmoothProjectiveComplexScheme) : GeneralSpace where
  Point := Nat
  Path := GradedGeometricProgram V
  idPath := GradedGeometricProgram.id
  compPath := fun A B => GradedGeometricProgram.comp A B

/-- Native-cycle semantics of every graded General Space path. -/
noncomputable def nativeProgramTransport
    (G : GeometricCycleClassSpine V H) :
    TransportSystem (gradedProgramSpace V) where
  Fiber := fun p => codimensionCycles V.X p
  transport := fun P Z => P.cycleEval G Z
  transport_id := by
    intro p Z
    rfl
  transport_comp := by
    intro p q r A B Z
    rfl

/-- Rational Betti semantics of the SAME graded General Space paths. -/
noncomputable def bettiProgramTransport
    (G : GeometricCycleClassSpine V H) :
    TransportSystem (gradedProgramSpace V) where
  Fiber := fun p => RationalSingularCohomology H.analytification (2 * p)
  transport := fun P alpha => P.cohomologyEval G alpha
  transport_id := by
    intro p alpha
    rfl
  transport_comp := by
    intro p q r A B alpha
    rfl

#check nativeCycleSpace
#check nativeCycleRealization
#check geometricBettiCycleRealization
#check suppliedBettiCycleRealization
#check supplied_geometric_face_agree
#check gradedProgramSpace
#check nativeProgramTransport
#check bettiProgramTransport

#print axioms supplied_geometric_face_agree
#print axioms nativeProgramTransport
#print axioms bettiProgramTransport

end GSTClassicalHodgeGeneralSpaceRealization
