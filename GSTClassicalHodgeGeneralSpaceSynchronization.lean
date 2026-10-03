import GSTClassicalHodgeGeneralSpaceRealization

/-!
# GST CLASSICAL HODGE — General Space synchronization

Native cycles and rational Betti classes now live over the same General Space
path syntax.  The existing master cycle-class naturality theorem becomes a
natural transformation between those two path semantics.

The Hodge defect is therefore not an ad-hoc coordinate subtraction: it is the
difference between two synchronized realizations transported by one cosmic
path.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeGeneralSpaceSynchronization

open GSTGeneralSpaceRealization
open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeGradedGeometricProgramOrbit
open GSTClassicalHodgeGeneralSpaceRealization

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- **GENERAL SPACE CYCLE-CLASS SYNCHRONIZATION.**
The genuine cycle-class map is a natural transformation from native execution
to Betti execution for every verified graded geometric path. -/
noncomputable def cycleClassTransportMorphism
    (G : GeometricCycleClassSpine V H) :
    TransportMorphism (nativeProgramTransport G) (bettiProgramTransport G) where
  map := fun p Z => H.cycleClass p Z
  naturality := by
    intro p q P Z
    exact P.cycleClass_cycleEval G Z

/-- Defect between the native-cycle Betti face and an independently supplied
Betti/Hodge face at the same weight. -/
def programDefect
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (Z : codimensionCycles V.X p)
    (alpha : RationalSingularCohomology H.analytification (2 * p)) :
    RationalSingularCohomology H.analytification (2 * p) :=
  H.cycleClass p Z - alpha

/-- A genuinely synchronized source has zero defect. -/
theorem programDefect_source_zero
    (G : GeometricCycleClassSpine V H)
    (p : Nat) (Z : codimensionCycles V.X p) :
    programDefect G p Z (H.cycleClass p Z) = 0 := by
  simp [programDefect]

/-- **UNIVERSAL DEFECT TRANSPORT LAW.**
For one genuine General Space geometry path, target defect is exactly the Betti
transport of source defect.  This is the realization-level law requested by
the General Space redesign. -/
theorem programDefect_transport
    (G : GeometricCycleClassSpine V H)
    {p q : Nat}
    (P : GradedGeometricProgram V p q)
    (Z : codimensionCycles V.X p)
    (alpha : RationalSingularCohomology H.analytification (2 * p)) :
    programDefect G q (P.cycleEval G Z) (P.cohomologyEval G alpha) =
      P.cohomologyEval G (programDefect G p Z alpha) := by
  simp [programDefect, P.cycleClass_cycleEval G Z]

/-- Zero synchronization defect propagates through every genuine graded
geometry path. -/
theorem programDefect_zero_propagates
    (G : GeometricCycleClassSpine V H)
    {p q : Nat}
    (P : GradedGeometricProgram V p q)
    (Z : codimensionCycles V.X p)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (hzero : programDefect G p Z alpha = 0) :
    programDefect G q (P.cycleEval G Z) (P.cohomologyEval G alpha) = 0 := by
  rw [programDefect_transport G P Z alpha, hzero]
  simp

/-- The naturality square can be read directly as equality of the two target
faces of one transported cosmic state. -/
theorem native_betti_faces_synchronize
    (G : GeometricCycleClassSpine V H)
    {p q : Nat}
    (P : GradedGeometricProgram V p q)
    (Z : codimensionCycles V.X p) :
    H.cycleClass q ((nativeProgramTransport G).transport P Z) =
      (bettiProgramTransport G).transport P (H.cycleClass p Z) := by
  exact P.cycleClass_cycleEval G Z

#check cycleClassTransportMorphism
#check programDefect
#check programDefect_source_zero
#check programDefect_transport
#check programDefect_zero_propagates
#check native_betti_faces_synchronize

#print axioms cycleClassTransportMorphism
#print axioms programDefect_transport
#print axioms programDefect_zero_propagates

end GSTClassicalHodgeGeneralSpaceSynchronization
