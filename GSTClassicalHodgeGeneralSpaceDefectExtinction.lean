import GSTClassicalHodgeGeneralSpaceSynchronization
import GSTClassicalHodgeExactClayStatement

/-!
# GST CLASSICAL HODGE — General Space defect extinction

This module performs the no-cheating part of the Hodge attack.  Whenever a
verified General Space geometric path sends an actual algebraic source class
to a target Betti/Hodge state, the SAME path sends the native source cycle to
an explicit native target cycle.  Synchronization then identifies its cycle
class with the target.

No theorem here assumes that every Hodge target is reachable.  That global
construction remains mathematics to be proved by the enlarged GST cosmology.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeGeneralSpaceDefectExtinction

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeGradedGeometricProgramOrbit
open GSTClassicalHodgeGeneralSpaceSynchronization
open GSTClassicalHodgeExactClayStatement

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- **CONSTRUCTIVE GENERAL SPACE LANDING.**
A genuine path hit constructs the target algebraic cycle; no target cycle is
supplied as an input. -/
theorem target_algebraic_of_program_hit
    (G : GeometricCycleClassSpine V H)
    {p q : Nat}
    (P : GradedGeometricProgram V p q)
    (Z : codimensionCycles V.X p)
    (alpha : RationalSingularCohomology H.analytification (2 * q))
    (hhit : P.cohomologyEval G (H.cycleClass p Z) = alpha) :
    ∃ Ztarget : codimensionCycles V.X q,
      H.cycleClass q Ztarget = alpha := by
  refine ⟨P.cycleEval G Z, ?_⟩
  calc
    H.cycleClass q (P.cycleEval G Z) =
        P.cohomologyEval G (H.cycleClass p Z) :=
      P.cycleClass_cycleEval G Z
    _ = alpha := hhit

/-- The target defect itself vanishes for every genuine path hit. -/
theorem target_programDefect_zero_of_hit
    (G : GeometricCycleClassSpine V H)
    {p q : Nat}
    (P : GradedGeometricProgram V p q)
    (Z : codimensionCycles V.X p)
    (alpha : RationalSingularCohomology H.analytification (2 * q))
    (hhit : P.cohomologyEval G (H.cycleClass p Z) = alpha) :
    programDefect G q (P.cycleEval G Z) alpha = 0 := by
  rw [← hhit]
  exact programDefect_zero_propagates G P Z (H.cycleClass p Z)
    (programDefect_source_zero G p Z)

/-- A rational separator annihilating every actual cycle class cannot detect a
target reached by a genuine General Space geometric path. -/
theorem separator_cannot_detect_program_hit
    (G : GeometricCycleClassSpine V H)
    {p q : Nat}
    (P : GradedGeometricProgram V p q)
    (Z : codimensionCycles V.X p)
    (alpha : RationalSingularCohomology H.analytification (2 * q))
    (lambda : RationalSingularCohomology H.analytification (2 * q) →ₗ[ℚ] ℚ)
    (hann : ∀ W : codimensionCycles V.X q,
      lambda (H.cycleClass q W) = 0)
    (hhit : P.cohomologyEval G (H.cycleClass p Z) = alpha) :
    lambda alpha = 0 := by
  rcases target_algebraic_of_program_hit G P Z alpha hhit with
    ⟨W, hW⟩
  rw [← hW]
  exact hann W

/-- Contradiction form used by defect/separator attacks. -/
theorem no_separator_for_program_hit
    (G : GeometricCycleClassSpine V H)
    {p q : Nat}
    (P : GradedGeometricProgram V p q)
    (Z : codimensionCycles V.X p)
    (alpha : RationalSingularCohomology H.analytification (2 * q))
    (lambda : RationalSingularCohomology H.analytification (2 * q) →ₗ[ℚ] ℚ)
    (hann : ∀ W : codimensionCycles V.X q,
      lambda (H.cycleClass q W) = 0)
    (hdetect : lambda alpha ≠ 0)
    (hhit : P.cohomologyEval G (H.cycleClass p Z) = alpha) : False := by
  exact hdetect (separator_cannot_detect_program_hit
    G P Z alpha lambda hann hhit)

/-- Elementwise exact Hodge landing: if the enlarged GST cosmology constructs
a genuine path hit for THIS Hodge class, the literal algebraic-cycle witness
is produced immediately.  No global reachability premise is packaged here. -/
theorem hodge_class_algebraic_of_constructed_program
    (G : GeometricCycleClassSpine V H)
    (q : Nat)
    (alpha : RationalSingularCohomology H.analytification (2 * q))
    (_halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading q))
    {p : Nat}
    (P : GradedGeometricProgram V p q)
    (Z : codimensionCycles V.X p)
    (hhit : P.cohomologyEval G (H.cycleClass p Z) = alpha) :
    ∃ W : codimensionCycles V.X q,
      H.cycleClass q W = alpha :=
  target_algebraic_of_program_hit G P Z alpha hhit

#check target_algebraic_of_program_hit
#check target_programDefect_zero_of_hit
#check separator_cannot_detect_program_hit
#check no_separator_for_program_hit
#check hodge_class_algebraic_of_constructed_program

#print axioms target_algebraic_of_program_hit
#print axioms target_programDefect_zero_of_hit
#print axioms no_separator_for_program_hit

end GSTClassicalHodgeGeneralSpaceDefectExtinction
