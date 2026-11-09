import GSTGraphV2NativeCurvatureBirth
import GSTHodgeSingleHypothesisConditional

/-!
GST Graph V2 integrated information/CM/curvature original-X word calculus.
The two geometric operators must be genuine CycleClassOperatorPairs,
not arbitrary dimensionless graph transitions. Curvature is their
noncommutative commutator and every finite word yields an original-X
cycle with the exact cohomological word class.
This connects the active GST Hodge hypothesis with the wave/CM/curvature
geometry without inserting a Hodge-to-Chow inverse.
-/

noncomputable section

namespace GSTGraphV2IntegratedWaveCMGate

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeCycleOperatorNaturality
open GSTGraphV2NativeCurvatureBirth

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Actual event types in a proposed geometric wave/CM realization. -/
inductive Mode
  | wave
  | cm
  | curvature
  deriving DecidableEq, Repr

def nativeStep (A B : CycleClassOperatorPair V H p) :
    Mode → codimensionCycles V.X p → codimensionCycles V.X p
  | .wave, Z => A.cycleOperator Z
  | .cm, Z => B.cycleOperator Z
  | .curvature, Z => nativeCurvatureCycle A B Z

def hodgeStep (A B : CycleClassOperatorPair V H p) :
    Mode → RationalSingularCohomology H.analytification (2*p) →
      RationalSingularCohomology H.analytification (2*p)
  | .wave, z => A.cohomologyOperator z
  | .cm, z => B.cohomologyOperator z
  | .curvature, z =>
      A.cohomologyOperator (B.cohomologyOperator z) -
      B.cohomologyOperator (A.cohomologyOperator z)

theorem step_cycleClass
    (A B : CycleClassOperatorPair V H p)
    (m : Mode) (Z : codimensionCycles V.X p) :
    H.cycleClass p (nativeStep A B m Z) =
      hodgeStep A B m (H.cycleClass p Z) := by
  cases m with
  | wave =>
      exact A.cycleClass_cycleOperator Z
  | cm =>
      exact B.cycleClass_cycleOperator Z
  | curvature =>
      exact nativeCurvature_cycleClass A B Z

/-- All finite mixed words in information, CM and curvature modes. -/
def nativeWord (A B : CycleClassOperatorPair V H p) :
    List Mode → codimensionCycles V.X p → codimensionCycles V.X p
  | [], Z => Z
  | m :: ms, Z => nativeWord A B ms (nativeStep A B m Z)

def hodgeWord (A B : CycleClassOperatorPair V H p) :
    List Mode →
      RationalSingularCohomology H.analytification (2*p) →
      RationalSingularCohomology H.analytification (2*p)
  | [], z => z
  | m :: ms, z => hodgeWord A B ms (hodgeStep A B m z)

/-- Complete mixed-word naturality, with no bound on causal word length. -/
theorem word_cycleClass
    (A B : CycleClassOperatorPair V H p)
    (ms : List Mode) (Z : codimensionCycles V.X p) :
    H.cycleClass p (nativeWord A B ms Z) =
      hodgeWord A B ms (H.cycleClass p Z) := by
  induction ms generalizing Z with
  | nil =>
      rfl
  | cons m ms ih =>
      change H.cycleClass p
          (nativeWord A B ms (nativeStep A B m Z)) =
        hodgeWord A B ms
          (hodgeStep A B m (H.cycleClass p Z))
      rw [ih, step_cycleClass]

/-- Source-range invariant for all arbitrary-length causal programs. -/
theorem word_in_cycleClass_range
    (A B : CycleClassOperatorPair V H p)
    (ms : List Mode) (Z : codimensionCycles V.X p) :
    hodgeWord A B ms (H.cycleClass p Z) ∈
      LinearMap.range (H.cycleClass p) := by
  exact ⟨nativeWord A B ms Z, word_cycleClass A B ms Z⟩

/-- A prescribed target reached by genuine operators has an actual
original-X algebraic-cycle representative, defined constructively. -/
theorem originalX_cycle_of_prescribed_reachable_target
    (A B : CycleClassOperatorPair V H p)
    (ms : List Mode)
    (Z : codimensionCycles V.X p)
    (alpha : RationalSingularCohomology H.analytification (2*p))
    (hReach : hodgeWord A B ms (H.cycleClass p Z) = alpha) :
    ∃ Zalpha : codimensionCycles V.X p, H.cycleClass p Zalpha = alpha := by
  exact ⟨nativeWord A B ms Z, (word_cycleClass A B ms Z).trans hReach⟩

theorem every_geometric_word_is_algebraic
    (A B : CycleClassOperatorPair V H p)
    (sources : Nat → codimensionCycles V.X p)
    (program : Nat → List Mode) (n : Nat) :
    hodgeWord A B (program n) (H.cycleClass p (sources n)) ∈
      LinearMap.range (H.cycleClass p) := by
  exact word_in_cycleClass_range A B (program n) (sources n)

#check word_cycleClass
#check word_in_cycleClass_range
#check originalX_cycle_of_prescribed_reachable_target
#print axioms word_cycleClass

end GSTGraphV2IntegratedWaveCMGate
