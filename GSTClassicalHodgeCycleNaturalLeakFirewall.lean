import GSTClassicalHodgeCanonicalLeakRealizationBarrier
import GSTClassicalHodgeCycleOperatorNaturality

/-!
# GST CLASSICAL HODGE — CYCLE-NATURAL LEAK FIREWALL

The canonical spine/ghost construction isolates one exact nonzero GST value:
the universal two-slot transfer from the live coordinate of the genuine
projective spine to the sheet detected by an omniversal separator ghost.

Earlier files prove that this value is outside the actual cycle-class range
and cannot be realized by a verified graded geometric program.  This file
strengthens the obstruction from those particular program syntaxes to the
entire class of linear native operators carrying an exact cycle-class
naturality square.

The argument is completely intrinsic to the existing GST/native cosmology.
The spine source is already an actual native cycle.  Therefore every genuine
cycle-class-natural operator sends it to another actual cycle class, and the
omniversal separator annihilates the result.  The GST two-slot leak, however,
has nonzero separator read.  Hence no cycle-natural native operator can have
that leak as its cohomological action on the spine source.

Equivalently: any ambient cohomology operator which agrees with the canonical
GST leak on the spine source has no native linear lift commuting with the
cycle-class map.  This rules out *all* factorized/native-linear
externalizations at once; a successful completion cannot obtain the ghost
motion by merely choosing another native operator inside the current
cycle-natural category.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeCycleNaturalLeakFirewall

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeAtomicAnnihilator
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeLimitlessSpinePropagation
open GSTClassicalHodgeOmniversalSeparatorGhostCrown
open GSTClassicalHodgeGhostSpineCosmicLeak
open GSTClassicalHodgeCanonicalLeakRealizationBarrier
open GSTClassicalHodgeCycleOperatorNaturality

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Every genuine cycle-class-natural operator has zero separator read on the
canonical algebraic spine source of an omniversal ghost.  This is independent
of any projective-word, correspondence-word, or finite-chart presentation. -/
theorem cycleNatural_on_ghostSpine_detector_eq_zero
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (E : OmniversalSeparatorGhost G)
    (T : CycleClassOperatorPair V H E.weight) :
    E.separator.detector
      (T.cohomologyOperator (ghostSpineSeed G M E).hodge.1) = 0 := by
  have hnat := T.cycleClass_cycleOperator (ghostSpineSeed G M E).cycle
  rw [(ghostSpineSeed G M E).class_eq] at hnat
  have hrange :
      T.cohomologyOperator (ghostSpineSeed G M E).hodge.1 ∈
        LinearMap.range (H.cycleClass E.weight) :=
    ⟨T.cycleOperator (ghostSpineSeed G M E).cycle, hnat⟩
  have hatomic :
      T.cohomologyOperator (ghostSpineSeed G M E).hodge.1 ∈
        pointCycleClassSpan E.weight (H.cycleClass E.weight) := by
    rw [← smoothProjective_cycleClass_range_eq_atomic_span V H E.weight]
    exact hrange
  have hker :
      pointCycleClassSpan E.weight (H.cycleClass E.weight) ≤
        LinearMap.ker E.separator.detector :=
    (annihilatesPointCycles_iff_atomicSpan_le_ker
      E.weight (H.cycleClass E.weight) E.separator.detector).mp
      E.separator.annihilates_atoms
  exact hker hatomic

/-- The canonical GST leak itself has nonzero separator read. -/
theorem canonicalLeakValue_detector_ne_zero
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (E : OmniversalSeparatorGhost G) :
    E.separator.detector (canonicalLeakValue G M E) ≠ 0 := by
  simpa [canonicalLeakValue] using
    (ghostSpine_twoSlot_detector_ne_zero G M E)

/-- **ALL CYCLE-NATURAL OPERATORS ARE EXCLUDED.**
No native/cohomological operator pair commuting with the actual cycle-class map
can send the canonical algebraic spine source to the canonical GST ghost leak. -/
theorem no_cycleNatural_realization_of_canonicalLeak
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (E : OmniversalSeparatorGhost G) :
    IsEmpty
      { T : CycleClassOperatorPair V H E.weight //
        T.cohomologyOperator (ghostSpineSeed G M E).hodge.1 =
          canonicalLeakValue G M E } := by
  refine ⟨?_⟩
  rintro ⟨T, hT⟩
  have hzero := cycleNatural_on_ghostSpine_detector_eq_zero G M E T
  rw [hT] at hzero
  exact canonicalLeakValue_detector_ne_zero G M E hzero

/-- Ambient-operator form of the firewall.  If a cohomology operator agrees
with the GST leak on the canonical spine source, then it admits no native
linear lift whose square with the actual cycle-class map commutes. -/
theorem canonicalLeakOperator_has_no_native_cycleClass_lift
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (E : OmniversalSeparatorGhost G)
    (T : Module.End ℚ
      (RationalSingularCohomology H.analytification (2 * E.weight)))
    (hT : T (ghostSpineSeed G M E).hodge.1 =
      canonicalLeakValue G M E) :
    ¬ ∃ A : Module.End ℚ (codimensionCycles V.X E.weight),
      (H.cycleClass E.weight).comp A =
        T.comp (H.cycleClass E.weight) := by
  rintro ⟨A, hA⟩
  let R : CycleClassOperatorPair V H E.weight := {
    cycleOperator := A
    cohomologyOperator := T
    cycleClass_natural := hA
  }
  let W :
      { Q : CycleClassOperatorPair V H E.weight //
        Q.cohomologyOperator (ghostSpineSeed G M E).hodge.1 =
          canonicalLeakValue G M E } :=
    ⟨R, hT⟩
  exact (no_cycleNatural_realization_of_canonicalLeak G M E).false W

/-- Counterexample normal form at the strongest operator-independent level:
if the Stage-2G Hodge statement fails, one omniversal ghost is selected such
that every ambient operator realizing its canonical GST spine-to-ghost value
on the actual spine source necessarily fails to admit any cycle-class-natural
native lift. -/
theorem failure_yields_cycleNatural_leak_blackout
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (hnot : ¬ BigradedBettiHodgeStatement V H) :
    ∃ E : OmniversalSeparatorGhost G,
      ∀ T : Module.End ℚ
        (RationalSingularCohomology H.analytification (2 * E.weight)),
        T (ghostSpineSeed G M E).hodge.1 = canonicalLeakValue G M E →
        ¬ ∃ A : Module.End ℚ (codimensionCycles V.X E.weight),
          (H.cycleClass E.weight).comp A =
            T.comp (H.cycleClass E.weight) := by
  rcases (not_hodge_iff_nonempty_omniversalSeparatorGhost G).mp hnot with ⟨E⟩
  refine ⟨E, ?_⟩
  intro T hT
  exact canonicalLeakOperator_has_no_native_cycleClass_lift G M E T hT

#check cycleNatural_on_ghostSpine_detector_eq_zero
#check canonicalLeakValue_detector_ne_zero
#check no_cycleNatural_realization_of_canonicalLeak
#check canonicalLeakOperator_has_no_native_cycleClass_lift
#check failure_yields_cycleNatural_leak_blackout

#print axioms cycleNatural_on_ghostSpine_detector_eq_zero
#print axioms no_cycleNatural_realization_of_canonicalLeak
#print axioms canonicalLeakOperator_has_no_native_cycleClass_lift
#print axioms failure_yields_cycleNatural_leak_blackout

end GSTClassicalHodgeCycleNaturalLeakFirewall
