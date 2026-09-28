import GSTClassicalHodgeLimitlessSeparatorGhost
import GSTClassicalHodgeGradedSeparatorBackpropagation
import GSTClassicalHodgeSingleSheetCrown

/-!
# GST CLASSICAL HODGE — OMNIVERSAL SEPARATOR-GHOST CROWN

This module packages the strongest obstruction form obtained from the upgraded
limitless/fibered/graded geometry stack.

A genuine Stage-2G failure cannot remain an unspecified missing cycle.  It
forces one basis sheet together with a completed limitless dual probe which is
nonzero on that exact sheet and orthogonal to every algebraic Hodge state.  The
same detector is orthogonal to every state obtained from every native cycle by
every verified graded geometric program.  Pulling it backward through any such
program preserves atomic annihilation.

Thus the obstruction is a coherent ghost cone over the entire independently
verified projective + principal-cut cosmology.
-/

set_option maxHeartbeats 90000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeOmniversalSeparatorGhostCrown

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicAnnihilator
open GSTClassicalHodgeSingleSheetCrown
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeGradedGeometricProgramOrbit
open GSTClassicalHodgeLimitlessSeparatorGhost
open GSTClassicalHodgeGradedSeparatorBackpropagation
open GSTClassicalHodgeAtomicDefectDuality

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- One coherent obstruction packet seen simultaneously in classical
cohomology, the completed limitless fibered dual, and the entire graded
geometric-program cosmology. -/
structure OmniversalSeparatorGhost
    (G : GeometricCycleClassSpine V H) where
  weight : Nat
  sheet : ClassicalHodgeBasisIndex V H weight
  separator : BasisAtomicSeparator V H weight sheet
  ghost : FiberedCompletedAddress V H :=
    separatorFiberedProbe (V := V) (H := H) weight separator.detector
  ghost_ne_zero : ghost ≠ 0
  ghost_detects_sheet :
    fiberedPairing
      (fiberedWeightCoordinates V H weight
        (classicalHodgeBasis V H weight sheet)) ghost ≠ 0
  kills_all_native_programs :
    ∀ p : Nat,
    ∀ P : GradedGeometricProgram V p weight,
    ∀ Z : codimensionCycles V.X p,
      separator.detector
        (P.cohomologyEval G (H.cycleClass p Z)) = 0
  backward_atomic :
    ∀ p : Nat,
    ∀ P : GradedGeometricProgram V p weight,
      AnnihilatesPointCycleClasses p (H.cycleClass p)
        (pullbackDetector G P separator.detector)

/-- Every microscopic separator canonically upgrades to the omniversal ghost
packet. -/
noncomputable def BasisAtomicSeparator.toOmniversalGhost
    (G : GeometricCycleClassSpine V H)
    {p : Nat}
    {i : ClassicalHodgeBasisIndex V H p}
    (S : BasisAtomicSeparator V H p i) :
    OmniversalSeparatorGhost G where
  weight := p
  sheet := i
  separator := S
  ghost := separatorFiberedProbe (V := V) (H := H) p S.detector
  ghost_ne_zero := basisSeparator_ghost_ne_zero S
  ghost_detects_sheet := basisSeparator_ghost_detects_sheet S
  kills_all_native_programs := by
    intro q P Z
    exact basisSeparator_kills_every_program_cycle G P S Z
  backward_atomic := by
    intro q P
    exact basisSeparator_pullback_annihilates_atoms G P S

/-- **FAILURE = EXISTENCE OF AN OMNIVERSAL GEOMETRIC-ORBIT GHOST.**
The forward implication constructs the full obstruction packet.  Conversely,
its stored basis separator is already a witness that Stage-2G fails. -/
theorem not_hodge_iff_nonempty_omniversalSeparatorGhost
    (G : GeometricCycleClassSpine V H) :
    ¬ BigradedBettiHodgeStatement V H ↔
      Nonempty (OmniversalSeparatorGhost G) := by
  constructor
  · intro hnot
    rw [not_bigradedBettiHodgeStatement_iff_exists_basis_separator V H] at hnot
    rcases hnot with ⟨p,i,⟨S⟩⟩
    exact ⟨S.toOmniversalGhost G⟩
  · rintro ⟨E⟩ hHodge
    have hnone :=
      (bigradedBettiHodgeStatement_iff_no_basis_separator V H).mp
        hHodge E.weight E.sheet
    exact isEmpty_iff.mp hnone E.separator

/-- Exact positive form: eliminating these omniversal ghosts is equivalent to
closing the genuine Stage-2G Hodge statement. -/
theorem hodge_iff_no_omniversalSeparatorGhost
    (G : GeometricCycleClassSpine V H) :
    BigradedBettiHodgeStatement V H ↔
      IsEmpty (OmniversalSeparatorGhost G) := by
  constructor
  · intro h
    refine ⟨?_⟩
    intro E
    have hnone :=
      (bigradedBettiHodgeStatement_iff_no_basis_separator V H).mp
        h E.weight E.sheet
    exact isEmpty_iff.mp hnone E.separator
  · intro hnone
    by_contra hnot
    have hne := (not_hodge_iff_nonempty_omniversalSeparatorGhost G).mp hnot
    exact isEmpty_iff.mp hnone (Classical.choice hne)

/-- Origin form of the ghost law: the obstruction is orthogonal to every
canonical-origin program state. -/
theorem omniversalGhost_kills_origin_orbit
    {G : GeometricCycleClassSpine V H}
    (E : OmniversalSeparatorGhost G)
    (P : GradedGeometricProgram V 0 E.weight) :
    E.separator.detector
      (P.cohomologyEval G (geometricOriginClass V H)) = 0 := by
  exact E.kills_all_native_programs 0 P
    (GSTClassicalHodgeCodimensionZeroFundamentalCycle.codimensionZeroFundamentalCycle V)

#check OmniversalSeparatorGhost
#check BasisAtomicSeparator.toOmniversalGhost
#check not_hodge_iff_nonempty_omniversalSeparatorGhost
#check hodge_iff_no_omniversalSeparatorGhost
#check omniversalGhost_kills_origin_orbit

#print axioms not_hodge_iff_nonempty_omniversalSeparatorGhost
#print axioms hodge_iff_no_omniversalSeparatorGhost
#print axioms omniversalGhost_kills_origin_orbit

end GSTClassicalHodgeOmniversalSeparatorGhostCrown
