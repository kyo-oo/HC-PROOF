import GSTClassicalHodgeTransformedEscapeTerminalObstruction
import GSTClassicalHodgeProjectiveWordOrbit
import GSTClassicalHodgeLimitlessTwoSlotFailureDichotomy

/-!
# GST CLASSICAL HODGE — SINGLE PROJECTIVE WORD ESCAPE OBSTRUCTION

The transformed limitless escape does not require a global projective arsenal,
all ordered basis pairs, or even a decomposition into the code/Lefschetz
primitive generators.

Because the escape source is already an actual algebraic Hodge state, exact
cycle-class naturality of one finite projective operator word is enough.  If
that word acts on the escape source as the one limitless GST matrix-unit motion
selected by the failure, then its native-cycle image gives an algebraic
representative for the escaped state.  This contradicts the escape definition.

Hence a seeded minimal Hodge counterexample selects one concrete source state,
one concrete target sheet and one concrete GST motion such that NO finite word
built from genuine projective self-transports can realize that motion on that
single source state.

This is strictly weaker than `ProjectiveTwoGenerator`: no behavior is required
on any other Hodge vector and no primitive factorization is assumed.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeSingleProjectiveWordEscapeObstruction

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeConcreteFailureDichotomy
open GSTClassicalHodgeLimitlessCosmicMatrixUnits
open GSTClassicalHodgeLimitlessTwoSlotFailureDichotomy
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeProjectiveWordOrbit
open GSTClassicalHodgeMinimalPrimitiveSeparatorGhost
open GSTClassicalHodgeLocalSeedBareLefschetzExtinction
open GSTClassicalHodgeTransformedEscapeTerminalObstruction

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- The absolutely minimal projective realization datum for one transformed
escape: one genuine projective word and one equality on the escape's own
already-algebraic source state. -/
structure ProjectiveWordEscapeRealization
    (G : GeometricCycleClassSpine V H)
    (E : LimitlessCosmicEscape (V := V) (H := H) (p := p)) where
  word : ProjectiveOperatorWord V p
  source_action :
    (word.operatorPair G).cohomologyOperator E.alpha.1 =
      (liftCosmicWindowOperator
        (pairBasisIndex E.source E.target)
        (rationalCosmicMatrixUnit sourceSlot.1 targetSlot.1)
        E.alpha).1

/-- **ONE PROJECTIVE WORD CANNOT REALIZE THE ESCAPE.**
Exact cycle-class naturality sends the already-algebraic escape source to an
actual native-cycle class, whereas the transformed GST escape says the same
state lies outside the algebraic Hodge fiber. -/
theorem no_projectiveWordEscapeRealization
    (G : GeometricCycleClassSpine V H)
    (E : LimitlessCosmicEscape (V := V) (H := H) (p := p)) :
    IsEmpty (ProjectiveWordEscapeRealization G E) := by
  refine ⟨?_⟩
  intro R
  have hrange : E.alpha.1 ∈ LinearMap.range (H.cycleClass p) := by
    rw [smoothProjective_cycleClass_range_eq_atomic_span V H p]
    exact E.alpha_algebraic
  rcases hrange with ⟨Z, hZ⟩
  have hnat := R.word.cycleClass_eval G Z
  rw [hZ, R.source_action] at hnat
  have hout :
      liftCosmicWindowOperator
          (pairBasisIndex E.source E.target)
          (rationalCosmicMatrixUnit sourceSlot.1 targetSlot.1)
          E.alpha ∈
        AlgebraicFiber (V := V) (H := H) (p := p) := by
    rw [mem_AlgebraicHodgeSubspace_iff]
    rw [← smoothProjective_cycleClass_range_eq_atomic_span V H p]
    exact ⟨R.word.eval Z, hnat⟩
  exact E.escapes hout

/-- Pointwise contradiction form. -/
theorem projectiveWordEscapeRealization_false
    (G : GeometricCycleClassSpine V H)
    (E : LimitlessCosmicEscape (V := V) (H := H) (p := p))
    (R : ProjectiveWordEscapeRealization G E) : False :=
  (no_projectiveWordEscapeRealization G E).false R

/-- **TRANSFORMED MINIMAL-GHOST TERMINAL WORD OBSTRUCTION.**
The exact escape selected from a seeded minimal primitive ghost forbids even a
single projective word realizing its GST motion on its own source state. -/
theorem transformedEscape_has_no_projectiveWord
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    (S : MinimalGhostLocalSeed G M) :
    IsEmpty
      (ProjectiveWordEscapeRealization G
        (transformedEscape G M S)) :=
  no_projectiveWordEscapeRealization G (transformedEscape G M S)

#check ProjectiveWordEscapeRealization
#check no_projectiveWordEscapeRealization
#check projectiveWordEscapeRealization_false
#check transformedEscape_has_no_projectiveWord

#print axioms no_projectiveWordEscapeRealization
#print axioms projectiveWordEscapeRealization_false
#print axioms transformedEscape_has_no_projectiveWord

end GSTClassicalHodgeSingleProjectiveWordEscapeObstruction
