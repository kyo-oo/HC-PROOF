import GSTClassicalHodgeFiniteClosedCorrespondenceOperator
import GSTClassicalHodgeTransformedEscapeTerminalObstruction

/-!
# GST CLASSICAL HODGE — FINITE CORRESPONDENCE ESCAPE OBSTRUCTION

The transformed GST escape can now be tested against genuine closed
correspondences, not merely words in self-maps.

On a smooth projective carrier every native cycle has a finite point normal
form.  The preceding module therefore promotes any finite closed
correspondence in X × X to an actual rational-linear native cycle operator.

For one limitless cosmic escape E, choose one actual native cycle representing
its already-algebraic source state.  If any finite closed correspondence sends
that source cycle to a cycle whose genuine Betti class is the transformed GST
escape image, the escape image is algebraic by construction — contradiction.

Thus a Hodge counterexample transformed into the GST cosmology forbids not only
projective self-map words but every finite closed correspondence from realizing
the selected source-to-target motion on that single source state.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeFiniteCorrespondenceEscapeObstruction

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeLimitlessCosmicMatrixUnits
open GSTClassicalHodgeLimitlessTwoSlotFailureDichotomy
open GSTClassicalHodgeFiniteClosedCorrespondence
open GSTClassicalHodgeFiniteClosedCorrespondenceOperator
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeMinimalPrimitiveSeparatorGhost
open GSTClassicalHodgeLocalSeedBareLefschetzExtinction
open GSTClassicalHodgeTransformedEscapeTerminalObstruction

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- The escape source already lies in the actual algebraic Hodge fiber, hence
has a genuine native codimension-p representative. -/
noncomputable def escapeSourceCycle
    (E : LimitlessCosmicEscape (V := V) (H := H) (p := p)) :
    codimensionCycles V.X p := by
  have hrange : E.alpha.1 ∈ LinearMap.range (H.cycleClass p) := by
    rw [smoothProjective_cycleClass_range_eq_atomic_span V H p]
    exact E.alpha_algebraic
  exact Classical.choose hrange

/-- Exact cycle-class receipt for the chosen native source representative. -/
theorem escapeSourceCycle_spec
    (E : LimitlessCosmicEscape (V := V) (H := H) (p := p)) :
    H.cycleClass p (escapeSourceCycle E) = E.alpha.1 := by
  have hrange : E.alpha.1 ∈ LinearMap.range (H.cycleClass p) := by
    rw [smoothProjective_cycleClass_range_eq_atomic_span V H p]
    exact E.alpha_algebraic
  exact Classical.choose_spec hrange

/-- Absolutely local finite-correspondence realization datum: one actual closed
correspondence and equality only on the escape's one chosen native source
cycle. -/
structure FiniteCorrespondenceEscapeRealization
    (E : LimitlessCosmicEscape (V := V) (H := H) (p := p)) where
  correspondence : FiniteClosedCorrespondence V
  source_action :
    H.cycleClass p
        (nativeCorrespondenceOperator correspondence p (escapeSourceCycle E)) =
      (liftCosmicWindowOperator
        (pairBasisIndex E.source E.target)
        (rationalCosmicMatrixUnit sourceSlot.1 targetSlot.1)
        E.alpha).1

/-- **NO FINITE CLOSED CORRESPONDENCE CAN REALIZE AN ESCAPE.**
The native output of a genuine correspondence is automatically in the actual
cycle-class range, contradicting the defining nonalgebraicity of the cosmic
escape image. -/
theorem no_finiteCorrespondenceEscapeRealization
    (E : LimitlessCosmicEscape (V := V) (H := H) (p := p)) :
    IsEmpty (FiniteCorrespondenceEscapeRealization E) := by
  refine ⟨?_⟩
  intro R
  have houtRange :
      (liftCosmicWindowOperator
        (pairBasisIndex E.source E.target)
        (rationalCosmicMatrixUnit sourceSlot.1 targetSlot.1)
        E.alpha).1 ∈ LinearMap.range (H.cycleClass p) := by
    exact ⟨
      nativeCorrespondenceOperator R.correspondence p (escapeSourceCycle E),
      R.source_action⟩
  have houtAlg :
      liftCosmicWindowOperator
          (pairBasisIndex E.source E.target)
          (rationalCosmicMatrixUnit sourceSlot.1 targetSlot.1)
          E.alpha ∈
        AlgebraicFiber (V := V) (H := H) (p := p) := by
    rw [mem_AlgebraicHodgeSubspace_iff]
    rw [← smoothProjective_cycleClass_range_eq_atomic_span V H p]
    exact houtRange
  exact E.escapes houtAlg

/-- Minimal-ghost specialization: the exact transformed escape selected by a
seeded minimal primitive ghost cannot be realized by any finite closed
correspondence on its own source state. -/
theorem transformedEscape_has_no_finiteCorrespondence
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    (S : MinimalGhostLocalSeed G M) :
    IsEmpty
      (FiniteCorrespondenceEscapeRealization
        (transformedEscape G M S)) :=
  no_finiteCorrespondenceEscapeRealization (transformedEscape G M S)

#check escapeSourceCycle
#check escapeSourceCycle_spec
#check FiniteCorrespondenceEscapeRealization
#check no_finiteCorrespondenceEscapeRealization
#check transformedEscape_has_no_finiteCorrespondence

#print axioms escapeSourceCycle_spec
#print axioms no_finiteCorrespondenceEscapeRealization
#print axioms transformedEscape_has_no_finiteCorrespondence

end GSTClassicalHodgeFiniteCorrespondenceEscapeObstruction
