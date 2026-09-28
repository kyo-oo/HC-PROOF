import GSTClassicalHodgeFiniteClosedCorrespondenceOperator
import GSTClassicalHodgeOmniversalSeparatorGhostCrown

/-!
# GST CLASSICAL HODGE — FINITE-CORRESPONDENCE SEPARATOR COLLISION

A hypothetical Hodge failure has already been transformed into an omniversal
separator ghost.  The ghost annihilates every genuine cycle class in its
obstructed weight.  A finite closed correspondence, independently of any
cohomological or Hodge realization, produces an actual native algebraic cycle
from every native source cycle.  Therefore every such correspondence output is
also invisible to the separator.

This sharpens the final geometric target.  We do not need a correspondence to
realize an exact matrix unit, a whole-fiber GST word, or even a prescribed
Hodge basis vector.  To destroy an omniversal ghost it is enough to construct
one genuine finite correspondence and one genuine native source cycle whose
output has nonzero separator reading.

Equivalently, a surviving Hodge failure forces a total finite-correspondence
blackout: one nonzero separator annihilates every output of every finite closed
correspondence at the obstructed weight.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeFiniteCorrespondenceSeparatorCollision

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeAtomicAnnihilator
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeFiniteClosedCorrespondence
open GSTClassicalHodgeFiniteClosedCorrespondenceOperator
open GSTClassicalHodgeOmniversalSeparatorGhostCrown

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Every output of every genuine finite closed correspondence is annihilated
by an omniversal separator at its obstructed weight, simply because that output
is still an actual native algebraic cycle. -/
theorem omniversalGhost_kills_finiteCorrespondence_output
    (G : GeometricCycleClassSpine V H)
    (E : OmniversalSeparatorGhost G)
    (K : FiniteClosedCorrespondence V)
    (Z : codimensionCycles V.X E.weight) :
    E.separator.detector
      (H.cycleClass E.weight
        (nativeCorrespondenceOperator K E.weight Z)) = 0 := by
  have hker :
      pointCycleClassSpan E.weight (H.cycleClass E.weight) ≤
        LinearMap.ker E.separator.detector :=
    (annihilatesPointCycles_iff_atomicSpan_le_ker
      E.weight (H.cycleClass E.weight) E.separator.detector).mp
      E.separator.annihilates_atoms
  apply hker
  rw [← smoothProjective_cycleClass_range_eq_atomic_span V H E.weight]
  exact ⟨nativeCorrespondenceOperator K E.weight Z, rfl⟩

/-- Minimal geometric collision datum.  It asks for no exact target basis
identity: only one actual finite-correspondence output seen nontrivially by the
ghost detector. -/
structure FiniteCorrespondenceGhostDetection
    (G : GeometricCycleClassSpine V H)
    (E : OmniversalSeparatorGhost G) where
  correspondence : FiniteClosedCorrespondence V
  source : codimensionCycles V.X E.weight
  detected :
    E.separator.detector
      (H.cycleClass E.weight
        (nativeCorrespondenceOperator correspondence E.weight source)) ≠ 0

/-- An omniversal ghost admits no finite-correspondence detection datum. -/
theorem no_finiteCorrespondenceGhostDetection
    (G : GeometricCycleClassSpine V H)
    (E : OmniversalSeparatorGhost G) :
    IsEmpty (FiniteCorrespondenceGhostDetection G E) := by
  refine ⟨?_⟩
  intro D
  exact D.detected
    (omniversalGhost_kills_finiteCorrespondence_output
      G E D.correspondence D.source)

/-- The exact transformed obstruction imposed by a surviving ghost. -/
def FiniteCorrespondenceBlackout
    (G : GeometricCycleClassSpine V H)
    (E : OmniversalSeparatorGhost G) : Prop :=
  ∀ K : FiniteClosedCorrespondence V,
  ∀ Z : codimensionCycles V.X E.weight,
    E.separator.detector
      (H.cycleClass E.weight
        (nativeCorrespondenceOperator K E.weight Z)) = 0

/-- Every omniversal ghost automatically carries the total finite-correspondence
blackout property. -/
theorem omniversalGhost_finiteCorrespondenceBlackout
    (G : GeometricCycleClassSpine V H)
    (E : OmniversalSeparatorGhost G) :
    FiniteCorrespondenceBlackout G E := by
  intro K Z
  exact omniversalGhost_kills_finiteCorrespondence_output G E K Z

/-- **FAILURE -> TOTAL FINITE-CORRESPONDENCE BLACKOUT.**
A genuine Hodge failure therefore transforms into one nonzero omniversal ghost
which annihilates the output of every genuine finite closed correspondence on
every native source cycle at its obstructed weight. -/
theorem failure_yields_finiteCorrespondence_blackout
    (G : GeometricCycleClassSpine V H)
    (hnot : ¬ BigradedBettiHodgeStatement V H) :
    ∃ E : OmniversalSeparatorGhost G,
      FiniteCorrespondenceBlackout G E := by
  let E : OmniversalSeparatorGhost G :=
    Classical.choice
      ((not_hodge_iff_nonempty_omniversalSeparatorGhost G).mp hnot)
  exact ⟨E, omniversalGhost_finiteCorrespondenceBlackout G E⟩

/-- **SEPARATOR-LEVEL CORRESPONDENCE CROWN.**
To close Hodge it is enough that every possible omniversal ghost is detected by
one genuine finite correspondence output.  This requirement is strictly weaker
than asking for an exact GST matrix unit or exact target-basis realization. -/
theorem bigradedBettiHodge_of_finiteCorrespondenceGhostDetection
    (G : GeometricCycleClassSpine V H)
    (detect : ∀ E : OmniversalSeparatorGhost G,
      Nonempty (FiniteCorrespondenceGhostDetection G E)) :
    BigradedBettiHodgeStatement V H := by
  by_contra hnot
  let E : OmniversalSeparatorGhost G :=
    Classical.choice
      ((not_hodge_iff_nonempty_omniversalSeparatorGhost G).mp hnot)
  exact isEmpty_iff.mp (no_finiteCorrespondenceGhostDetection G E)
    (Classical.choice (detect E))

#check omniversalGhost_kills_finiteCorrespondence_output
#check FiniteCorrespondenceGhostDetection
#check no_finiteCorrespondenceGhostDetection
#check FiniteCorrespondenceBlackout
#check omniversalGhost_finiteCorrespondenceBlackout
#check failure_yields_finiteCorrespondence_blackout
#check bigradedBettiHodge_of_finiteCorrespondenceGhostDetection

#print axioms omniversalGhost_kills_finiteCorrespondence_output
#print axioms no_finiteCorrespondenceGhostDetection
#print axioms failure_yields_finiteCorrespondence_blackout
#print axioms bigradedBettiHodge_of_finiteCorrespondenceGhostDetection

end GSTClassicalHodgeFiniteCorrespondenceSeparatorCollision
