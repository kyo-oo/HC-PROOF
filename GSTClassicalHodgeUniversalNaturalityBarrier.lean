import GSTClassicalHodgeCycleOperatorNaturality
import GSTClassicalHodgeOmniversalSeparatorGhostCrown
import GSTClassicalHodgeGhostSpineCosmicLeak

/-!
# GST CLASSICAL HODGE — UNIVERSAL CYCLE-NATURALITY BARRIER

The projective and finite-correspondence blackout theorems are instances of a
more fundamental fact which should be visible explicitly.

A cycle-class-natural operator sends the class of an actual algebraic cycle to
the class of another actual algebraic cycle.  An omniversal separator ghost
annihilates every such class.  Therefore no cycle-natural operator, regardless
of how rich its geometric construction is, can carry an algebraic source to a
state detected nontrivially by the ghost.

This proves that the remaining Hodge attack cannot be completed by merely
externalizing a GST sheet-changing matrix unit as a natural algebraic-cycle
operator.  Under a counterexample, such an externalization is impossible for
formal reasons.  The separator must instead be destroyed by an independent
cohomological/geometric computation (pairing, cup product, polarization,
intersection theory, etc.) which shows that no such annihilator can exist.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeUniversalNaturalityBarrier

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeAtomicAnnihilator
open GSTClassicalHodgeCycleOperatorNaturality
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeOmniversalSeparatorGhostCrown
open GSTClassicalHodgeSynchronizedDefectOrbit
open GSTClassicalHodgeGhostSpineCosmicLeak

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Every cycle-natural cohomological image of an actual algebraic class is
annihilated by an omniversal separator ghost. -/
theorem ghost_kills_every_cycleNatural_image
    (G : GeometricCycleClassSpine V H)
    (E : OmniversalSeparatorGhost G)
    (A : CycleClassOperatorPair V H E.weight)
    (Z : codimensionCycles V.X E.weight) :
    E.separator.detector
      (A.cohomologyOperator (H.cycleClass E.weight Z)) = 0 := by
  have hnat := A.cycleClass_cycleOperator Z
  have hrange :
      H.cycleClass E.weight (A.cycleOperator Z) ∈
        LinearMap.range (H.cycleClass E.weight) :=
    ⟨A.cycleOperator Z, rfl⟩
  have hatomic :
      H.cycleClass E.weight (A.cycleOperator Z) ∈
        pointCycleClassSpan E.weight (H.cycleClass E.weight) := by
    rw [← smoothProjective_cycleClass_range_eq_atomic_span V H E.weight]
    exact hrange
  have hker :
      pointCycleClassSpan E.weight (H.cycleClass E.weight) ≤
        LinearMap.ker E.separator.detector :=
    (annihilatesPointCycles_iff_atomicSpan_le_ker
      E.weight (H.cycleClass E.weight) E.separator.detector).mp
      E.separator.annihilates_atoms
  have hz := hker hatomic
  rw [LinearMap.mem_ker] at hz
  rw [← hnat]
  exact hz

/-- Specialization to the canonical nonzero algebraic spine source selected at
the ghost weight. -/
theorem ghost_kills_every_cycleNatural_spine_image
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (E : OmniversalSeparatorGhost G)
    (A : CycleClassOperatorPair V H E.weight) :
    E.separator.detector
      (A.cohomologyOperator (ghostSpineSeed G M E).hodge.1) = 0 := by
  rw [← (ghostSpineSeed G M E).class_eq]
  exact ghost_kills_every_cycleNatural_image
    G E A (ghostSpineSeed G M E).cycle

/-- No natural operator can realize any prescribed detector-visible target on
an algebraic source.  This is the abstract form of all projective/correspondence
realization barriers. -/
theorem no_cycleNatural_visible_target
    (G : GeometricCycleClassSpine V H)
    (E : OmniversalSeparatorGhost G)
    (A : CycleClassOperatorPair V H E.weight)
    (Z : codimensionCycles V.X E.weight)
    (beta : RationalSingularCohomology H.analytification (2 * E.weight))
    (hbeta : E.separator.detector beta ≠ 0)
    (haction : A.cohomologyOperator (H.cycleClass E.weight Z) = beta) :
    False := by
  apply hbeta
  rw [← haction]
  exact ghost_kills_every_cycleNatural_image G E A Z

/-- In particular, the nonzero GST ghost leak from the canonical spine cannot
be the action of any genuine cycle-class-natural operator while the ghost
survives. -/
theorem canonicalGhostLeak_not_cycleNatural
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (E : OmniversalSeparatorGhost G)
    (A : CycleClassOperatorPair V H E.weight)
    (haction :
      A.cohomologyOperator (ghostSpineSeed G M E).hodge.1 =
        canonicalGhostLeak G M E) :
    False := by
  have hvisible := ghostLeak_detected_nonzero G M E
  exact no_cycleNatural_visible_target
    G E A (ghostSpineSeed G M E).cycle
      (canonicalGhostLeak G M E) hvisible
      (by simpa [(ghostSpineSeed G M E).class_eq] using haction)

#check ghost_kills_every_cycleNatural_image
#check ghost_kills_every_cycleNatural_spine_image
#check no_cycleNatural_visible_target
#check canonicalGhostLeak_not_cycleNatural

#print axioms ghost_kills_every_cycleNatural_image
#print axioms ghost_kills_every_cycleNatural_spine_image
#print axioms no_cycleNatural_visible_target
#print axioms canonicalGhostLeak_not_cycleNatural

end GSTClassicalHodgeUniversalNaturalityBarrier
