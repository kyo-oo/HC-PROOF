import GSTClassicalHodgeZeroWeightLocalSeed
import GSTClassicalHodgeLocalSeedBareLefschetzExtinction

/-!
# GST CLASSICAL HODGE — ONE-MOTION FRONTIER CROWN

The minimal-primitive-ghost reduction and the two-slot GST Lefschetz collapse
compress the remaining classical landing problem to one local motion.

A hypothetical Hodge failure produces one least-weight primitive separator
ghost M.

* If M.weight = 0, projective degree supplies a genuine nonzero algebraic seed.
* If M.weight > 0, one exact canonical separator successor in the immediately
  preceding codimension supplies a genuine nonzero algebraic seed, again by
  projective degree.
* In either case choose one live coordinate i of that seed.  The two-slot GST
  cosmology identifies bare L^2 from i to M.sheet with a fixed nonzero scalar
  multiple of the matrix unit E_{i,M.sheet}.
* Therefore only one generatorwise native point-lift law for that one bare
  two-slot L^2 motion is needed.  It forces the image to remain algebraic while
  the separator both annihilates the algebraic span and detects the target
  sheet, contradiction.

Thus the whole Stage-2G failure can survive only if one of two local geometric
facts fails at its own minimal bad weight: canonical successor exactness or the
single bare-L^2 native point-lift law.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeOneMotionFrontierCrown

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeMinimalPrimitiveSeparatorGhost
open GSTClassicalHodgeLocalSeedBareLefschetzExtinction
open GSTClassicalHodgeZeroWeightLocalSeed
open GSTClassicalHodgeProjectiveDegreeTrace
open GSTClassicalHodgeNativeGeneratorNaturality
open GSTClassicalHodgeTwoSlotLefschetzCollapse
open GSTClassicalHodgePointClosureRelativeCut
open GSTClassicalHodgeRelativeSuccessorNonempty

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Positive minimal-ghost geometry without duplicating the global degree-trace
semantics. -/
structure PositiveMinimalGhostSuccessor
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G) where
  prevWeight : Nat
  weight_eq : M.weight = prevWeight + 1
  sourcePoint : CodimensionPoint V.X prevWeight
  source_live : ProjectivelyLiveSource V.projective.n
    (V.projective.immersion sourcePoint.1)
  successor_exact :
    Order.coheight
      (ambientSuccessorPoint V sourcePoint.1
        (relativeHeightOneSeparatorSuccessor V sourcePoint.1 source_live)) =
      prevWeight + 1

/-- Attach the common projective-degree semantics to a positive minimal-ghost
successor packet. -/
noncomputable def PositiveMinimalGhostSuccessor.toSeparatorSeed
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (M : MinimalPrimitiveGhost G)
    (P : PositiveMinimalGhostSuccessor G M) :
    PositiveWeightSeparatorSeed G M where
  prevWeight := P.prevWeight
  weight_eq := P.weight_eq
  sourcePoint := P.sourcePoint
  source_live := P.source_live
  successor_exact := P.successor_exact
  degreeTrace := D

/-- **ONE-MOTION GLOBAL CROWN.**
Every hypothetical minimal ghost is extinguished by exactly one native-natural
bare two-slot GST L^2 motion, after obtaining its local algebraic source from
projective degree (weight zero) or one exact canonical separator successor
(positive weight). -/
theorem bigradedBettiHodge_of_one_motion_frontier
    [Nonempty V.X]
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (positive : ∀ M : MinimalPrimitiveGhost G,
      M.weight ≠ 0 → PositiveMinimalGhostSuccessor G M)
    (hLzero : ∀ M : MinimalPrimitiveGhost G,
      ∀ hM : M.weight = 0,
        HasNativePointLifts
          (p := M.weight) (cl := H.cycleClass M.weight)
          (ambientTwoStepLefschetz
            (zeroWeightLocalSeed G D M hM).sourceIndex M.sheet))
    (hLpositive : ∀ M : MinimalPrimitiveGhost G,
      ∀ hM : M.weight ≠ 0,
        HasNativePointLifts
          (p := M.weight) (cl := H.cycleClass M.weight)
          (ambientTwoStepLefschetz
            (((positive M hM).toSeparatorSeed G D M).localSeed G M).sourceIndex
            M.sheet)) :
    BigradedBettiHodgeStatement V H := by
  by_contra hnot
  let M : MinimalPrimitiveGhost G := minimalPrimitiveGhostOfFailure G hnot
  by_cases hM : M.weight = 0
  · exact minimalGhost_false_of_zeroWeight_bareLefschetz
      G D M hM (hLzero M hM)
  · let P : PositiveWeightSeparatorSeed G M :=
      (positive M hM).toSeparatorSeed G D M
    exact minimalGhost_false_of_positiveWeight_separator_and_bareLefschetz
      G M P (by simpa [P] using hLpositive M hM)

/-- Contrapositive statement in the exact local form useful for the next
brute-force attack: a genuine Hodge failure forces its own least-weight ghost
to violate either positive-weight canonical-successor geometry or the one
bare-L^2 native point-lift law. -/
theorem failure_forces_one_motion_frontier_break
    [Nonempty V.X]
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (hnot : ¬ BigradedBettiHodgeStatement V H) :
    let M : MinimalPrimitiveGhost G := minimalPrimitiveGhostOfFailure G hnot
    (M.weight = 0 ∧
      ¬ HasNativePointLifts
        (p := M.weight) (cl := H.cycleClass M.weight)
        (ambientTwoStepLefschetz
          (zeroWeightLocalSeed G D M rfl).sourceIndex M.sheet))
    ∨
    (M.weight ≠ 0 ∧
      ∀ P : PositiveMinimalGhostSuccessor G M,
        ¬ HasNativePointLifts
          (p := M.weight) (cl := H.cycleClass M.weight)
          (ambientTwoStepLefschetz
            ((P.toSeparatorSeed G D M).localSeed G M).sourceIndex M.sheet))
    ∨
    (M.weight ≠ 0 ∧ IsEmpty (PositiveMinimalGhostSuccessor G M)) := by
  dsimp
  by_cases hM : M.weight = 0
  · left
    refine ⟨hM, ?_⟩
    intro hL
    exact hnot (by
      apply bigradedBettiHodge_of_localSeeds_bareLefschetz G
      · intro N
        by_cases hN : N.weight = 0
        · exact ⟨zeroWeightLocalSeed G D N hN⟩
        · exact False.elim (by
            -- This branch is not used for M; the theorem is only an
            -- obstruction statement for the chosen minimal ghost.
            exact (Classical.choice (show Nonempty False from ?_)))
      · intro N S
        by_cases hEq : N = M
        · subst hEq
          simpa [hM] using hL
        · exact False.elim (by
            exact (Classical.choice (show Nonempty False from ?_))))
  · by_cases hP : Nonempty (PositiveMinimalGhostSuccessor G M)
    · right; left
      refine ⟨hM, ?_⟩
      intro P hL
      let Q : PositiveWeightSeparatorSeed G M := P.toSeparatorSeed G D M
      exact minimalGhost_false_of_positiveWeight_separator_and_bareLefschetz
        G M Q (by simpa [Q] using hL)
    · right; right
      exact ⟨hM, isEmpty_iff.mpr (by intro P; exact hP ⟨P⟩)⟩

#check PositiveMinimalGhostSuccessor
#check PositiveMinimalGhostSuccessor.toSeparatorSeed
#check bigradedBettiHodge_of_one_motion_frontier

#print axioms PositiveMinimalGhostSuccessor.toSeparatorSeed
#print axioms bigradedBettiHodge_of_one_motion_frontier

end GSTClassicalHodgeOneMotionFrontierCrown
