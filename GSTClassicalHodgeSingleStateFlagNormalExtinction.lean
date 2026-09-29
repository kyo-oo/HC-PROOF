import GSTClassicalHodgePrincipalCutFlagNormalGeometryFirst
import GSTClassicalHodgeSingleStateBareLefschetzExtinction

/-!
# GST CLASSICAL HODGE — SINGLE-STATE FLAG-NORMAL EXTINCTION

The single-state bare-Lefschetz theorem shows that a hypothetical minimal Hodge
ghost is killed as soon as one already-algebraic local seed has algebraic image
under the relevant two-slot `L^2` motion.

The principal-cut flag-normal construction is stronger than what that
contradiction needs: it supplies a genuine same-weight cycle/cohomology pair.
Hence its cohomology action sends every actual cycle class to an actual cycle
class automatically.

This file isolates the resulting minimal geometric obligation.  We do NOT ask
that the flag normal realize `L^2` on the whole Hodge fiber, nor on all point
cycles.  For each hypothetical first-failure ghost it is enough that one
geometric flag normal agree with bare `L^2` on the single local algebraic seed
used by the contradiction.

Thus the remaining comparison is one state, one source, one target ghost
sheet.  No global two-generator externalization, arbitrary projective self-map,
coefficient projection formula, or global native point-lift law is assumed.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeSingleStateFlagNormalExtinction

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeCrossWeightNativePropagation
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeMinimalPrimitiveSeparatorGhost
open GSTClassicalHodgeLocalSeedBareLefschetzExtinction
open GSTClassicalHodgeSingleStateBareLefschetzExtinction
open GSTClassicalHodgePrincipalCutFlagCorrespondenceDescent
open GSTClassicalHodgePrincipalCutFlagCorrespondenceDescent.PrincipalCutFlagBiFiniteRealization
open GSTClassicalHodgePrincipalCutFlagNormalGeometryFirst
open GSTClassicalHodgeGradedFiniteClosedCorrespondence

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- One geometric flag normal matching the bare GST `L^2` operator only on the
single local seed used by the minimal-ghost contradiction. -/
structure SingleStateFlagNormalLefschetzRealization
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    (S : MinimalGhostLocalSeed G M) where
  sigma : Finset (CodimensionPoint V.X M.weight)
  incidence : PrincipalCutFlagBiFiniteRealization V M.weight sigma
  transpose_naturality :
    GradedCorrespondencePointNaturality
      incidence.correspondence.transpose H (M.weight + 1) M.weight
  matches_seed :
    (principalCutFlagNormalPair
      (G := G) incidence transpose_naturality).cohomologyOperator S.source.1 =
      ambientTwoStepLefschetz S.sourceIndex M.sheet S.source.1

namespace SingleStateFlagNormalLefschetzRealization

/-- The flag-normal image of the local source lies in the actual atomic
algebraic span because the source itself is algebraic and the flag normal has
an exact cycle-class square. -/
theorem flag_image_algebraic
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    (S : MinimalGhostLocalSeed G M)
    (F : SingleStateFlagNormalLefschetzRealization G M S) :
    (principalCutFlagNormalPair
      (G := G) F.incidence F.transpose_naturality).cohomologyOperator
        S.source.1 ∈
      pointCycleClassSpan M.weight (H.cycleClass M.weight) := by
  have hsourceRange :
      S.source.1 ∈ LinearMap.range (H.cycleClass M.weight) := by
    have hsourceAtomic :
        S.source.1 ∈ pointCycleClassSpan M.weight (H.cycleClass M.weight) :=
      S.source_algebraic
    rwa [← smoothProjective_cycleClass_range_eq_atomic_span
      V H M.weight] at hsourceAtomic
  rcases hsourceRange with ⟨Z, hZ⟩
  let T : GradedCycleClassOperatorPair V H M.weight M.weight :=
    principalCutFlagNormalPair
      (G := G) F.incidence F.transpose_naturality
  have htargetRange :
      T.cohomologyOperator S.source.1 ∈
        LinearMap.range (H.cycleClass M.weight) := by
    refine ⟨T.cycleOperator Z, ?_⟩
    rw [T.cycleClass_natural, hZ]
  have htargetAtomic :
      T.cohomologyOperator S.source.1 ∈
        pointCycleClassSpan M.weight (H.cycleClass M.weight) := by
    rwa [← smoothProjective_cycleClass_range_eq_atomic_span
      V H M.weight]
  exact htargetAtomic

/-- **ONE GEOMETRIC FLAG NORMAL KILLS THE MINIMAL GHOST.**
The only comparison used is `matches_seed`, an equality on one already
algebraic state. -/
theorem minimalGhost_false
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    (S : MinimalGhostLocalSeed G M)
    (F : SingleStateFlagNormalLefschetzRealization G M S) : False := by
  have hflag := F.flag_image_algebraic G M S
  have himage :
      ambientTwoStepLefschetz S.sourceIndex M.sheet S.source.1 ∈
        pointCycleClassSpan M.weight (H.cycleClass M.weight) := by
    rw [← F.matches_seed]
    exact hflag
  exact minimalGhost_false_of_localSeed_bareLefschetz_image_algebraic
    G M S himage

end SingleStateFlagNormalLefschetzRealization

/-- **SINGLE-STATE FLAG-NORMAL HODGE CRITERION.**
For every hypothetical minimal ghost, choose one nonzero algebraic local seed
and one genuine principal-cut flag normal whose cohomology action agrees with
bare two-step GST Lefschetz on that seed alone.  This already proves the
bigraded Betti Hodge statement. -/
theorem bigradedBettiHodge_of_singleStateFlagNormals
    (G : GeometricCycleClassSpine V H)
    (seed : ∀ M : MinimalPrimitiveGhost G,
      Nonempty (MinimalGhostLocalSeed G M))
    (flag : ∀ M : MinimalPrimitiveGhost G,
      ∀ S : MinimalGhostLocalSeed G M,
        Nonempty (SingleStateFlagNormalLefschetzRealization G M S)) :
    BigradedBettiHodgeStatement V H := by
  by_contra hnot
  let M : MinimalPrimitiveGhost G := minimalPrimitiveGhostOfFailure G hnot
  let S : MinimalGhostLocalSeed G M := (seed M).some
  exact (flag M S).some.minimalGhost_false G M S

#check SingleStateFlagNormalLefschetzRealization
#check SingleStateFlagNormalLefschetzRealization.flag_image_algebraic
#check SingleStateFlagNormalLefschetzRealization.minimalGhost_false
#check bigradedBettiHodge_of_singleStateFlagNormals

#print axioms SingleStateFlagNormalLefschetzRealization.flag_image_algebraic
#print axioms SingleStateFlagNormalLefschetzRealization.minimalGhost_false
#print axioms bigradedBettiHodge_of_singleStateFlagNormals

end GSTClassicalHodgeSingleStateFlagNormalExtinction
