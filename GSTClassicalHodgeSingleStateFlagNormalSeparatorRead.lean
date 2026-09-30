import GSTClassicalHodgeSingleStateFlagNormalExtinction
import GSTClassicalHodgeSeparatorFiniteGSTPoincare

/-!
# GST CLASSICAL HODGE — SINGLE-STATE FLAG-NORMAL SEPARATOR READ

The single-state flag-normal extinction theorem still asks for equality of two
ambient cohomology vectors on one algebraic seed:

  flagNormal(source) = bareL2(source).

That is stronger than the contradiction uses.

The flag-normal image is automatically algebraic, hence the minimal atomic
separator reads it as zero.  The exact two-slot GST calculation sends the live
source coordinate to a nonzero multiple of the basis sheet detected by the
same separator, hence the separator reads the bare `L^2` image nontrivially.
Therefore it is enough to identify ONE SCALAR OBSERVABLE:

  separator(flagNormal(source)) = separator(bareL2(source)).

This file proves that reduction.  It then rewrites the right-hand side as the
canonical finite-GST Poincare top pairing already attached to the separator.
Consequently the final one-state geometry can be targeted at one finite-world
Poincare read rather than at equality of ambient cohomology states.

No Hodge-surjectivity, target basis representative, global adjoint law, matrix
unit realization, or equality of cohomology operators is assumed.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeSingleStateFlagNormalSeparatorRead

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeAtomicAnnihilator
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeMinimalPrimitiveSeparatorGhost
open GSTClassicalHodgeLocalSeedBareLefschetzExtinction
open GSTClassicalHodgeUniversalTwoSlotNativeClosure
open GSTClassicalHodgePrincipalCutFlagCorrespondenceDescent
open GSTClassicalHodgePrincipalCutFlagCorrespondenceDescent.PrincipalCutFlagBiFiniteRealization
open GSTClassicalHodgePrincipalCutFlagNormalGeometryFirst
open GSTClassicalHodgeCrossWeightNativePropagation
open GSTClassicalHodgeSeparatorFiniteGSTPoincare
open GSTClassicalHodgeLimitlessSeparatorGhost
open GSTClassicalHodgeFiniteSupportChart

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- The genuine Hodge-fiber value of the bare two-step GST Lefschetz primitive
on the one local algebraic seed. -/
noncomputable def bareTwoStepHodgeImage
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    (S : MinimalGhostLocalSeed G M) :
    ClassicalHodgeFiber V H M.weight :=
  twoSlotHodgeOperator S.sourceIndex M.sheet
    (diagonalLefschetzQ 2 2) S.source

/-- The bundled Hodge image has exactly the same ambient value as the existing
`ambientTwoStepLefschetz` extension on the local seed. -/
theorem bareTwoStepHodgeImage_val
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    (S : MinimalGhostLocalSeed G M) :
    (bareTwoStepHodgeImage G M S).1 =
      ambientTwoStepLefschetz S.sourceIndex M.sheet S.source.1 := by
  symm
  exact extendHodgeEndomorphism_on_hodge
    (V := V) (H := H)
    (twoSlotHodgeOperator S.sourceIndex M.sheet (diagonalLefschetzQ 2 2))
    S.source

/-- The minimal separator reads the bare two-step image nontrivially.  This is
the scalar form of the exact two-slot calculation. -/
theorem bareTwoStep_separator_read_ne_zero
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    (S : MinimalGhostLocalSeed G M) :
    M.separator.detector
      (ambientTwoStepLefschetz S.sourceIndex M.sheet S.source.1) ≠ 0 := by
  rw [ambientTwoStepLefschetz_on_hodge_coordinate]
  rw [LinearMap.map_smul]
  simp only [smul_eq_mul]
  exact mul_ne_zero
    (mul_ne_zero twoSlot_forwardScalar_ne_zero S.sourceCoefficient_ne_zero)
    M.separator.detects_basis

/-- Exact finite-GST Poincare form of the same nonzero bare-`L^2` separator
read. -/
theorem bareTwoStep_separator_read_eq_finiteGSTPoincare
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    (S : MinimalGhostLocalSeed G M) :
    M.separator.detector
        (ambientTwoStepLefschetz S.sourceIndex M.sheet S.source.1) =
      rationalWorldTopPairing
        (fiberedSupportWorld
          (fiberedWeightCoordinates V H M.weight
            (bareTwoStepHodgeImage G M S)))
        (dualizedSupportProbe
          (fiberedWeightCoordinates V H M.weight
            (bareTwoStepHodgeImage G M S))
          (separatorFiberedProbe
            (V := V) (H := H) M.weight M.separator.detector)) := by
  have h := detector_eq_finiteGSTPoincare
    M.separator.detector (bareTwoStepHodgeImage G M S)
  simpa [bareTwoStepHodgeImage_val G M S] using h

/-- A flag-normal realization only at the one scalar observable actually used
by the minimal-ghost contradiction. -/
structure SingleStateFlagNormalSeparatorReadRealization
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    (S : MinimalGhostLocalSeed G M) where
  sigma : Finset (GSTNativeCodimensionCyclePresentation.CodimensionPoint
    V.X M.weight)
  incidence : PrincipalCutFlagBiFiniteRealization V M.weight sigma
  transpose_naturality :
    GSTClassicalHodgeGradedFiniteClosedCorrespondence.GradedCorrespondencePointNaturality
      incidence.correspondence.transpose H (M.weight + 1) M.weight
  matches_separator_read :
    M.separator.detector
        ((principalCutFlagNormalPair
          (G := G) incidence transpose_naturality).cohomologyOperator
            S.source.1) =
      M.separator.detector
        (ambientTwoStepLefschetz S.sourceIndex M.sheet S.source.1)

namespace SingleStateFlagNormalSeparatorReadRealization

/-- The genuine flag-normal image of the local seed is algebraic.  This uses
only the two exact cycle-class squares and is independent of the read-matching
field. -/
theorem flag_image_algebraic
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    (S : MinimalGhostLocalSeed G M)
    (F : SingleStateFlagNormalSeparatorReadRealization G M S) :
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
  rwa [smoothProjective_cycleClass_range_eq_atomic_span
    V H M.weight] at htargetRange

/-- Since the flag image is algebraic, the minimal atomic separator reads it
as zero. -/
theorem flag_separator_read_eq_zero
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    (S : MinimalGhostLocalSeed G M)
    (F : SingleStateFlagNormalSeparatorReadRealization G M S) :
    M.separator.detector
      ((principalCutFlagNormalPair
        (G := G) F.incidence F.transpose_naturality).cohomologyOperator
          S.source.1) = 0 := by
  have hker :
      pointCycleClassSpan M.weight (H.cycleClass M.weight) ≤
        LinearMap.ker M.separator.detector :=
    (annihilatesPointCycles_iff_atomicSpan_le_ker
      M.weight (H.cycleClass M.weight) M.separator.detector).mp
      M.separator.annihilates_atoms
  exact hker (F.flag_image_algebraic G M S)

/-- **ONE SCALAR FLAG READ KILLS THE MINIMAL GHOST.**
Vector equality with bare `L^2` is unnecessary.  Equality of the one separator
read already collides zero algebraic read with the nonzero GST read. -/
theorem minimalGhost_false
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    (S : MinimalGhostLocalSeed G M)
    (F : SingleStateFlagNormalSeparatorReadRealization G M S) : False := by
  have hzero := F.flag_separator_read_eq_zero G M S
  have hmatch := F.matches_separator_read
  rw [hzero] at hmatch
  exact bareTwoStep_separator_read_ne_zero G M S hmatch.symm

end SingleStateFlagNormalSeparatorReadRealization

/-- A still more geometric formulation: instead of mentioning bare `L^2` on
the right, ask the flag separator read to equal the canonical finite-GST
Poincare observable of that one bare image. -/
structure SingleStateFlagNormalPoincareReadRealization
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    (S : MinimalGhostLocalSeed G M) where
  sigma : Finset (GSTNativeCodimensionCyclePresentation.CodimensionPoint
    V.X M.weight)
  incidence : PrincipalCutFlagBiFiniteRealization V M.weight sigma
  transpose_naturality :
    GSTClassicalHodgeGradedFiniteClosedCorrespondence.GradedCorrespondencePointNaturality
      incidence.correspondence.transpose H (M.weight + 1) M.weight
  flag_read_eq_poincare :
    M.separator.detector
        ((principalCutFlagNormalPair
          (G := G) incidence transpose_naturality).cohomologyOperator
            S.source.1) =
      rationalWorldTopPairing
        (fiberedSupportWorld
          (fiberedWeightCoordinates V H M.weight
            (bareTwoStepHodgeImage G M S)))
        (dualizedSupportProbe
          (fiberedWeightCoordinates V H M.weight
            (bareTwoStepHodgeImage G M S))
          (separatorFiberedProbe
            (V := V) (H := H) M.weight M.separator.detector))

namespace SingleStateFlagNormalPoincareReadRealization

/-- Finite-GST Poincare read matching immediately gives the minimal scalar-read
packet. -/
noncomputable def toSeparatorRead
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    (S : MinimalGhostLocalSeed G M)
    (F : SingleStateFlagNormalPoincareReadRealization G M S) :
    SingleStateFlagNormalSeparatorReadRealization G M S where
  sigma := F.sigma
  incidence := F.incidence
  transpose_naturality := F.transpose_naturality
  matches_separator_read := by
    exact F.flag_read_eq_poincare.trans
      (bareTwoStep_separator_read_eq_finiteGSTPoincare G M S).symm

/-- **ONE FINITE-GST POINCARE READ KILLS THE MINIMAL GHOST.** -/
theorem minimalGhost_false
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    (S : MinimalGhostLocalSeed G M)
    (F : SingleStateFlagNormalPoincareReadRealization G M S) : False :=
  (F.toSeparatorRead G M S).minimalGhost_false G M S

end SingleStateFlagNormalPoincareReadRealization

/-- Global Hodge criterion with only one scalar separator comparison per
hypothetical minimal ghost. -/
theorem bigradedBettiHodge_of_localSeeds_flagNormalSeparatorReads
    (G : GeometricCycleClassSpine V H)
    (seed : ∀ M : MinimalPrimitiveGhost G,
      Nonempty (MinimalGhostLocalSeed G M))
    (flag : ∀ M : MinimalPrimitiveGhost G,
      ∀ S : MinimalGhostLocalSeed G M,
        Nonempty (SingleStateFlagNormalSeparatorReadRealization G M S)) :
    BigradedBettiHodgeStatement V H := by
  by_contra hnot
  let M : MinimalPrimitiveGhost G := minimalPrimitiveGhostOfFailure G hnot
  let S : MinimalGhostLocalSeed G M := (seed M).some
  exact (flag M S).some.minimalGhost_false G M S

/-- Same criterion expressed entirely through the canonical finite-GST
Poincare read. -/
theorem bigradedBettiHodge_of_localSeeds_flagNormalPoincareReads
    (G : GeometricCycleClassSpine V H)
    (seed : ∀ M : MinimalPrimitiveGhost G,
      Nonempty (MinimalGhostLocalSeed G M))
    (flag : ∀ M : MinimalPrimitiveGhost G,
      ∀ S : MinimalGhostLocalSeed G M,
        Nonempty (SingleStateFlagNormalPoincareReadRealization G M S)) :
    BigradedBettiHodgeStatement V H := by
  apply bigradedBettiHodge_of_localSeeds_flagNormalSeparatorReads G seed
  intro M S
  exact ⟨(flag M S).some.toSeparatorRead G M S⟩

#check bareTwoStepHodgeImage
#check bareTwoStep_separator_read_ne_zero
#check bareTwoStep_separator_read_eq_finiteGSTPoincare
#check SingleStateFlagNormalSeparatorReadRealization
#check SingleStateFlagNormalSeparatorReadRealization.minimalGhost_false
#check SingleStateFlagNormalPoincareReadRealization
#check SingleStateFlagNormalPoincareReadRealization.minimalGhost_false
#check bigradedBettiHodge_of_localSeeds_flagNormalSeparatorReads
#check bigradedBettiHodge_of_localSeeds_flagNormalPoincareReads

#print axioms bareTwoStep_separator_read_ne_zero
#print axioms bareTwoStep_separator_read_eq_finiteGSTPoincare
#print axioms SingleStateFlagNormalSeparatorReadRealization.minimalGhost_false
#print axioms SingleStateFlagNormalPoincareReadRealization.minimalGhost_false
#print axioms bigradedBettiHodge_of_localSeeds_flagNormalPoincareReads

end GSTClassicalHodgeSingleStateFlagNormalSeparatorRead
