import GSTClassicalHodgeMinimalGhostNativeOrbitAnnihilation
import GSTClassicalHodgeProjectiveCorrespondenceCosmicRealization

/-!
# GST CLASSICAL HODGE — MINIMAL GHOST PROJECTIVE TRANSVERSALITY

The minimal-ghost conservation law can be specialized all the way down to the
actual projective-correspondence algebra already present in the repository.
Every projective kernel is a rational linear combination of genuine scheme
endomorphism pushforwards.  Its cohomological action is not supplied by hand:
the geometric cycle-class spine constructs the exact commuting operator pair.

For extinguishing one least-weight ghost we do not need this action to equal a
matrix unit, a cosmic read/write word, or any prescribed operator on the whole
Hodge fiber.  We need only one scalar to be nonzero:

  ghostDetector ( projectiveAction algebraicSource ) != 0.

But projective action is genuinely native-natural, hence it preserves the
actual atomic cycle-class span.  The minimal separator annihilates that span.
Therefore every such scalar is forced to zero.  A single transverse projective
kernel is a contradiction.

This is the smallest projective construction target obtained so far: one
kernel, one algebraic source, one nonzero detector value.
-/

set_option maxHeartbeats 90000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeMinimalGhostProjectiveTransversality

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeMinimalPrimitiveSeparatorGhost
open GSTClassicalHodgePrimitiveAlgebraicDefect
open GSTClassicalHodgeNativeGeneratorNaturality
open GSTClassicalHodgeMinimalGhostNativeOrbitAnnihilation
open GSTClassicalHodgeProjectiveCorrespondenceAlgebra
open GSTClassicalHodgeProjectiveCorrespondenceCosmicRealization

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- The independently induced Betti action of every genuine projective kernel
has native point lifts, witnessed by applying the same native kernel to the
point cycle. -/
theorem projectiveKernel_hasNativePointLifts
    (G : GeometricCycleClassSpine V H)
    {p : Nat}
    (K : ProjectiveNativeKernel V p) :
    HasNativePointLifts
      (p := p) (cl := H.cycleClass p)
      (projectiveCorrespondencePair G K).cohomologyOperator := by
  intro x
  refine ⟨K.operator (codimensionPointCycle V.X p x), ?_⟩
  exact (projectiveCorrespondencePair G K).cycleClass_cycleOperator
    (codimensionPointCycle V.X p x)

/-- Every genuine projective-correspondence action on an algebraic source is
invisible to a surviving minimal ghost. -/
theorem minimalGhost_annihilates_projectiveKernel
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    (K : ProjectiveNativeKernel V M.weight)
    (alpha : ClassicalHodgeFiber V H M.weight)
    (halpha : alpha ∈ AlgebraicHodgeSubspace V H M.weight) :
    M.separator.detector
      ((projectiveCorrespondencePair G K).cohomologyOperator alpha.1) = 0 := by
  exact minimalGhost_annihilates_nativeNatural_image G M
    (projectiveCorrespondencePair G K).cohomologyOperator
    (projectiveKernel_hasNativePointLifts G K)
    alpha halpha

/-- One scalar projective transversality witness.  No operator equality is
requested: the projective kernel merely has to move one algebraic source to a
state detected nontrivially by the least-weight ghost. -/
structure MinimalGhostProjectiveTransverse
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G) where
  kernel : ProjectiveNativeKernel V M.weight
  source : ClassicalHodgeFiber V H M.weight
  source_algebraic : source ∈ AlgebraicHodgeSubspace V H M.weight
  transverse :
    M.separator.detector
      ((projectiveCorrespondencePair G kernel).cohomologyOperator source.1) ≠ 0

/-- **ONE-SCALAR PROJECTIVE EXTINCTION.**
A least-weight separator ghost cannot coexist with even one transverse element
of the genuine projective-correspondence algebra. -/
theorem minimalGhost_false_of_projectiveTransverse
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    (T : MinimalGhostProjectiveTransverse G M) : False := by
  exact T.transverse
    (minimalGhost_annihilates_projectiveKernel G M
      T.kernel T.source T.source_algebraic)

/-- Complete Stage-2G landing follows if every hypothetical least-weight ghost
admits one projective-transverse scalar witness.  This target is strictly
weaker than projective realization of a cosmic matrix unit on an entire Hodge
fiber. -/
theorem bigradedBettiHodge_of_minimalGhost_projectiveTransversality
    (G : GeometricCycleClassSpine V H)
    (T : ∀ M : MinimalPrimitiveGhost G,
      Nonempty (MinimalGhostProjectiveTransverse G M)) :
    BigradedBettiHodgeStatement V H := by
  by_contra hnot
  let M : MinimalPrimitiveGhost G := minimalPrimitiveGhostOfFailure G hnot
  exact minimalGhost_false_of_projectiveTransverse G M (T M).some

/-- Equivalent negative form: under a surviving minimal ghost the whole
projective-correspondence orbit of the algebraic Hodge subspace lies inside the
separator hyperplane. -/
theorem minimalGhost_projective_orbit_subset_kernel
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G) :
    ∀ (K : ProjectiveNativeKernel V M.weight),
      ∀ alpha : ClassicalHodgeFiber V H M.weight,
        alpha ∈ AlgebraicHodgeSubspace V H M.weight →
          M.separator.detector
            ((projectiveCorrespondencePair G K).cohomologyOperator alpha.1) = 0 := by
  intro K alpha halpha
  exact minimalGhost_annihilates_projectiveKernel G M K alpha halpha

#check projectiveKernel_hasNativePointLifts
#check minimalGhost_annihilates_projectiveKernel
#check MinimalGhostProjectiveTransverse
#check minimalGhost_false_of_projectiveTransverse
#check bigradedBettiHodge_of_minimalGhost_projectiveTransversality
#check minimalGhost_projective_orbit_subset_kernel

#print axioms projectiveKernel_hasNativePointLifts
#print axioms minimalGhost_annihilates_projectiveKernel
#print axioms minimalGhost_false_of_projectiveTransverse
#print axioms bigradedBettiHodge_of_minimalGhost_projectiveTransversality

end GSTClassicalHodgeMinimalGhostProjectiveTransversality
