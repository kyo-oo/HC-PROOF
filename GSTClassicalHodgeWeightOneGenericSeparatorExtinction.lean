import GSTClassicalHodgeGenericSeparatorDegreeSeed
import GSTClassicalHodgeLocalSeedBareLefschetzExtinction

/-!
# GST CLASSICAL HODGE — WEIGHT-ONE GENERIC-SEPARATOR EXTINCTION

The generic-separator exactness layer proves the first ambient rank jump
`0 -> 1` directly from specialization geometry on an irreducible carrier.
Projective degree then turns that exact separator into a nonzero genuine
algebraic Hodge seed in weight one.

This file splices that seed into the minimal-ghost one-motion argument.
Consequently a least Hodge failure at weight one no longer needs any externally
supplied separator-exactness theorem.  The only surviving local input is the
single native point-lift law for the bare two-slot GST `L^2` motion from one
live coordinate of the geometric seed into the detected ghost sheet.

No Hodge surjectivity statement, arbitrary cycle representative, catenarity
axiom, or successor-exactness hypothesis occurs here.
-/

set_option maxHeartbeats 90000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeWeightOneGenericSeparatorExtinction

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeMinimalPrimitiveSeparatorGhost
open GSTClassicalHodgeNativeGeneratorNaturality
open GSTClassicalHodgeLocalSeedBareLefschetzExtinction
open GSTClassicalHodgeProjectiveDegreeTrace
open GSTClassicalHodgeGenericSeparatorDegreeSeed

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- The unconditional generic-separator degree seed becomes the exact local
algebraic source packet required by a minimal ghost of weight one. -/
noncomputable def weightOneLocalSeed
    [IrreducibleSpace V.X]
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (M : MinimalPrimitiveGhost G)
    (hM : M.weight = 1)
    (x : CodimensionPoint V.X 0)
    (hlive : ProjectivelyLiveSource V.projective.n
      (V.projective.immersion x.1)) :
    MinimalGhostLocalSeed G M := by
  let S1 := generic_separator_nativeHodgeSeed G D x hlive
  have hAlg1 : S1.hodge ∈ AlgebraicHodgeSubspace V H 1 := by
    rw [← smoothProjective_cycleClass_range_eq_atomic_span V H 1]
    exact ⟨S1.cycle, S1.class_eq⟩
  let a : ClassicalHodgeFiber V H M.weight := hM.symm ▸ S1.hodge
  have ha0 : a ≠ 0 := by
    subst hM
    exact S1.hodge_ne_zero
  have haAlg : a ∈ AlgebraicHodgeSubspace V H M.weight := by
    subst hM
    exact hAlg1
  exact localSeedOfNonzeroAlgebraic G M a haAlg ha0

/-- **WEIGHT-ONE MINIMAL-GHOST EXTINCTION WITHOUT SUCCESSOR EXACTNESS INPUT.**
The first positive Hodge weight is killed by the geometry-proved generic
separator seed plus one bare GST `L^2` native point-lift law. -/
theorem minimalGhost_false_of_weightOne_genericSeparator_bareLefschetz
    [IrreducibleSpace V.X]
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (M : MinimalPrimitiveGhost G)
    (hM : M.weight = 1)
    (x : CodimensionPoint V.X 0)
    (hlive : ProjectivelyLiveSource V.projective.n
      (V.projective.immersion x.1))
    (hL : HasNativePointLifts
      (p := M.weight) (cl := H.cycleClass M.weight)
      (ambientTwoStepLefschetz
        (weightOneLocalSeed G D M hM x hlive).sourceIndex M.sheet)) : False :=
  minimalGhost_false_of_localSeed_bareLefschetz
    G M (weightOneLocalSeed G D M hM x hlive) hL

#check weightOneLocalSeed
#check minimalGhost_false_of_weightOne_genericSeparator_bareLefschetz

#print axioms weightOneLocalSeed
#print axioms minimalGhost_false_of_weightOne_genericSeparator_bareLefschetz

end GSTClassicalHodgeWeightOneGenericSeparatorExtinction
