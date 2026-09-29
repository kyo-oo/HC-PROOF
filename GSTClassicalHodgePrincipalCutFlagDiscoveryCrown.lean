import GSTClassicalHodgePrincipalCutFlagNativeReturn
import GSTClassicalHodgeNativeCohomologyExtensionAmbiguity
import GSTClassicalHodgeGeometricCycleClassSpine

/-!
# GST CLASSICAL HODGE — PRINCIPAL-CUT FLAG DISCOVERY CROWN

This module records the full output of the new brute-force discovery layer in
one place.

The old attack searched directly for a cohomological inverse/matrix unit.  The
new route starts from the actual principal-cut geometry and proves first what
is genuinely forced there.

For every live source point in a finite chart:

1. the forward flag is the existing geometric principal-cut operator;
2. its finite reverse flag exists on native cycles;
3. the native round trip has a nonzero diagonal coefficient and an explicit
   algebraic correction cycle;
4. any two cohomological realizations of this SAME native round trip can differ
   only through the atomic-defect quotient.

Hence all native-cycle geometry and all scalar self-return data are already
fixed.  The only remaining freedom is one quotient map on the non-algebraic
primitive defect sector.  This is the precise target for the GST
Poincare/worldtrace expansion; no further manipulation of ordinary native
cycles can change it.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgePrincipalCutFlagDiscoveryCrown

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeCrossWeightNativePropagation
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgePrincipalCutIncidenceTransposeCosmology
open GSTClassicalHodgePrincipalCutFlagAdjointCosmology
open GSTClassicalHodgePrincipalCutFlagNativeReturn
open GSTClassicalHodgeNativeCohomologyExtensionAmbiguity

/-- **NATIVE FLAG DISCOVERY CROWN.**
The principal-cut flag has a certified forward cohomological face and a native
reverse whose point round trip is nonzero diagonal plus one actual correction
cycle. -/
theorem principalCutFlag_native_discovery_crown
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (sigma : Finset (CodimensionPoint V.X p))
    (x : CodimensionPoint V.X p)
    (hx : x ∈ sigma)
    (hExact : GSTClassicalHodgeRelativeSuccessorExactStratum.RelativeSuccessorAmbientExact V p x)
    (hNonempty : (GSTClassicalHodgePointClosureRelativeCut.relativeCodimensionOneFinset V x.1).Nonempty) :
    let lambda := successorSelfEnergy V p x
    lambda ≠ 0
      ∧ localFlagNormalNative V p sigma (codimensionPointCycle V.X p x) =
          lambda • codimensionPointCycle V.X p x +
            crossTalkCycle V p sigma x
      ∧ H.cycleClass (p + 1) (successorPresentationCycle V p x) =
          (G.principalCutPair p).cohomologyOperator
            (H.cycleClass p (codimensionPointCycle V.X p x)) := by
  dsimp
  exact ⟨
    successorSelfEnergy_ne_zero_of_exact_nonempty
      V p x hExact hNonempty,
    localFlagNormalNative_point_decomposition V p sigma x,
    cycleClass_successorPresentationCycle G p x⟩

/-- If two ambient cohomological realizations use exactly the native flag
normal operator, all disagreement between them is already concentrated in the
atomic-defect quotient. -/
theorem flagNormal_realizations_differ_only_on_defect
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    {p : Nat}
    (sigma : Finset (CodimensionPoint V.X p))
    (A B : GradedCycleClassOperatorPair V H p p)
    (hA : A.cycleOperator = localFlagNormalNative V p sigma)
    (hB : B.cycleOperator = localFlagNormalNative V p sigma) :
    GSTClassicalHodgeAtomicSpan.pointCycleClassSpan p (H.cycleClass p) ≤
      LinearMap.ker (cohomologyDifference A B) := by
  apply atomicSpan_le_difference_kernel A B
  exact hA.trans hB.symm

/-- Exact uniqueness statement specialized to the new principal-cut flag
normal geometry.  Once the residual quotient ambiguity is killed, there is no
second hidden cohomological freedom. -/
theorem flagNormal_cohomology_unique_iff_defectAmbiguity_zero
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    {p : Nat}
    (sigma : Finset (CodimensionPoint V.X p))
    (A B : GradedCycleClassOperatorPair V H p p)
    (hA : A.cycleOperator = localFlagNormalNative V p sigma)
    (hB : B.cycleOperator = localFlagNormalNative V p sigma) :
    A.cohomologyOperator = B.cohomologyOperator ↔
      extensionAmbiguity A B (hA.trans hB.symm) = 0 := by
  exact cohomologyExtension_unique_iff A B (hA.trans hB.symm)

/-- A genuinely different cohomological realization of the fixed native flag
normal must expose a nonzero primitive/atomic-defect witness. -/
theorem flagNormal_difference_has_defect_witness
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    {p : Nat}
    (sigma : Finset (CodimensionPoint V.X p))
    (A B : GradedCycleClassOperatorPair V H p p)
    (hA : A.cycleOperator = localFlagNormalNative V p sigma)
    (hB : B.cycleOperator = localFlagNormalNative V p sigma)
    (hne : A.cohomologyOperator ≠ B.cohomologyOperator) :
    ∃ z : GSTClassicalHodgeAtomicDefectDuality.AtomicDefectSpace V H p,
      extensionAmbiguity A B (hA.trans hB.symm) z ≠ 0 := by
  exact exists_defect_witness_of_cohomologyOperator_ne
    A B (hA.trans hB.symm) hne

#check principalCutFlag_native_discovery_crown
#check flagNormal_realizations_differ_only_on_defect
#check flagNormal_cohomology_unique_iff_defectAmbiguity_zero
#check flagNormal_difference_has_defect_witness

#print axioms principalCutFlag_native_discovery_crown
#print axioms flagNormal_realizations_differ_only_on_defect
#print axioms flagNormal_cohomology_unique_iff_defectAmbiguity_zero
#print axioms flagNormal_difference_has_defect_witness

end GSTClassicalHodgePrincipalCutFlagDiscoveryCrown
