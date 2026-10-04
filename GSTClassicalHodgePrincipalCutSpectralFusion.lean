import GSTClassicalHodgePrincipalCutNonzeroForcesExactSuccessor
import GSTClassicalHodgeClosedCorrespondenceSpectralAmplifier

/-!
# GST CLASSICAL HODGE — PRINCIPAL-CUT / SPECTRAL FUSION

The closed-correspondence spectral amplifier was originally phrased with a
point-visible seed for each selected Hodge sheet.  That restriction is not
mathematical: polynomial functional calculus for a realized correspondence is
cycle-class natural on every native algebraic cycle.

This file feeds the synchronized algebraic Hodge seed produced by a nonzero
genuine principal-cut action directly into the spectral extractor.  Hence one
actual principal-cut cycle may be reused for every spectral slot in which it
has nonzero coordinate.  No projectively-live separator, exact-successor
input, target cycle, matrix-unit realization, or point-visible witness is
needed.
-/

set_option maxHeartbeats 120000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open scoped BigOperators

namespace GSTClassicalHodgePrincipalCutSpectralFusion

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeProjectiveDegreeTrace
open GSTClassicalHodgeSynchronizedDefectOrbit
open GSTClassicalHodgePrincipalCutNonzeroForcesExactSuccessor
open GSTClassicalHodgeCanonicalSpectralObservable
open GSTClassicalHodgeClosedCorrespondenceSpectralAmplifier
open GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra
open GSTClassicalHodgeCycleOperatorNaturality

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- A synchronized native/Hodge seed is visible in a spectral slot precisely
when its genuine Hodge coordinate in that slot is nonzero. -/
def SeedVisible
    {G : GeometricCycleClassSpine V H}
    {W : FiniteHodgeBasisWindow V H p}
    (R : ClosedCorrespondenceWindowRealization G W)
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (i : Fin W.N) : Prop :=
  hodgeCoordinate (W.basisIndex i) S.hodge ≠ 0

/-- Apply the augmented spectral projector polynomial directly to the native
cycle carried by a synchronized source and normalize by its nonzero slot
coordinate. -/
noncomputable def extractedBasisCycleFromSeed
    {G : GeometricCycleClassSpine V H}
    {W : FiniteHodgeBasisWindow V H p}
    (R : ClosedCorrespondenceWindowRealization G W)
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (i : Fin W.N)
    (hvis : SeedVisible R S i) :
    codimensionCycles V.X p := by
  let c : ℚ := hodgeCoordinate (W.basisIndex i) S.hodge
  let s : ℚ := W.augmentedIsolatorScale i
  exact (s * c)⁻¹ •
    linearPolyEval (realizedWordPair R.word).cycleOperator
      (W.augmentedIsolatorPolynomial i) S.cycle

/-- **ALGEBRAIC-SEED SPECTRAL EXTRACTION.**
The spectral polynomial of one genuine realized correspondence extracts the
exact requested Hodge basis sheet from any synchronized algebraic seed that is
visible in that slot. -/
theorem extractedBasisCycleFromSeed_spec
    {G : GeometricCycleClassSpine V H}
    {W : FiniteHodgeBasisWindow V H p}
    (R : ClosedCorrespondenceWindowRealization G W)
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (i : Fin W.N)
    (hvis : SeedVisible R S i) :
    H.cycleClass p (extractedBasisCycleFromSeed R S i hvis) =
      (classicalHodgeBasis V H p (W.basisIndex i)).1 := by
  let c : ℚ := hodgeCoordinate (W.basisIndex i) S.hodge
  let s : ℚ := W.augmentedIsolatorScale i
  have hc : c ≠ 0 := hvis
  have hs : s ≠ 0 := W.augmentedIsolatorScale_ne_zero i
  have hnat := linearPolyEval_intertwines
    (H.cycleClass p)
    (realizedWordPair R.word).cycleOperator
    (realizedWordPair R.word).cohomologyOperator
    (realizedWordPair R.word).cycleClass_cycleOperator
    (W.augmentedIsolatorPolynomial i)
    S.cycle
  have hpolyWord :
      linearPolyEval (realizedWordPair R.word).cohomologyOperator
          (W.augmentedIsolatorPolynomial i) S.hodge.1 =
        linearPolyEval W.zeroComplementObservable
          (W.augmentedIsolatorPolynomial i) S.hodge.1 :=
    R.linearPolyEval_on_hodge (W.augmentedIsolatorPolynomial i) S.hodge
  have hproj := W.augmentedProjectorOnHodge_apply i S.hodge
  unfold extractedBasisCycleFromSeed
  rw [LinearMap.map_smul]
  rw [hnat]
  rw [S.class_eq]
  change (s * c)⁻¹ •
      linearPolyEval (realizedWordPair R.word).cohomologyOperator
        (W.augmentedIsolatorPolynomial i) S.hodge.1 = _
  rw [hpolyWord]
  change (s * c)⁻¹ • W.augmentedProjectorOnHodge i S.hodge = _
  rw [hproj]
  simp [s, c, hs, hc, smul_smul, mul_comm, mul_left_comm, mul_assoc]

/-- Every slot visible from one synchronized algebraic seed is therefore in the
actual native cycle-class range. -/
theorem visibleSeed_basis_mem_cycleClass_range
    {G : GeometricCycleClassSpine V H}
    {W : FiniteHodgeBasisWindow V H p}
    (R : ClosedCorrespondenceWindowRealization G W)
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (i : Fin W.N)
    (hvis : SeedVisible R S i) :
    (classicalHodgeBasis V H p (W.basisIndex i)).1 ∈
      LinearMap.range (H.cycleClass p) := by
  exact ⟨extractedBasisCycleFromSeed R S i hvis,
    extractedBasisCycleFromSeed_spec R S i hvis⟩

/-- A single synchronized algebraic seed that is visible in every selected slot
algebraizes the entire selected spectral window. -/
theorem visibleSeed_window_algebraic
    {G : GeometricCycleClassSpine V H}
    {W : FiniteHodgeBasisWindow V H p}
    (R : ClosedCorrespondenceWindowRealization G W)
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (hvis : ∀ i : Fin W.N, SeedVisible R S i) :
    ∀ i : Fin W.N,
      (classicalHodgeBasis V H p (W.basisIndex i)).1 ∈
        LinearMap.range (H.cycleClass p) :=
  fun i => visibleSeed_basis_mem_cycleClass_range R S i (hvis i)

/-- **PRINCIPAL-CUT / SPECTRAL TARGET EXTRACTION.**
A nonzero genuine principal-cut cohomology action produces the synchronized
algebraic seed.  One genuine closed-correspondence spectral observable then
extracts any selected Hodge sheet on which that seed has nonzero coordinate.
The old projectively-live/exact-successor witness is completely absent. -/
theorem principalCut_nonzero_spectral_basis_cycle
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (q : Nat)
    (x : CodimensionPoint V.X q)
    (hCoh :
      (G.principalCutPair q).cohomologyOperator
          (H.cycleClass q (codimensionPointCycle V.X q x)) ≠ 0)
    {W : FiniteHodgeBasisWindow V H (q + 1)}
    (R : ClosedCorrespondenceWindowRealization G W)
    (i : Fin W.N)
    (hvis : SeedVisible R
      (nativeHodgeSeed_of_principalCut_point_nonzero G D q x hCoh) i) :
    ∃ Z : codimensionCycles V.X (q + 1),
      H.cycleClass (q + 1) Z =
        (classicalHodgeBasis V H (q + 1) (W.basisIndex i)).1 := by
  let S := nativeHodgeSeed_of_principalCut_point_nonzero G D q x hCoh
  exact ⟨extractedBasisCycleFromSeed R S i hvis,
    extractedBasisCycleFromSeed_spec R S i hvis⟩

#check SeedVisible
#check extractedBasisCycleFromSeed
#check extractedBasisCycleFromSeed_spec
#check visibleSeed_basis_mem_cycleClass_range
#check visibleSeed_window_algebraic
#check principalCut_nonzero_spectral_basis_cycle

#print axioms extractedBasisCycleFromSeed_spec
#print axioms visibleSeed_window_algebraic
#print axioms principalCut_nonzero_spectral_basis_cycle

end GSTClassicalHodgePrincipalCutSpectralFusion