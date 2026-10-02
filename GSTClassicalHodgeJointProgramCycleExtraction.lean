import GSTClassicalHodgeJointProgramInterpolation

/-!
# Native cycle extraction from a finite joint spectrum

An independently supplied native seed may contain many spectral directions.
The ordered projector compiled in the preceding module removes the unwanted
directions.  Only the coefficient of the requested direction must be nonzero.
The witness is execution of an actual geometric program on the native seed.

For orbit seeds, the same construction compiles a program from weight zero;
there is no all-weight conserved charge or global nonvanishing requirement.
-/

noncomputable section

open scoped BigOperators

namespace GSTClassicalHodgeJointProgramCycleExtraction

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeGradedGeometricProgramOrbit
open GSTClassicalHodgeGradedGeometricOrbitAlgebra
open GSTClassicalHodgeJointProgramInterpolation

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {G : GeometricCycleClassSpine V H}
variable {p : Nat}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The normalization is performed on the native cycle, after execution of
the genuine geometric projector. -/
def extractedCycle (S : JointProgramSpectrum G p ι)
    (a : ι → ℚ) (Z : codimensionCycles V.X p) (i : ι) :
    codimensionCycles V.X p :=
  (a i)⁻¹ • (S.projector i).cycleEval G Z

/-- Exact native witness for one selected direction.  No nonzero condition
is imposed on the seed's other coordinates. -/
theorem extractedCycle_spec (S : JointProgramSpectrum G p ι)
    (a : ι → ℚ) (Z : codimensionCycles V.X p) (i : ι)
    (hseed : H.cycleClass p Z = ∑ k, a k • S.vector k)
    (hlive : a i ≠ 0) :
    H.cycleClass p (extractedCycle S a Z i) = S.vector i := by
  unfold extractedCycle
  rw [map_smul, GradedGeometricProgram.cycleClass_cycleEval,
    hseed, S.projector_on_sum]
  exact inv_smul_smul₀ hlive _

/-- A surviving coordinate of any native spectral seed is algebraic. -/
theorem vector_mem_cycleClass_range (S : JointProgramSpectrum G p ι)
    (a : ι → ℚ) (Z : codimensionCycles V.X p) (i : ι)
    (hseed : H.cycleClass p Z = ∑ k, a k • S.vector k)
    (hlive : a i ≠ 0) :
    S.vector i ∈ LinearMap.range (H.cycleClass p) :=
  ⟨extractedCycle S a Z i, extractedCycle_spec S a Z i hseed hlive⟩

/-- Native extraction also establishes Hodge type, even when the spectrum's
vectors were initially specified only in ambient cohomology. -/
theorem extracted_vector_is_hodge (S : JointProgramSpectrum G p ι)
    (a : ι → ℚ) (Z : codimensionCycles V.X p) (i : ι)
    (hseed : H.cycleClass p Z = ∑ k, a k • S.vector k)
    (hlive : a i ≠ 0) :
    S.vector i ∈ rationalHodgeSubspace (H.hodgeBigrading p) := by
  rw [← extractedCycle_spec S a Z i hseed hlive]
  exact G.algebraic_is_hodge p _

/-- Compile normalization, a weight-zero source program, and the ordered
projector into a single program. -/
def extractedProgram (S : JointProgramSpectrum G p ι)
    (a : ι → ℚ) (P : GradedGeometricProgram V 0 p) (i : ι) :
    GradedGeometricProgram V 0 p :=
  .smul (a i)⁻¹ (.comp P (S.projector i))

theorem extractedProgram_spec (S : JointProgramSpectrum G p ι)
    (a : ι → ℚ) (P : GradedGeometricProgram V 0 p) (i : ι)
    (hseed : P.cohomologyEval G (geometricOriginClass V H) =
      ∑ k, a k • S.vector k)
    (hlive : a i ≠ 0) :
    (extractedProgram S a P i).cohomologyEval G
      (geometricOriginClass V H) = S.vector i := by
  change (a i)⁻¹ • (S.projector i).cohomologyEval G
      (P.cohomologyEval G (geometricOriginClass V H)) = S.vector i
  rw [hseed, S.projector_on_sum]
  exact inv_smul_smul₀ hlive _

/-- Extraction at native level is literally composition of the same programs. -/
theorem extractedProgram_cycleEval (S : JointProgramSpectrum G p ι)
    (a : ι → ℚ) (P : GradedGeometricProgram V 0 p) (i : ι)
    (Z : codimensionCycles V.X 0) :
    (extractedProgram S a P i).cycleEval G Z =
      extractedCycle S a (P.cycleEval G Z) i := by
  rfl

theorem vector_mem_orbit_of_spectral_seed (S : JointProgramSpectrum G p ι)
    (a : ι → ℚ) (i : ι)
    (hseed : (∑ k, a k • S.vector k) ∈ geometricProgramOrbitModule G p)
    (hlive : a i ≠ 0) :
    S.vector i ∈ geometricProgramOrbitModule G p := by
  rcases hseed with ⟨P, hP⟩
  exact ⟨extractedProgram S a P i,
    (extractedProgram_spec S a P i hP.symm hlive).symm⟩

/-- Each target may use its own seed.  A single jointly nonzero seed is not
needed, so the construction bypasses hyperplane avoidance. -/
def spectralCycleAssembly (S : JointProgramSpectrum G p ι)
    (a : ι → ι → ℚ) (Z : ι → codimensionCycles V.X p)
    (b : ι → ℚ) : codimensionCycles V.X p :=
  ∑ i, b i • extractedCycle S (a i) (Z i) i

theorem spectralCycleAssembly_spec (S : JointProgramSpectrum G p ι)
    (a : ι → ι → ℚ) (Z : ι → codimensionCycles V.X p)
    (hseed : ∀ i, H.cycleClass p (Z i) = ∑ k, a i k • S.vector k)
    (hlive : ∀ i, a i i ≠ 0) (b : ι → ℚ) :
    H.cycleClass p (spectralCycleAssembly S a Z b) =
      ∑ i, b i • S.vector i := by
  unfold spectralCycleAssembly
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, extractedCycle_spec S (a i) (Z i) i (hseed i) (hlive i)]

/-- Extraction witnesses depend linearly on the target coefficients once the
independent seeds have been fixed. -/
def spectralCycleAssemblyLinear (S : JointProgramSpectrum G p ι)
    (a : ι → ι → ℚ) (Z : ι → codimensionCycles V.X p) :
    (ι → ℚ) →ₗ[ℚ] codimensionCycles V.X p where
  toFun := spectralCycleAssembly S a Z
  map_add' := by
    intro b c
    simp [spectralCycleAssembly, add_smul, Finset.sum_add_distrib]
  map_smul' := by
    intro c b
    simp [spectralCycleAssembly, mul_smul, Finset.smul_sum]

#print axioms extractedCycle_spec
#print axioms extracted_vector_is_hodge
#print axioms extractedProgram_spec
#print axioms vector_mem_orbit_of_spectral_seed
#print axioms spectralCycleAssembly_spec

end GSTClassicalHodgeJointProgramCycleExtraction
