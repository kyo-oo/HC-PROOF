import GSTClassicalHodgeJointProgramCycleExtraction
import GSTClassicalHodgeGradedProgramSpectralSaturation

/-!
# Finite Hodge landing through joint geometric spectra

Each live direction may use a different finite spectrum, different probes,
and a different native seed.  The requested Hodge class is reconstructed by
an explicit finite sum of the extracted native cycles.  Competitor directions
need not belong to the class's support and need not initially be Hodge classes.

The coverage hypotheses remain explicit.  This module compiles such geometric
data into witnesses; it does not assert their existence for arbitrary varieties.
-/

noncomputable section

open scoped BigOperators

namespace GSTClassicalHodgeJointSpectrumFiniteLanding

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeLocalCyclicCriterion
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeCodimensionZeroFundamentalCycle
open GSTClassicalHodgeGradedGeometricProgramOrbit
open GSTClassicalHodgeGradedGeometricOrbitAlgebra
open GSTClassicalHodgeGradedProgramSpectralSaturation
open GSTClassicalHodgeJointProgramInterpolation
open GSTClassicalHodgeJointProgramCycleExtraction

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {G : GeometricCycleClassSpine V H}
variable {p : Nat}

/-- Local data for extracting one target.  The seed equation is a verifiable
finite expansion; no cycle representative of the target itself is a field. -/
structure JointNativeTarget (G : GeometricCycleClassSpine V H)
    {p : Nat} (v : RationalSingularCohomology H.analytification (2 * p)) where
  rank : Nat
  spectrum : JointProgramSpectrum G p (Fin rank)
  target : Fin rank
  target_eq : spectrum.vector target = v
  seed : codimensionCycles V.X p
  coefficient : Fin rank → ℚ
  seed_eq : H.cycleClass p seed = ∑ k, coefficient k • spectrum.vector k
  target_live : coefficient target ≠ 0

namespace JointNativeTarget

variable {v : RationalSingularCohomology H.analytification (2 * p)}

def cycle (T : JointNativeTarget G v) : codimensionCycles V.X p :=
  extractedCycle T.spectrum T.coefficient T.seed T.target

theorem cycle_spec (T : JointNativeTarget G v) :
    H.cycleClass p T.cycle = v := by
  exact (extractedCycle_spec T.spectrum T.coefficient T.seed T.target
    T.seed_eq T.target_live).trans T.target_eq

end JointNativeTarget

/-- Stronger source provenance: the seed is executed from the fundamental
cycle by a finite mixed geometric program. -/
structure JointOrbitTarget (G : GeometricCycleClassSpine V H)
    {p : Nat} (v : RationalSingularCohomology H.analytification (2 * p)) where
  rank : Nat
  spectrum : JointProgramSpectrum G p (Fin rank)
  target : Fin rank
  target_eq : spectrum.vector target = v
  source : GradedGeometricProgram V 0 p
  coefficient : Fin rank → ℚ
  source_eq : source.cohomologyEval G (geometricOriginClass V H) =
    ∑ k, coefficient k • spectrum.vector k
  target_live : coefficient target ≠ 0

namespace JointOrbitTarget

variable {v : RationalSingularCohomology H.analytification (2 * p)}

def program (T : JointOrbitTarget G v) : GradedGeometricProgram V 0 p :=
  extractedProgram T.spectrum T.coefficient T.source T.target

theorem program_spec (T : JointOrbitTarget G v) :
    T.program.cohomologyEval G (geometricOriginClass V H) = v := by
  exact (extractedProgram_spec T.spectrum T.coefficient T.source T.target
    T.source_eq T.target_live).trans T.target_eq

def toNativeTarget (T : JointOrbitTarget G v) : JointNativeTarget G v where
  rank := T.rank
  spectrum := T.spectrum
  target := T.target
  target_eq := T.target_eq
  seed := T.source.cycleEval G (codimensionZeroFundamentalCycle V)
  coefficient := T.coefficient
  seed_eq := by
    rw [GradedGeometricProgram.cycleClass_cycleEval]
    exact T.source_eq
  target_live := T.target_live

theorem mem_orbit (T : JointOrbitTarget G v) :
    v ∈ geometricProgramOrbitModule G p :=
  ⟨T.program, T.program_spec.symm⟩

end JointOrbitTarget

/-- Independent finite native spectra cover precisely the live target support. -/
structure FiniteJointNativeCover (G : GeometricCycleClassSpine V H)
    {p : Nat} (alpha : ClassicalHodgeFiber V H p) where
  direction : ∀ i : HodgeSupportIndex alpha,
    JointNativeTarget G (classicalHodgeBasis V H p i.1).1

namespace FiniteJointNativeCover

variable {alpha : ClassicalHodgeFiber V H p}

/-- Explicit cycle: normalize and execute each local projector, then sum with
the original target's basis coefficients. -/
def cycle (C : FiniteJointNativeCover G alpha) : codimensionCycles V.X p :=
  ∑ i : HodgeSupportIndex alpha,
    (classicalHodgeBasis V H p).repr alpha i.1 • (C.direction i).cycle

theorem cycle_spec (C : FiniteJointNativeCover G alpha) :
    H.cycleClass p C.cycle = alpha.1 := by
  unfold cycle
  rw [map_sum, hodgeClass_eq_support_sum alpha]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, (C.direction i).cycle_spec]

theorem exists_native_cycle (C : FiniteJointNativeCover G alpha) :
    ∃ Z : codimensionCycles V.X p, H.cycleClass p Z = alpha.1 :=
  ⟨C.cycle, C.cycle_spec⟩

end FiniteJointNativeCover

/-- Orbit-source version of a local cover. -/
structure FiniteJointOrbitCover (G : GeometricCycleClassSpine V H)
    {p : Nat} (alpha : ClassicalHodgeFiber V H p) where
  direction : ∀ i : HodgeSupportIndex alpha,
    JointOrbitTarget G (classicalHodgeBasis V H p i.1).1

namespace FiniteJointOrbitCover

variable {alpha : ClassicalHodgeFiber V H p}

def toNativeCover (C : FiniteJointOrbitCover G alpha) :
    FiniteJointNativeCover G alpha where
  direction i := (C.direction i).toNativeTarget

theorem class_mem_orbit (C : FiniteJointOrbitCover G alpha) :
    alpha.1 ∈ geometricProgramOrbitModule G p := by
  rw [hodgeClass_eq_support_sum alpha]
  apply Submodule.sum_mem
  intro i _
  exact (geometricProgramOrbitModule G p).smul_mem
    ((classicalHodgeBasis V H p).repr alpha i.1) (C.direction i).mem_orbit

/-- Native witness with all local seeds traced to geometric programs. -/
theorem exists_native_cycle (C : FiniteJointOrbitCover G alpha) :
    ∃ Z : codimensionCycles V.X p, H.cycleClass p Z = alpha.1 :=
  C.toNativeCover.exists_native_cycle

/-- Since programs admit rational addition, the entire finite assembly is
also reachable by one program from the fundamental cycle. -/
theorem exists_single_program (C : FiniteJointOrbitCover G alpha) :
    ∃ P : GradedGeometricProgram V 0 p,
      P.cohomologyEval G (geometricOriginClass V H) = alpha.1 := by
  obtain ⟨P, hP⟩ := C.class_mem_orbit
  exact ⟨P, hP.symm⟩

end FiniteJointOrbitCover

/-! Compatibility with the existing green single-observable route. -/

section SingleSpectrum

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A single simple spectrum is a special case of the joint-spectrum engine. -/
def singleSpectrumToJoint
    (S : GradedProgramSpectralFamily (V := V) (H := H) (p := p) G ι) :
    JointProgramSpectrum G p ι where
  vector i := (classicalHodgeBasis V H p (S.basisIndex i)).1
  probe _ _ := S.program
  eigenvalue _ _ k := S.eigenvalue k
  eigenvector _ _ k := S.eigenvector k
  separates i j hji := S.eigenvalue_injective.ne hji.symm

end SingleSpectrum

/-- Every old finite spectral cover supplies the new local orbit data using
its original coordinatewise-visible seeds.  No simultaneous cyclic-seed
assembly or hidden target-cycle choice is used. -/
def orbitCoverOfSingleSpectrum {alpha : ClassicalHodgeFiber V H p}
    (C : FiniteGradedProgramSpectralCover G alpha) :
    FiniteJointOrbitCover G alpha := by
  classical
  refine ⟨fun i => ?_⟩
  let k := Classical.choose (C.covers_live_support i)
  have hk := Classical.choose_spec (C.covers_live_support i)
  let a := Classical.choose (C.visible k)
  have ha := Classical.choose_spec (C.visible k)
  have hmem : (∑ j : Fin C.rank,
      a.1 j • (classicalHodgeBasis V H p (C.spectral.basisIndex j)).1) ∈
        geometricProgramOrbitModule G p := a.2
  have hex : ∃ P : GradedGeometricProgram V 0 p,
      (∑ j : Fin C.rank,
        a.1 j • (classicalHodgeBasis V H p (C.spectral.basisIndex j)).1) =
          P.cohomologyEval G (geometricOriginClass V H) := hmem
  let P := Classical.choose hex
  have hP := Classical.choose_spec hex
  exact {
    rank := C.rank
    spectrum := singleSpectrumToJoint C.spectral
    target := k
    target_eq := by
      change (classicalHodgeBasis V H p (C.spectral.basisIndex k)).1 = _
      exact congrArg (fun j => (classicalHodgeBasis V H p j).1) hk
    source := P
    coefficient := a.1
    source_eq := hP.symm
    target_live := ha
  }

/-- Native extraction for every existing single-spectrum cover is a direct
specialization of the compiled joint-spectrum route. -/
def nativeCoverOfSingleSpectrum {alpha : ClassicalHodgeFiber V H p}
    (C : FiniteGradedProgramSpectralCover G alpha) :
    FiniteJointNativeCover G alpha :=
  (orbitCoverOfSingleSpectrum C).toNativeCover

/-- Public landing.  Its finite coverage input is explicit and must still be
constructed in the intended geometric application. -/
theorem bigradedBettiHodge_of_finite_joint_native_covers
    (G : GeometricCycleClassSpine V H)
    (C : ∀ q : Nat, ∀ alpha : ClassicalHodgeFiber V H q,
      Nonempty (FiniteJointNativeCover G alpha)) :
    BigradedBettiHodgeStatement V H := by
  intro q x hx
  exact (Classical.choice (C q ⟨x, hx⟩)).exists_native_cycle

theorem gradedGeometricOrbitCyclic_of_finite_joint_orbit_covers
    (G : GeometricCycleClassSpine V H)
    (C : ∀ q : Nat, ∀ alpha : ClassicalHodgeFiber V H q,
      Nonempty (FiniteJointOrbitCover G alpha)) :
    GradedGeometricOrbitModuleCyclic G := by
  intro q x hx
  exact (Classical.choice (C q ⟨x, hx⟩)).class_mem_orbit

#print axioms JointNativeTarget.cycle_spec
#print axioms JointOrbitTarget.program_spec
#print axioms FiniteJointNativeCover.cycle_spec
#print axioms FiniteJointOrbitCover.exists_single_program
#print axioms orbitCoverOfSingleSpectrum
#print axioms nativeCoverOfSingleSpectrum
#print axioms bigradedBettiHodge_of_finite_joint_native_covers
#print axioms gradedGeometricOrbitCyclic_of_finite_joint_orbit_covers

end GSTClassicalHodgeJointSpectrumFiniteLanding
