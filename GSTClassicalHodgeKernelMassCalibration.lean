import GSTClassicalHodgeSynchronizedSeedFiberedLanding

/-!
# GST CLASSICAL HODGE — KERNEL MASS CALIBRATION

This file removes the scalar fibered-joint-state obstruction whenever native
mass has a nontrivial direction invisible to the actual cycle-class map.

For a synchronized algebraic Hodge seed S and a null-class cycle K with
nonzero canonical native mass, set

  calibratedCycle(S,K)
    = S.cycle
      + ((classicalHodgeMass(S.hodge) - nativeCycleMass(S.cycle))
           * nativeCycleMass(K)^(-1)) • K.

The calibrated cycle has *exactly the same genuine cohomology class* as S.
Its native mass is exactly the mass of S's genuine Hodge coordinate vector.
The two finite marginals therefore glue into an explicit fibered-native state
with zero actual cycle-class defect.

The final dichotomy is unconditional and contains no Hodge conclusion:

* either native mass annihilates the cycle-class kernel at weight p; or
* every ALREADY algebraic synchronized seed at that weight admits a finite
  defect-zero joint representation.

This is a mass-calibration and internal lifting theorem, not a construction
of previously nonalgebraic target Hodge basis cycles. No Hodge-surjectivity,
ghost-targeted closure, D/branch packet, projective spoke, or two-successor
cardinality law appears as a premise.
-/

set_option maxHeartbeats 90000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeKernelMassCalibration

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeSynchronizedDefectOrbit
open GSTClassicalHodgeSynchronizedSeedFiberedLanding
open GSTClassicalHodgeFiberedNativePullback
open GSTClassicalHodgeFiberedCycleClassDefect
open GSTClassicalHodgeNativeCycleCosmicShadow
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeThreeUniverseSeedIdentification

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Native mass vanishes on every cohomologically null native cycle at this
fixed weight. The negation is precisely the calibration witness below. -/
def NativeMassKernelLawAtWeight : Prop :=
  ∀ K : codimensionCycles V.X p,
    H.cycleClass p K = 0 → nativeCycleMass V p K = 0

/-- An explicit affine correction of a genuine synchronized seed along one
native cycle. Its coefficient is chosen to match the Hodge coordinate mass. -/
noncomputable def massCalibratedCycle
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (K : codimensionCycles V.X p) : codimensionCycles V.X p :=
  S.cycle +
    ((classicalHodgeMass V H p S.hodge - nativeCycleMass V p S.cycle) *
      (nativeCycleMass V p K)⁻¹) • K

/-- Calibration along a genuinely null-class cycle preserves the entire real
cycle-class image of the original seed, not merely its cosmic shadow. -/
theorem massCalibratedCycle_class
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (K : codimensionCycles V.X p)
    (hK : H.cycleClass p K = 0) :
    H.cycleClass p (massCalibratedCycle S K) = S.hodge.1 := by
  simp [massCalibratedCycle, hK, S.class_eq]

/-- If the null-class calibration direction has nonzero native mass, the new
genuine cycle has exactly the prescribed classical Hodge coordinate mass. -/
theorem massCalibratedCycle_mass
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (K : codimensionCycles V.X p)
    (hK : nativeCycleMass V p K ≠ 0) :
    nativeCycleMass V p (massCalibratedCycle S K) =
      classicalHodgeMass V H p S.hodge := by
  simp only [massCalibratedCycle, map_add, map_smul, smul_eq_mul]
  rw [mul_assoc, inv_mul_cancel₀ hK, mul_one]
  abel

/-- The corrected native cycle is again a genuine nonzero synchronized
algebraic Hodge seed, with the same Hodge vector as the input seed. -/
noncomputable def massCalibratedSeed
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (K : codimensionCycles V.X p)
    (hK : H.cycleClass p K = 0) :
    NativeHodgeOrbitSeed (V := V) (H := H) (p := p) where
  cycle := massCalibratedCycle S K
  hodge := S.hodge
  hodge_ne_zero := S.hodge_ne_zero
  class_eq := massCalibratedCycle_class S K hK

/-- The corrected seed has the exact scalar balance required by the existing
explicit common-refinement gluing theorem. -/
theorem massCalibratedSeed_balanced
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (K : codimensionCycles V.X p)
    (hKclass : H.cycleClass p K = 0)
    (hKmass : nativeCycleMass V p K ≠ 0) :
    SeedFiberedMassBalance (massCalibratedSeed S K hKclass) := by
  change classicalHodgeMass V H p S.hodge =
    nativeCycleMass V p (massCalibratedCycle S K)
  exact (massCalibratedCycle_mass S K hKmass).symm

/-- **CONSTRUCTIVE ZERO-DEFECT SEED LIFT.**

At any actual native codimension-p point anchor, a null-class/nonzero-mass
direction constructs a finite fibered state representing exactly the original
Hodge seed while preserving its original cycle class. -/
theorem exists_massCalibrated_defectZero_jointSeed
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (K : codimensionCycles V.X p)
    (hKclass : H.cycleClass p K = 0)
    (hKmass : nativeCycleMass V p K ≠ 0)
    (x₀ : CodimensionPoint V.X p) :
    ∃ Φ : FiberedNativeAddress V H p,
      fiberedHodgeClass (V := V) (H := H) (p := p) Φ = S.hodge
      ∧ toNativeCycle V H p Φ = massCalibratedCycle S K
      ∧ fiberedCycleClassDefect (V := V) (H := H) (p := p) Φ = 0 := by
  let T := massCalibratedSeed S K hKclass
  have hb : SeedFiberedMassBalance T :=
    massCalibratedSeed_balanced S K hKclass hKmass
  obtain ⟨Φ, hh, hn, hd⟩ :=
    (exists_defectZero_seedJointState_iff_massBalance T x₀).2 hb
  refine ⟨Φ, ?_, ?_, hd⟩
  · simpa [T, massCalibratedSeed] using
      seedJointState_hodgeFace T Φ hh
  · simpa [T, massCalibratedSeed] using
      seedJointState_nativeFace T Φ hn

/-- **UNCONDITIONAL NATIVE-MASS CALIBRATION DICHOTOMY.**

At a fixed weight with at least one native point, either mass is already
well-defined on actual cohomological cycle classes, OR every existing
synchronized algebraic seed admits an exact finite zero-defect representation.

The conclusion does not generate nonalgebraic Hodge target sheets. It resolves
the scalar gluing barrier independently of the stronger projective two-step
Lefschetz target-realization problem. -/
theorem kernelLaw_or_allSynchronizedSeeds_have_defectZero_jointState
    (x₀ : CodimensionPoint V.X p) :
    NativeMassKernelLawAtWeight (V := V) (H := H) (p := p)
      ∨ ∀ S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p),
        ∃ Φ : FiberedNativeAddress V H p,
          fiberedHodgeClass (V := V) (H := H) (p := p) Φ = S.hodge
          ∧ fiberedCycleClassDefect (V := V) (H := H) (p := p) Φ = 0 := by
  classical
  by_cases hker : NativeMassKernelLawAtWeight (V := V) (H := H) (p := p)
  · exact Or.inl hker
  · right
    have hK : ∃ K : codimensionCycles V.X p,
        H.cycleClass p K = 0 ∧ nativeCycleMass V p K ≠ 0 := by
      by_contra hn
      apply hker
      intro K hz
      by_contra hm
      exact hn ⟨K, hz, hm⟩
    obtain ⟨K, hz, hm⟩ := hK
    intro S
    obtain ⟨Φ, hface, _, hdef⟩ :=
      exists_massCalibrated_defectZero_jointSeed S K hz hm x₀
    exact ⟨Φ, hface, hdef⟩

#check NativeMassKernelLawAtWeight
#check massCalibratedCycle
#check massCalibratedCycle_class
#check massCalibratedCycle_mass
#check massCalibratedSeed
#check massCalibratedSeed_balanced
#check exists_massCalibrated_defectZero_jointSeed
#check kernelLaw_or_allSynchronizedSeeds_have_defectZero_jointState

#print axioms massCalibratedCycle_class
#print axioms massCalibratedCycle_mass
#print axioms exists_massCalibrated_defectZero_jointSeed
#print axioms kernelLaw_or_allSynchronizedSeeds_have_defectZero_jointState

end GSTClassicalHodgeKernelMassCalibration
