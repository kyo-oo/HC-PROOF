import GSTClassicalHodgeGenuineCycleClassGeometry
import GSTClassicalHodgeProjectiveDetectorVisibility

/-!
# GST CLASSICAL HODGE — PROJECTIVE TOMOGRAPHY READOUT

This module isolates the scalar interface between genuine projective geometry
and the existing GST tomography collision machinery.

For a native source cycle `Z`, a rational detector `ell`, and a genuine
projective kernel `K`, the projective readout is simply `ell` evaluated on the
cohomological projective image of `cl(Z)`.  The new genuine-geometry
irreducibility law says that whenever `cl(Z)` is nonzero and `ell` sees some
rational Hodge state, one such readout is nonzero.

Because the projective kernel sector is a rational span, any nonzero readout
can then be normalized to any prescribed rational scalar.  No target basis
cycle and no exact GST operator identity is used.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeProjectiveTomographyReadout

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeProjectiveCorrespondenceAlgebra
open GSTClassicalHodgeProjectiveCorrespondenceCosmicRealization
open GSTClassicalHodgeProjectiveDetectorVisibility
open GSTClassicalHodgeGenuineCycleClassGeometry

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Scalar projective readout of one genuine native source through one detector. -/
noncomputable def projectiveDetectorReadout
    (J : GenuineCycleClassGeometry V H)
    (p : Nat)
    (Z : codimensionCycles V.X p)
    (detector :
      RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ] ℚ)
    (K : ProjectiveNativeKernel V p) : ℚ :=
  detector
    ((projectiveCorrespondencePair J.spine K).cohomologyOperator
      (H.cycleClass p Z))

/-- Rational scaling of a genuine projective kernel scales its detector readout. -/
theorem projectiveDetectorReadout_scale
    (J : GenuineCycleClassGeometry V H)
    (p : Nat)
    (Z : codimensionCycles V.X p)
    (detector :
      RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ] ℚ)
    (q : ℚ)
    (K : ProjectiveNativeKernel V p) :
    projectiveDetectorReadout J p Z detector
        (scaleProjectiveKernel q K) =
      q * projectiveDetectorReadout J p Z detector K := by
  unfold projectiveDetectorReadout
  rw [scaled_projectivePair_on_cycleClass J.spine q K Z]
  simp

/-- Genuine projective-orbit irreducibility produces a nonzero readout. -/
theorem exists_nonzero_projectiveDetectorReadout
    (J : GenuineCycleClassGeometry V H)
    (p : Nat)
    (Z : codimensionCycles V.X p)
    (hZ : H.cycleClass p Z ≠ 0)
    (alpha : ClassicalHodgeFiber V H p)
    (detector :
      RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ] ℚ)
    (hdet : detector alpha.1 ≠ 0) :
    ∃ K : ProjectiveNativeKernel V p,
      projectiveDetectorReadout J p Z detector K ≠ 0 := by
  simpa [projectiveDetectorReadout] using
    J.orbitIrreducibility.separates p Z hZ alpha detector hdet

/-- Normalize one projective kernel so that its scalar readout equals `target`. -/
noncomputable def normalizeProjectiveReadout
    (J : GenuineCycleClassGeometry V H)
    (p : Nat)
    (Z : codimensionCycles V.X p)
    (detector :
      RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ] ℚ)
    (K : ProjectiveNativeKernel V p)
    (target : ℚ) : ProjectiveNativeKernel V p :=
  scaleProjectiveKernel
    (target / projectiveDetectorReadout J p Z detector K) K

/-- A nonzero source readout can be normalized to any desired rational value. -/
theorem normalizeProjectiveReadout_spec
    (J : GenuineCycleClassGeometry V H)
    (p : Nat)
    (Z : codimensionCycles V.X p)
    (detector :
      RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ] ℚ)
    (K : ProjectiveNativeKernel V p)
    (hK : projectiveDetectorReadout J p Z detector K ≠ 0)
    (target : ℚ) :
    projectiveDetectorReadout J p Z detector
        (normalizeProjectiveReadout J p Z detector K target) = target := by
  rw [projectiveDetectorReadout_scale]
  unfold normalizeProjectiveReadout
  field_simp [hK]

/-- Combined existence/normalization form used by finite GST tomography. -/
theorem exists_projectiveDetectorReadout_eq
    (J : GenuineCycleClassGeometry V H)
    (p : Nat)
    (Z : codimensionCycles V.X p)
    (hZ : H.cycleClass p Z ≠ 0)
    (alpha : ClassicalHodgeFiber V H p)
    (detector :
      RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ] ℚ)
    (hdet : detector alpha.1 ≠ 0)
    (target : ℚ) :
    ∃ K : ProjectiveNativeKernel V p,
      projectiveDetectorReadout J p Z detector K = target := by
  obtain ⟨K, hK⟩ :=
    exists_nonzero_projectiveDetectorReadout J p Z hZ alpha detector hdet
  exact ⟨normalizeProjectiveReadout J p Z detector K target,
    normalizeProjectiveReadout_spec J p Z detector K hK target⟩

#check projectiveDetectorReadout
#check projectiveDetectorReadout_scale
#check exists_nonzero_projectiveDetectorReadout
#check normalizeProjectiveReadout
#check normalizeProjectiveReadout_spec
#check exists_projectiveDetectorReadout_eq

#print axioms projectiveDetectorReadout_scale
#print axioms exists_nonzero_projectiveDetectorReadout
#print axioms normalizeProjectiveReadout_spec
#print axioms exists_projectiveDetectorReadout_eq

end GSTClassicalHodgeProjectiveTomographyReadout
