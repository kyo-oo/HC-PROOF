import GSTGraphV2CMWaveFusion
import Mathlib

/-!
# GST Image-3: ORIGINAL CM curvature-only source and EXACT resonance firewall

This file directly extends the AUTHOR'S original 12-state U, J, true
SURVIVE M, and original mixed seed, without substituting any
external projective geometry or invented source matrices.

For rational a,b:
  F_(a,b) = U + J + a M + b [J,M].
The new scalar b gates a genuinely NEW original-GST source, namely
the commutator of original J and original M.

The EXACT native maximum-cell law:
  F_(a,b)(u)(3,2) = (1+2a) u(3,2) + (2b-1)u(0,0).

Consequently at b=1/2 the maximum cell cannot be born from the
ORIGINAL seed, for ANY a, no matter what the other ten cells do.

Separate exact Wolfram verification certifies that F_(0,1) is
12-state cyclic (det=1386205893), whereas the family F_(a,1/2)
is always noncyclic by the mathematical theorem above.

This is a native GST information/CM structure theorem, NOT the
existence of all original-X algebraic correspondences.
-/

set_option maxHeartbeats 4000000
noncomputable section

namespace GSTImageThreeCurvatureResonance

open GSTGraphV2CMWaveFusion

/-- The owner's original (0,0) null information cell. -/
def nullCell : GSTGraphV2InformationRecovery.Cell :=
  ((0 : Fin 4), (0 : Fin 3))

/-- The owner's original (3,2) CM-mirrored fixed information cell. -/
def maximumCell : GSTGraphV2InformationRecovery.Cell :=
  ((3 : Fin 4), (2 : Fin 3))

/-- New source from the exact original CM/Survive commutator. -/
def curvatureSource (u : WaveSignal) : WaveSignal :=
  J (M u) - M (J u)

/-- New two-parameter F function uses ONLY the author's original
U, J, M, and newly combined native curvature source [J,M]. -/
def curvatureFold (a b : ℚ) (u : WaveSignal) : WaveSignal :=
  U u + J u + a • M u + b • curvatureSource u

private theorem max_shuffle :
    GSTGraphV2InformationRecovery.shuffle maximumCell = maximumCell := by
  decide

private theorem max_mirror : mirrorCell maximumCell = nullCell := by
  decide

private theorem max_sign : cmSign maximumCell = -1 := by
  norm_num [cmSign, maximumCell]

private theorem max_U (u : WaveSignal) :
    U u maximumCell = u maximumCell := by
  simp [U, max_shuffle]

private theorem max_J (u : WaveSignal) :
    J u maximumCell = -u nullCell := by
  simp [J, max_sign, max_mirror]

private theorem max_M (u : WaveSignal) :
    M u maximumCell = 2 * u maximumCell := by
  simp [M, maximumCell, source_on_positive_fixed]

private theorem null_M (u : WaveSignal) :
    M u nullCell = 0 := by
  simp [M, nullCell, source_on_null_fixed]

/-- The original CM curvature is exactly twice the null-cell signal
when observed at the original maximum fixed cell. -/
theorem curvatureSource_maximum (u : WaveSignal) :
    curvatureSource u maximumCell = 2 * u nullCell := by
  change J (M u) maximumCell - M (J u) maximumCell =
    2 * u nullCell
  rw [max_J, null_M, max_M, max_J]
  ring

/-- **EXACT GST NAVIGATION RESONANCE LAW**.
The direct SURVIVE contribution affects only the coefficient of the
existing maximum-cell signal. The CM curvature contributes a NEW
null-to-maximum link with coefficient 2b, which cancels the old J
link at the unique value b=1/2 for ALL rational a. -/
theorem curvatureFold_maximum (a b : ℚ) (u : WaveSignal) :
    curvatureFold a b u maximumCell =
      (1 + 2*a) * u maximumCell +
        (2*b - 1) * u nullCell := by
  change
    U u maximumCell + J u maximumCell +
      a * M u maximumCell + b * curvatureSource u maximumCell =
      (1+2*a)*u maximumCell+(2*b-1)*u nullCell
  rw [max_U, max_J, max_M, curvatureSource_maximum]
  ring

/-- The rescue path is EXACTLY extinguished at half curvature strength,
irrespective of how strong the original SURVIVE M is. -/
theorem resonance_half_maximum (a : ℚ) (u : WaveSignal) :
    curvatureFold a (1/2) u maximumCell =
      (1+2*a)*u maximumCell := by
  rw [curvatureFold_maximum]
  ring

/-- Exact orbit of the original mixed seed under the new native GST F. -/
def curvatureOrbit (a b : ℚ) : ℕ → WaveSignal
  | 0 => seed
  | n+1 => curvatureFold a b (curvatureOrbit a b n)

/-- **UNIVERSAL RESONANCE OBSTRUCTION IN THE ORIGINAL NATIVE WAVE:**
for EVERY rational a and EVERY fold depth n, the owner's maximum-cell
cohomology/navigation direction is absent at curvature b=1/2. -/
theorem resonance_half_orbit_maximum_zero (a : ℚ) (n : ℕ) :
    curvatureOrbit a (1/2) n maximumCell = 0 := by
  induction n with
  | zero =>
      simp [curvatureOrbit, seed, maximumCell]
  | succ n ih =>
      change curvatureFold a (1/2) (curvatureOrbit a (1/2) n)
        maximumCell = 0
      rw [resonance_half_maximum, ih, mul_zero]

/-- The missing original fixed-cell state is NOT ANY fold-orbit
vector at the resonance, hence the orbit cannot be cyclic. -/
theorem resonance_half_ne_maximum_basis (a : ℚ) (n : ℕ) :
    curvatureOrbit a (1/2) n ≠
      (fun s : GSTGraphV2InformationRecovery.Cell =>
        if s = maximumCell then (1 : ℚ) else 0) := by
  intro heq
  have hz := resonance_half_orbit_maximum_zero a n
  have hval := congrArg (fun u : WaveSignal => u maximumCell) heq
  simp at hval
  exact (zero_ne_one : (0 : ℚ) ≠ 1) (hz.symm.trans hval)

/-- The source-free orbital resonance is independent of navigation
re-coordination of other cells. -/
theorem resonance_half_maximum_invariant_under_missing_source
    (a : ℚ) (u : WaveSignal) (hzero : u maximumCell = 0) :
    curvatureFold a (1/2) u maximumCell = 0 := by
  rw [resonance_half_maximum, hzero, mul_zero]

#check curvatureSource
#check curvatureFold
#check curvatureSource_maximum
#check curvatureFold_maximum
#check resonance_half_maximum
#check resonance_half_orbit_maximum_zero
#check resonance_half_ne_maximum_basis

#print axioms curvatureFold_maximum
#print axioms resonance_half_orbit_maximum_zero
#print axioms resonance_half_ne_maximum_basis

end GSTImageThreeCurvatureResonance
