import Mathlib

/-!
# GST unbounded geometric primitive rank from native intersection detectors

This abstract Q-linear result applies to arbitrary FINITE families of actual
algebraic primitive classes on an arbitrary Hodge fiber. Unlike the old
single-operator Gaussian CM orbit (rank <= 2), an arbitrary number of
separately constructed geometric classes can be proved independent by an
exact diagonal pairing certificate.

For example, blow up P^4 along any finite collection of mutually disjoint
smooth genus-positive curves. Each exceptional component has an independently
realized primitive algebraic class, and its own transverse Gysin intersection
detector. Disjoint exceptional supports make the detector off-diagonals zero,
while the diagonal detector is -m for an ample divisor mh-E with m>0.

This file proves the uniform rational finite-rank argument from explicit
pairing identities. Existence of the disjoint curves, their blowups and
their genuine Hodge/cycle-class pairings remains a separately established
geometric input, never an assumed target algebraicity statement.
-/

set_option maxHeartbeats 2000000
noncomputable section

namespace GSTBlowupArbitraryRankDetector

variable {ι W C : Type*}
  [Fintype ι] [DecidableEq ι]
  [AddCommGroup W] [Module ℚ W]
  [AddCommGroup C] [Module ℚ C]

/-- A prescribed exact diagonal geometric charge pairing. The geometric
operators being tested are actual rational-linear Betti intersection
measurements; the fields do not assert target Hodge surjectivity. -/
def ExactDiagonalGeometricDetectors
    (ell : ι → W →ₗ[ℚ] ℚ)
    (classes : ι → W) (charge : ℚ) : Prop :=
  ∀ i j, ell i (classes j) = if i = j then charge else 0

/-- Every finite native rank can be recovered from geometric readouts:
the pairing of the j-th class with the i-th detector annihilates all other
directions exactly, without approximate numerical determinant estimates. -/
theorem geometric_detector_exact_coefficients
    (ell : ι → W →ₗ[ℚ] ℚ)
    (classes : ι → W)
    (charge : ℚ)
    (hdiag : ExactDiagonalGeometricDetectors ell classes charge)
    (coeff : ι → ℚ) (i : ι) :
    ell i (∑ j, coeff j • classes j) = coeff i * charge := by
  classical
  calc
    ell i (∑ j, coeff j • classes j) =
      ∑ j, coeff j * (if i = j then charge else 0) := by
        simp only [map_sum, map_smul, smul_eq_mul]
        apply Finset.sum_congr rfl
        intro j _
        rw [hdiag i j]
    _ = coeff i * charge := by
      simp [mul_ite, Finset.sum_ite_eq', eq_comm]

/-- The exact diagonal pairing proves NO nontrivial rational relation
among ANY finite number of geometric classes, if charge != 0. -/
theorem geometric_detector_coefficients_vanish
    (ell : ι → W →ₗ[ℚ] ℚ)
    (classes : ι → W)
    (charge : ℚ)
    (hdiag : ExactDiagonalGeometricDetectors ell classes charge)
    (hcharge : charge ≠ 0)
    (coeff : ι → ℚ)
    (hz : (∑ j, coeff j • classes j) = 0) :
    ∀ i, coeff i = 0 := by
  intro i
  have hr := geometric_detector_exact_coefficients
    ell classes charge hdiag coeff i
  rw [hz, map_zero] at hr
  exact (mul_eq_zero.mp hr.symm).resolve_right hcharge

/-- Semantic connection to actual algebraic-cycle carriers C:
linear combinations of actual source cycles have independent genuine
cohomology classes under a separately certified geometric pairing. -/
theorem native_cycles_are_rationally_independent
    (cl : C →ₗ[ℚ] W)
    (ell : ι → W →ₗ[ℚ] ℚ)
    (cycles : ι → C)
    (charge : ℚ)
    (hdiag : ExactDiagonalGeometricDetectors ell (fun i => cl (cycles i)) charge)
    (hcharge : charge ≠ 0)
    (coeff : ι → ℚ)
    (hzero : cl (∑ j, coeff j • cycles j) = 0) :
    ∀ i, coeff i = 0 := by
  have hsum : (∑ j, coeff j • cl (cycles j)) = 0 := by
    simpa [map_sum, map_smul] using hzero
  exact geometric_detector_coefficients_vanish
    ell (fun i => cl (cycles i)) charge hdiag hcharge coeff hsum

#check ExactDiagonalGeometricDetectors
#check geometric_detector_exact_coefficients
#check geometric_detector_coefficients_vanish
#check native_cycles_are_rationally_independent
#print axioms native_cycles_are_rationally_independent

end GSTBlowupArbitraryRankDetector
