import waves.GSTNCohomologyV2

/-!
# Wave II V3: independent N-holes and nonlinear current mass firewall

Upgrade the user's original GST N-cohomology, retaining its actual tower
readouts. The V2 canonicalNCohoBasis ignores the basis index and cannot
establish independence. Here delta coordinates are actually independent.

A rational-linear native mass cannot be universally nonnegative unless
identically zero. Thus it is not the geometric mass functional on integral
rectifiable currents. This theorem blocks an illegitimate substitution
in the universal primitive Hodge residual fixed-homology-current target.

No theorem here asserts the universal Hodge conjecture or its equivalent
fixed-homology almost-calibrated current construction.
-/

set_option maxHeartbeats 10000000

namespace GSTNCohomologyV3

open GSTNCohomology
open GSTNCohomologyV2

/-- The rational linear space of independent N-hole coordinates. -/
abbrev HoleCoordinates (s : NShape) := Fin s.holes → ℚ

/-- Actual Kronecker delta coordinate attached to hole i. -/
def independentHoleBasis (s : NShape) (i : Fin s.holes) :
    HoleCoordinates s :=
  fun j => if i = j then 1 else 0

/-- Every rational N-cohomology channel vector has an exact coordinate
expansion against the honest Kronecker hole basis. -/
theorem independentHoleBasis_reconstruct
    (s : NShape) (coeff : HoleCoordinates s) (j : Fin s.holes) :
    (∑ i : Fin s.holes, coeff i * independentHoleBasis s i j) =
      coeff j := by
  classical
  simp [independentHoleBasis, mul_ite]

/-- The independent basis has unique coordinates: zero sum forces each
coefficient to vanish. -/
theorem independentHoleBasis_coefficients_unique
    (s : NShape) (coeff : HoleCoordinates s)
    (hzero : ∀ j : Fin s.holes,
      (∑ i : Fin s.holes, coeff i * independentHoleBasis s i j) = 0) :
    ∀ i : Fin s.holes, coeff i = 0 := by
  intro i
  have hi := hzero i
  rw [independentHoleBasis_reconstruct s coeff i] at hi
  exact hi

/-- V2's indexed readout vectors are constant in their would-be basis
index. The repaired basis is a separate, honest coordinate object. -/
theorem former_basis_is_constant_in_basis_index
    (R : Nat) (s : NShape) (N : Nat)
    (i j : Fin s.holes) :
    canonicalNCohoBasis R s N i =
      canonicalNCohoBasis R s N j := by
  rfl

/-- Actual original N-tower data inserted into the independent coordinates. -/
def towerHoleCoefficients (R : Nat) (s : NShape) :
    HoleCoordinates s :=
  fun i => (waveIIAmplitude R (s.channel i) : ℚ)

theorem towerHoleCoefficients_reconstructed
    (R : Nat) (s : NShape) (j : Fin s.holes) :
    (∑ i : Fin s.holes,
      towerHoleCoefficients R s i * independentHoleBasis s i j) =
        (waveIIAmplitude R (s.channel j) : ℚ) := by
  exact independentHoleBasis_reconstruct s _ j

/-- A rational-linear native signed mass nonnegative on all signed
rational cycles is zero. Geometric current mass must be nonlinear. -/
theorem nonnegative_linear_native_mass_must_vanish
    {N : Type*} [AddCommGroup N] [Module ℚ N]
    (mass : N →ₗ[ℚ] ℚ)
    (hnonnegative : ∀ z : N, 0 ≤ mass z)
    (z : N) : mass z = 0 := by
  have hp := hnonnegative z
  have hn := hnonnegative (-z)
  rw [map_neg] at hn
  exact le_antisymm (neg_nonneg.mp hn) hp

/-- Any nonzero signed linear mass becomes negative under one of the
two orientations, unlike nonnegative geometric mass. -/
theorem nonzero_linear_mass_has_negative_orientation
    {N : Type*} [AddCommGroup N] [Module ℚ N]
    (mass : N →ₗ[ℚ] ℚ)
    (z : N) (hne : mass z ≠ 0) :
    mass z < 0 ∨ mass (-z) < 0 := by
  rcases lt_trichotomy (mass z) 0 with hneg | hz | hpos
  · exact Or.inl hneg
  · exact False.elim (hne hz)
  · right
    rw [map_neg]
    exact neg_lt_zero.mpr hpos

#check independentHoleBasis_reconstruct
#check independentHoleBasis_coefficients_unique
#check former_basis_is_constant_in_basis_index
#check towerHoleCoefficients_reconstructed
#check nonnegative_linear_native_mass_must_vanish
#check nonzero_linear_mass_has_negative_orientation

#print axioms independentHoleBasis_reconstruct
#print axioms independentHoleBasis_coefficients_unique
#print axioms nonnegative_linear_native_mass_must_vanish

end GSTNCohomologyV3
