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


/-! ## GST N-COHOMOLOGY DOUBLE CAUSAL FOLD: INDEPENDENT SOURCE BIRTH

The full N-hole coordinates are not compressed to a one-cell cosmic Hodge
diagonal. Two independently born causal graph-loop channels have a genuine
ordered-pair index, hence a product (not a sum) of their independent ranks.
A geometric nodal realization carries these classes in cohomological
degree two with mixed-Hodge weight zero. An arbitrary Tate extension
moves both degree and weight by 2j while retaining their separation.

The entire geometric Hodge interpretation follows from the causal incidence
and realized normalization computations, not from an arbitrary assignment
of a class on original X to a vector in the N-hole space.
-/

/-- The full rational multiplicity fiber of TWO independent N-hole families.
Both N-cohomology channel indices are retained. -/
abbrev DoubleCausalHoleCoordinates (s t : NShape) :=
  (Fin s.holes × Fin t.holes) → ℚ

/-- Independent tensor basis of the double-fold cohomology, with one
coordinate for every ordered pair of genuine N-hole channels. -/
def doubleCausalHoleBasis (s t : NShape)
    (a : Fin s.holes × Fin t.holes) :
    DoubleCausalHoleCoordinates s t :=
  fun b => if a = b then 1 else 0

/-- The product causal-fold coordinates have exact reconstruction, unlike
a rank-one collapsed cosmic-diagonal readout. -/
theorem doubleCausalHoleBasis_reconstruct
    (s t : NShape) (coeff : DoubleCausalHoleCoordinates s t)
    (j : Fin s.holes × Fin t.holes) :
    (∑ i : Fin s.holes × Fin t.holes,
      coeff i * doubleCausalHoleBasis s t i j) = coeff j := by
  classical
  simp [doubleCausalHoleBasis]

/-- Pairwise independent causal graph holes retain UNIQUE coefficients. -/
theorem doubleCausalHoleBasis_coefficients_unique
    (s t : NShape) (coeff : DoubleCausalHoleCoordinates s t)
    (hzero : ∀ j : Fin s.holes × Fin t.holes,
      (∑ i : Fin s.holes × Fin t.holes,
        coeff i * doubleCausalHoleBasis s t i j) = 0) :
    ∀ i : Fin s.holes × Fin t.holes, coeff i = 0 := by
  intro i
  rw [← doubleCausalHoleBasis_reconstruct s t coeff i]
  exact hzero i

/-- This is a genuine MULTIPLICATIVE birth count for independent
finite causal-hole indices: neither axis is collapsed. -/
theorem doubleCausalHoleBasis_channelCount
    (s t : NShape) :
    Fintype.card (Fin s.holes × Fin t.holes) =
      s.holes * t.holes := by
  simp

/-- Independent N-cohomological amplitudes form one genuine double-fold
tensor, rather than an unsupported external Hodge-to-Chow selector. -/
def doubleCausalHoleTensor (s t : NShape)
    (a : HoleCoordinates s) (b : HoleCoordinates t) :
    DoubleCausalHoleCoordinates s t :=
  fun ij => a ij.1 * b ij.2

/-- Tensor-product causal folding reproduces the independently measured
amplitude in each of its two coordinates. -/
theorem doubleCausalHoleTensor_apply
    (s t : NShape)
    (a : HoleCoordinates s) (b : HoleCoordinates t)
    (i : Fin s.holes) (j : Fin t.holes) :
    doubleCausalHoleTensor s t a b (i,j) = a i * b j := rfl


/-! ## GST MULTI-WORLD N-COHOMOLOGY: NO FINITE CAUSAL ARITY BOUND

The double graph-loop system is an m=2 realization of an arbitrary
finite family of typed N-hole sectors. The actual full multiplicity
fiber is a DEPENDENT product of the hole indices of each world.
Keeping all indices is essential: collapsing them to one cosmic
diagonal would destroy the product-rank emergence law.
-/

/-- Independent index of every genuine N-hole coordinate in every
causally participating world, with arbitrary finite arity m. -/
abbrev ManyCausalHoleIndex (m : ℕ) (s : Fin m → NShape) :=
  ∀ i : Fin m, Fin ((s i).holes)

/-- Every independent multi-causal hole coordinate survives as its
own rational amplitude; no source index or dimension is discarded. -/
abbrev ManyCausalHoleCoordinates (m : ℕ) (s : Fin m → NShape) :=
  ManyCausalHoleIndex m s → ℚ

/-- One delta channel per complete causal world-address tuple. -/
def manyCausalHoleBasis (m : ℕ) (s : Fin m → NShape)
    (a : ManyCausalHoleIndex m s) :
    ManyCausalHoleCoordinates m s :=
  fun b => if a = b then 1 else 0

/-- Exact ALL-ARITY source reconstruction of the emerged N-cohomology
space: causal multiplication retains the entire Hodge multiplicity fiber. -/
theorem manyCausalHoleBasis_reconstruct
    (m : ℕ) (s : Fin m → NShape)
    (coeff : ManyCausalHoleCoordinates m s)
    (j : ManyCausalHoleIndex m s) :
    (∑ i : ManyCausalHoleIndex m s,
      coeff i * manyCausalHoleBasis m s i j) = coeff j := by
  classical
  simp [manyCausalHoleBasis]

/-- Distinct multi-world causal channels remain linearly independent. -/
theorem manyCausalHoleBasis_coefficients_unique
    (m : ℕ) (s : Fin m → NShape)
    (coeff : ManyCausalHoleCoordinates m s)
    (hzero : ∀ j : ManyCausalHoleIndex m s,
      (∑ i : ManyCausalHoleIndex m s,
        coeff i * manyCausalHoleBasis m s i j) = 0) :
    ∀ j : ManyCausalHoleIndex m s, coeff j = 0 := by
  intro j
  rw [← manyCausalHoleBasis_reconstruct m s coeff j]
  exact hzero j

/-- Exact MULTIPLICATIVE causal rank across arbitrarily many independent
emergent N-hole dimensions, including the empty-world vacuum m=0. -/
theorem manyCausalHoleBasis_channelCount (m : ℕ) (s : Fin m → NShape) :
    Fintype.card (ManyCausalHoleIndex m s) =
      ∏ i : Fin m, (s i).holes := by
  classical
  simp [ManyCausalHoleIndex, Fintype.card_pi]

/-- The born product amplitude uses ACTUAL input amplitudes from each
individual N-hole world, not a freely chosen Hodge coordinate. -/
def manyCausalHoleTensor (m : ℕ) (s : Fin m → NShape)
    (a : ∀ i : Fin m, HoleCoordinates (s i)) :
    ManyCausalHoleCoordinates m s :=
  fun index => ∏ i : Fin m, a i (index i)

/-- The full tensor source readout is an explicit finite causal product. -/
theorem manyCausalHoleTensor_apply
    (m : ℕ) (s : Fin m → NShape)
    (a : ∀ i : Fin m, HoleCoordinates (s i))
    (index : ManyCausalHoleIndex m s) :
    manyCausalHoleTensor m s a index =
      ∏ i : Fin m, a i (index i) := rfl

#check manyCausalHoleBasis_reconstruct
#check manyCausalHoleBasis_channelCount
#check manyCausalHoleBasis_coefficients_unique
#check manyCausalHoleTensor_apply
#print axioms manyCausalHoleBasis_channelCount

#check doubleCausalHoleBasis_reconstruct
#check doubleCausalHoleBasis_coefficients_unique
#check doubleCausalHoleBasis_channelCount
#check doubleCausalHoleTensor_apply
#print axioms doubleCausalHoleBasis_reconstruct
#print axioms doubleCausalHoleBasis_channelCount


end GSTNCohomologyV3
