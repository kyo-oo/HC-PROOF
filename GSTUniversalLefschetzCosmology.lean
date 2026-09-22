import Mathlib
import Mathlib.RingTheory.Nilpotent.Basic
import GSTUniversalLefschetzDynamics
import GSTWorldPoincareDuality

/-!
# GST UNIVERSAL LEFSCHETZ COSMOLOGY

This file is the operator-algebra integration layer of the upgraded HC
cosmology.

The grading and duality parts are deliberately sourced from their stronger
parent modules:

* GSTGradedWorldAlgebra
* GSTUniversalLefschetzDynamics
* GSTWorldPoincareDuality

The genuinely new structure here is the linear endomorphism algebra:

    H := one-step digit transport
    V := one-step carry transport
    L := H + V

on every A x B world.

The powers of H and V are the native arbitrary-depth transports, H and V
commute, and L obeys the exact commuting binomial calculus.  The old
4 x 3 Crown is one specialization.
-/

set_option maxHeartbeats 20000000
set_option maxRecDepth 1000000

namespace GSTUniversalLefschetzCosmology

open GSTWorldCosmology
open GSTGradedWorldAlgebra
open GSTUniversalLefschetzDynamics
open GSTWorldPoincareDuality

variable {A B : Nat}

/-! ## 1. Native axis operators as integer-linear endomorphisms -/

noncomputable def digitEndo (A B : Nat) :
    Module.End ℤ (WorldCoef A B) where
  toFun := digitShiftN 1
  map_add' := by
    intro f g
    funext c
    change digitShiftN 1 (f + g) c =
      digitShiftN 1 f c + digitShiftN 1 g c
    unfold digitShiftN
    split_ifs <;> rfl
  map_smul' := by
    intro z f
    funext c
    change digitShiftN 1 (z • f) c =
      z • digitShiftN 1 f c
    unfold digitShiftN
    split_ifs <;> simp

noncomputable def carryEndo (A B : Nat) :
    Module.End ℤ (WorldCoef A B) where
  toFun := carryShiftN 1
  map_add' := by
    intro f g
    funext c
    change carryShiftN 1 (f + g) c =
      carryShiftN 1 f c + carryShiftN 1 g c
    unfold carryShiftN
    split_ifs <;> simp
  map_smul' := by
    intro z f
    funext c
    change carryShiftN 1 (z • f) c =
      z • carryShiftN 1 f c
    unfold carryShiftN
    split_ifs <;> rfl

@[simp]
theorem digitEndo_apply (g : WorldCoef A B) :
    digitEndo A B g = digitShiftN 1 g :=
  rfl

@[simp]
theorem carryEndo_apply (g : WorldCoef A B) :
    carryEndo A B g = carryShiftN 1 g :=
  rfl

/-- H^n is exactly native digit transport by n layers. -/
theorem digitEndo_pow_apply (n : Nat) (g : WorldCoef A B) :
    ((digitEndo A B)^n) g = digitShiftN n g := by
  induction n generalizing g with
  | zero =>
      simp [digitShiftN_zero]
  | succ n ih =>
      rw [pow_succ, Module.End.mul_apply]
      change ((digitEndo A B)^n) (digitShiftN 1 g) =
        digitShiftN (n+1) g
      rw [ih]
      simpa using digitShiftN_add n 1 g

/-- V^n is exactly native carry transport by n layers. -/
theorem carryEndo_pow_apply (n : Nat) (g : WorldCoef A B) :
    ((carryEndo A B)^n) g = carryShiftN n g := by
  induction n generalizing g with
  | zero =>
      simp [carryShiftN_zero]
  | succ n ih =>
      rw [pow_succ, Module.End.mul_apply]
      change ((carryEndo A B)^n) (carryShiftN 1 g) =
        carryShiftN (n+1) g
      rw [ih]
      simpa using carryShiftN_add n 1 g

/-- H is nilpotent at digit depth B. -/
theorem digitEndo_pow_depth :
    (digitEndo A B)^B = 0 := by
  apply LinearMap.ext
  intro g
  rw [digitEndo_pow_apply]
  exact digit_boundary_extinction g

/-- V is nilpotent at carry depth A. -/
theorem carryEndo_pow_depth :
    (carryEndo A B)^A = 0 := by
  apply LinearMap.ext
  intro g
  rw [carryEndo_pow_apply]
  exact carry_boundary_extinction g

/-- The two native axes commute as genuine endomorphisms. -/
theorem digit_carry_commute :
    Commute (digitEndo A B) (carryEndo A B) := by
  apply LinearMap.ext
  intro g
  change digitShiftN 1 (carryShiftN 1 g) =
    carryShiftN 1 (digitShiftN 1 g)
  exact axes_commute 1 1 g

/-! ## 2. Universal Lefschetz endomorphism -/

noncomputable def lefschetzEndo (A B : Nat) :
    Module.End ℤ (WorldCoef A B) :=
  digitEndo A B + carryEndo A B

@[simp]
theorem lefschetzEndo_apply (g : WorldCoef A B) :
    lefschetzEndo A B g = worldLefschetz g := by
  rfl

/-- Exact commuting binomial calculus for every Lefschetz power. -/
theorem lefschetz_binomial (n : Nat) :
    (lefschetzEndo A B)^n =
      ∑ m ∈ Finset.range (n+1),
        (digitEndo A B)^m *
          (carryEndo A B)^(n-m) *
          (n.choose m : Module.End ℤ (WorldCoef A B)) := by
  exact (digit_carry_commute (A:=A) (B:=B)).add_pow n

/-- The endomorphism form of the dimension-derived Lefschetz ceiling. -/
theorem lefschetz_pow_boundary :
    (lefschetzEndo A B)^(A+B-1) = 0 := by
  have h :=
    (digit_carry_commute (A:=A) (B:=B)).add_pow_add_eq_zero_of_pow_eq_zero
      (digitEndo_pow_depth (A:=A) (B:=B))
      (carryEndo_pow_depth (A:=A) (B:=B))
  simpa [lefschetzEndo, Nat.add_comm] using h

theorem lefschetz_pow_zero_of_boundary_le
    (n : Nat) (h : A+B-1 ≤ n) :
    (lefschetzEndo A B)^n = 0 :=
  pow_eq_zero_of_le h lefschetz_pow_boundary

/-! ## 3. Canonical grading interface

These names preserve the public interface of the earlier experimental file,
but the proofs now come from GSTGradedWorldAlgebra.
-/

abbrev sectorProj (k : Nat) (g : WorldCoef A B) : WorldCoef A B :=
  worldSectorProj k g

theorem sectorProj_idempotent (k : Nat) (g : WorldCoef A B) :
    sectorProj k (sectorProj k g) = sectorProj k g :=
  worldSectorProj_idempotent k g

theorem sectorProj_orthogonal
    (j k : Nat) (hjk : j ≠ k) (g : WorldCoef A B) :
    sectorProj j (sectorProj k g) = fun _ => 0 :=
  worldSectorProj_orthogonal j k hjk g

theorem sectorProj_sum (g : WorldCoef A B) :
    (fun c => ∑ k ∈ Finset.range (A+B), sectorProj k g c) = g :=
  worldSectorProj_sum g

theorem digitShift_respects_sector
    (k n : Nat) (g : WorldCoef A B) :
    digitShiftN n (sectorProj k g) =
      sectorProj (k+n) (digitShiftN n g) :=
  digitShiftN_respects_degree n k g

theorem carryShift_respects_sector
    (k n : Nat) (g : WorldCoef A B) :
    carryShiftN n (sectorProj k g) =
      sectorProj (k+n) (carryShiftN n g) :=
  carryShiftN_respects_degree n k g

/-- L raises total degree by exactly one. -/
theorem lefschetz_respects_sector
    (k : Nat) (g : WorldCoef A B) :
    lefschetzEndo A B (sectorProj k g) =
      sectorProj (k+1) (lefschetzEndo A B g) := by
  change worldLefschetz (worldSectorProj k g) =
    worldSectorProj (k+1) (worldLefschetz g)
  exact worldLefschetz_respects_degree k g

/-! ## 4. Canonical Poincare interface

Again, the mathematics is sourced from the stronger parent duality module.
-/

abbrev complementCell (c : WorldCell A B) : WorldCell A B :=
  worldDual c

theorem complementCell_involutive (c : WorldCell A B) :
    complementCell (complementCell c) = c :=
  worldDual_involutive c

abbrev basis (c : WorldCell A B) : WorldCoef A B :=
  worldBasis c

abbrev topPairing (f g : WorldCoef A B) : ℤ :=
  worldTopPairing f g

theorem topPairing_basis_right
    (f : WorldCoef A B) (c : WorldCell A B) :
    topPairing f (basis (complementCell c)) = f c :=
  worldTopPairing_pick_left f c

theorem topPairing_basis_left
    (g : WorldCoef A B) (c : WorldCell A B) :
    topPairing (basis c) g = g (complementCell c) := by
  simpa only [worldDual_involutive] using
    (worldTopPairing_pick_right g (complementCell c))

theorem topPairing_nondegenerate_left
    (f : WorldCoef A B)
    (h : ∀ g : WorldCoef A B, topPairing f g = 0) :
    f = fun _ => 0 :=
  worldTopPairing_nondegenerate_left f h

theorem topPairing_nondegenerate_right
    (g : WorldCoef A B)
    (h : ∀ f : WorldCoef A B, topPairing f g = 0) :
    g = fun _ => 0 :=
  worldTopPairing_nondegenerate_right g h

theorem topPairing_basis_basis
    (c d : WorldCell A B) :
    topPairing (basis c) (basis d) =
      if d = complementCell c then 1 else 0 := by
  rw [topPairing_basis_left]
  by_cases h : complementCell c = d
  · subst d
    simp [basis, worldBasis]
  · have h' : d ≠ complementCell c := Ne.symm h
    simp [basis, worldBasis, h, h']

/-! ## 5. The historical HC rectangle is one specialization -/

theorem hc_digit_nilpotence :
    (digitEndo 4 3)^3 = 0 :=
  digitEndo_pow_depth

theorem hc_carry_nilpotence :
    (carryEndo 4 3)^4 = 0 :=
  carryEndo_pow_depth

theorem hc_lefschetz_nilpotence :
    (lefschetzEndo 4 3)^6 = 0 := by
  simpa using (lefschetz_pow_boundary (A:=4) (B:=3))

/-- Unified operator/graded/duality crown. -/
theorem universal_lefschetz_crown :
    (∀ A B : Nat,
      Commute (digitEndo A B) (carryEndo A B))
    ∧ (∀ A B : Nat,
      (digitEndo A B)^B = 0)
    ∧ (∀ A B : Nat,
      (carryEndo A B)^A = 0)
    ∧ (∀ A B : Nat,
      (lefschetzEndo A B)^(A+B-1) = 0)
    ∧ (∀ A B k : Nat, ∀ g : WorldCoef A B,
      sectorProj k (sectorProj k g) = sectorProj k g) := by
  exact ⟨
    fun A B => digit_carry_commute,
    fun A B => digitEndo_pow_depth,
    fun A B => carryEndo_pow_depth,
    fun A B => lefschetz_pow_boundary,
    fun A B k g => sectorProj_idempotent k g⟩

#check digitEndo_pow_apply
#check carryEndo_pow_apply
#check digit_carry_commute
#check lefschetz_binomial
#check lefschetz_pow_boundary
#check sectorProj_sum
#check digitShift_respects_sector
#check carryShift_respects_sector
#check lefschetz_respects_sector
#check complementCell_involutive
#check topPairing_nondegenerate_left
#check topPairing_nondegenerate_right
#check topPairing_basis_basis
#check hc_lefschetz_nilpotence
#check universal_lefschetz_crown

#print axioms lefschetz_binomial
#print axioms lefschetz_pow_boundary
#print axioms sectorProj_sum
#print axioms lefschetz_respects_sector
#print axioms topPairing_nondegenerate_left
#print axioms topPairing_basis_basis
#print axioms universal_lefschetz_crown

end GSTUniversalLefschetzCosmology
