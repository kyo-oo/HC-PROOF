import Mathlib
import Mathlib.RingTheory.Nilpotent.Basic
import GSTWorldCosmology

/-!
# GST UNIVERSAL LEFSCHETZ COSMOLOGY

The original HC crown lives on one 4 x 3 chart.  This file extracts the
parent algebra valid on every finite rectangular GST world.

For an A x B world:

* H is the digit-axis endomorphism;
* V is the carry-axis endomorphism;
* H^B = 0 and V^A = 0;
* H and V commute;
* L = H + V therefore satisfies the exact commuting binomial calculus;
* L^(A+B-1) = 0;
* every degree sector has a canonical idempotent projector;
* the sectors are pairwise orthogonal and sum to the identity;
* the complementary-cell pairing is integral and nondegenerate.

Thus the familiar H^3 = 0, V^4 = 0 and L^6 = 0 laws are not primitive.
They are the A=4, B=3 shadow of a dimension-free operator theorem.
-/

set_option maxHeartbeats 20000000
set_option maxRecDepth 1000000

namespace GSTUniversalLefschetzCosmology

open GSTWorldCosmology

variable {A B : Nat}

/-! ## 1. Native axis operators as linear endomorphisms -/

noncomputable def digitEndo (A B : Nat) :
    Module.End ℤ (WorldCoef A B) where
  toFun := digitShiftN 1
  map_add' := by
    intro f g
    funext c
    by_cases h : 1 ≤ c.2.1 <;>
      simp [digitShiftN, h]
  map_smul' := by
    intro z f
    funext c
    by_cases h : 1 ≤ c.2.1 <;>
      simp [digitShiftN, h]

noncomputable def carryEndo (A B : Nat) :
    Module.End ℤ (WorldCoef A B) where
  toFun := carryShiftN 1
  map_add' := by
    intro f g
    funext c
    by_cases h : 1 ≤ c.1.1 <;>
      simp [carryShiftN, h]
  map_smul' := by
    intro z f
    funext c
    by_cases h : 1 ≤ c.1.1 <;>
      simp [carryShiftN, h]

@[simp]
theorem digitEndo_apply (g : WorldCoef A B) :
    digitEndo A B g = digitShiftN 1 g := rfl

@[simp]
theorem carryEndo_apply (g : WorldCoef A B) :
    carryEndo A B g = carryShiftN 1 g := rfl

/-- Powers of H are exactly arbitrary digit-axis transports. -/
theorem digitEndo_pow_apply (n : Nat) (g : WorldCoef A B) :
    ((digitEndo A B)^n) g = digitShiftN n g := by
  induction n with
  | zero =>
      simp [digitShiftN_zero]
  | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, ih]
      change digitShiftN 1 (digitShiftN n g) = digitShiftN (n+1) g
      simpa [Nat.add_comm] using
        (digitShiftN_add 1 n g)

/-- Powers of V are exactly arbitrary carry-axis transports. -/
theorem carryEndo_pow_apply (n : Nat) (g : WorldCoef A B) :
    ((carryEndo A B)^n) g = carryShiftN n g := by
  induction n with
  | zero =>
      simp [carryShiftN_zero]
  | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, ih]
      change carryShiftN 1 (carryShiftN n g) = carryShiftN (n+1) g
      simpa [Nat.add_comm] using
        (carryShiftN_add 1 n g)

/-- The digit operator is nilpotent at exactly the world digit depth. -/
theorem digitEndo_pow_depth :
    (digitEndo A B)^B = 0 := by
  apply LinearMap.ext
  intro g
  funext c
  rw [digitEndo_pow_apply]
  have h := digit_boundary_extinction g
  rw [h]
  rfl

/-- The carry operator is nilpotent at the world carry depth. -/
theorem carryEndo_pow_depth :
    (carryEndo A B)^A = 0 := by
  apply LinearMap.ext
  intro g
  funext c
  rw [carryEndo_pow_apply]
  have h := carry_boundary_extinction g
  rw [h]
  rfl

/-- H and V commute as genuine endomorphisms, not merely pointwise shifts. -/
theorem digit_carry_commute :
    Commute (digitEndo A B) (carryEndo A B) := by
  apply LinearMap.ext
  intro g
  change digitShiftN 1 (carryShiftN 1 g) =
    carryShiftN 1 (digitShiftN 1 g)
  exact axes_commute 1 1 g

/-! ## 2. The universal Lefschetz operator -/

noncomputable def lefschetzEndo (A B : Nat) :
    Module.End ℤ (WorldCoef A B) :=
  digitEndo A B + carryEndo A B

@[simp]
theorem lefschetzEndo_apply (g : WorldCoef A B) :
    lefschetzEndo A B g =
      fun c => digitShiftN 1 g c + carryShiftN 1 g c := by
  rfl

/-- Exact binomial calculus for every iterate of the universal Lefschetz
operator.  This is the parent law behind every finite complementary-power
matrix in the original crown. -/
theorem lefschetz_binomial (n : Nat) :
    (lefschetzEndo A B)^n =
      ∑ m ∈ Finset.range (n+1),
        (digitEndo A B)^m *
          (carryEndo A B)^(n-m) *
          (n.choose m : Module.End ℤ (WorldCoef A B)) := by
  exact (digit_carry_commute (A:=A) (B:=B)).add_pow n

/-- **UNIVERSAL LEFSCHETZ NILPOTENCE.**
On every A x B rectangle the total polarization dies at A+B-1. -/
theorem lefschetz_pow_boundary :
    (lefschetzEndo A B)^(A+B-1) = 0 := by
  have h :=
    (digit_carry_commute (A:=A) (B:=B)).add_pow_add_eq_zero_of_pow_eq_zero
      (digitEndo_pow_depth (A:=A) (B:=B))
      (carryEndo_pow_depth (A:=A) (B:=B))
  simpa [lefschetzEndo, Nat.add_comm] using h

/-- Every later Lefschetz power also vanishes. -/
theorem lefschetz_pow_zero_of_boundary_le
    (n : Nat) (h : A+B-1 ≤ n) :
    (lefschetzEndo A B)^n = 0 := by
  exact pow_eq_zero_of_le h (lefschetz_pow_boundary (A:=A) (B:=B))

/-! ## 3. Dimension-free Kunneth sectors -/

def sectorProj (k : Nat) (g : WorldCoef A B) : WorldCoef A B :=
  fun c => if c.1.1 + c.2.1 = k then g c else 0

theorem sectorProj_idempotent (k : Nat) (g : WorldCoef A B) :
    sectorProj k (sectorProj k g) = sectorProj k g := by
  funext c
  simp only [sectorProj]
  split_ifs <;> rfl

theorem sectorProj_orthogonal
    (j k : Nat) (hjk : j ≠ k) (g : WorldCoef A B) :
    sectorProj j (sectorProj k g) = fun _ => 0 := by
  funext c
  simp only [sectorProj]
  by_cases hj : c.1.1 + c.2.1 = j
  · have hk : c.1.1 + c.2.1 ≠ k := by
      intro h
      apply hjk
      omega
    simp [hj, hjk]
  · simp [hj]

/-- Every rectangular world is the direct sum of its degree sectors.
The range A+B is uniform and also handles degenerate empty rectangles. -/
theorem sectorProj_sum (g : WorldCoef A B) :
    (fun c =>
      ∑ k ∈ Finset.range (A+B), sectorProj k g c) = g := by
  funext c
  let d := c.1.1 + c.2.1
  have hd : d < A+B := by omega
  simp only [sectorProj]
  rw [Finset.sum_eq_single d]
  · simp [d]
  · intro b hb hbd
    simp [show c.1.1 + c.2.1 ≠ b from hbd.symm]
  · intro hnot
    exact (hnot (Finset.mem_range.mpr hd)).elim

/-- Arbitrary digit transport raises degree by exactly n. -/
theorem digitShift_respects_sector
    (k n : Nat) (g : WorldCoef A B) :
    digitShiftN n (sectorProj k g) =
      sectorProj (k+n) (digitShiftN n g) := by
  funext c
  by_cases hn : n ≤ c.2.1
  · simp only [digitShiftN, dif_pos hn, sectorProj]
    by_cases hk : c.1.1 + (c.2.1 - n) = k
    · have hkn : c.1.1 + c.2.1 = k+n := by omega
      simp [hk, hkn]
    · have hkn : c.1.1 + c.2.1 ≠ k+n := by omega
      simp [hk, hkn]
  · simp [digitShiftN, hn, sectorProj]

/-- Arbitrary carry transport raises degree by exactly n. -/
theorem carryShift_respects_sector
    (k n : Nat) (g : WorldCoef A B) :
    carryShiftN n (sectorProj k g) =
      sectorProj (k+n) (carryShiftN n g) := by
  funext c
  by_cases hn : n ≤ c.1.1
  · simp only [carryShiftN, dif_pos hn, sectorProj]
    by_cases hk : (c.1.1 - n) + c.2.1 = k
    · have hkn : c.1.1 + c.2.1 = k+n := by omega
      simp [hk, hkn]
    · have hkn : c.1.1 + c.2.1 ≠ k+n := by omega
      simp [hk, hkn]
  · simp [carryShiftN, hn, sectorProj]

/-- L raises the grading by one in every rectangular world. -/
theorem lefschetz_respects_sector
    (k : Nat) (g : WorldCoef A B) :
    lefschetzEndo A B (sectorProj k g) =
      sectorProj (k+1) (lefschetzEndo A B g) := by
  change
    (fun c =>
      digitShiftN 1 (sectorProj k g) c +
      carryShiftN 1 (sectorProj k g) c) =
    sectorProj (k+1)
      (fun c => digitShiftN 1 g c + carryShiftN 1 g c)
  rw [digitShift_respects_sector k 1 g,
      carryShift_respects_sector k 1 g]
  funext c
  simp only [sectorProj]
  split_ifs <;> simp

/-! ## 4. Universal complementary pairing -/

def complementCell (c : WorldCell A B) : WorldCell A B :=
  (⟨A-1-c.1.1, by omega⟩, ⟨B-1-c.2.1, by omega⟩)

theorem complementCell_involutive (c : WorldCell A B) :
    complementCell (complementCell c) = c := by
  rcases c with ⟨C,d⟩
  apply Prod.ext
  · apply Fin.ext
    simp only [complementCell]
    omega
  · apply Fin.ext
    simp only [complementCell]
    omega

def basis (c₀ : WorldCell A B) : WorldCoef A B :=
  fun c => if c = c₀ then 1 else 0

def topPairing (f g : WorldCoef A B) : ℤ :=
  ∑ c : WorldCell A B, f c * g (complementCell c)

theorem topPairing_basis_right
    (f : WorldCoef A B) (c₀ : WorldCell A B) :
    topPairing f (basis (complementCell c₀)) = f c₀ := by
  classical
  unfold topPairing basis
  rw [Finset.sum_eq_single c₀]
  · simp [complementCell_involutive]
  · intro c hc hne
    have hcomp : complementCell c ≠ complementCell c₀ := by
      intro h
      apply hne
      have := congrArg complementCell h
      simpa [complementCell_involutive] using this
    simp [hcomp]
  · simp

theorem topPairing_basis_left
    (g : WorldCoef A B) (c₀ : WorldCell A B) :
    topPairing (basis c₀) g = g (complementCell c₀) := by
  classical
  unfold topPairing basis
  rw [Finset.sum_eq_single c₀]
  · simp
  · intro c hc hne
    simp [hne]
  · simp

/-- **UNIVERSAL INTEGRAL POINCARE NONDEGENERACY, LEFT.** -/
theorem topPairing_nondegenerate_left
    (f : WorldCoef A B)
    (h : ∀ g : WorldCoef A B, topPairing f g = 0) :
    f = fun _ => 0 := by
  funext c
  have hc := h (basis (complementCell c))
  rw [topPairing_basis_right] at hc
  exact hc

/-- **UNIVERSAL INTEGRAL POINCARE NONDEGENERACY, RIGHT.** -/
theorem topPairing_nondegenerate_right
    (g : WorldCoef A B)
    (h : ∀ f : WorldCoef A B, topPairing f g = 0) :
    g = fun _ => 0 := by
  funext c
  have hc := h (basis (complementCell c))
  rw [topPairing_basis_left] at hc
  simpa [complementCell_involutive] using hc

/-- Basis vectors pair by exact complementary Kronecker duality. -/
theorem topPairing_basis_basis
    (c d : WorldCell A B) :
    topPairing (basis c) (basis d) =
      if d = complementCell c then 1 else 0 := by
  rw [topPairing_basis_left]
  unfold basis
  by_cases h : complementCell c = d
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]

/-! ## 5. The original HC rectangle is a specialization -/

theorem hc_digit_nilpotence :
    (digitEndo 4 3)^3 = 0 :=
  digitEndo_pow_depth

theorem hc_carry_nilpotence :
    (carryEndo 4 3)^4 = 0 :=
  carryEndo_pow_depth

theorem hc_lefschetz_nilpotence :
    (lefschetzEndo 4 3)^6 = 0 := by
  simpa using (lefschetz_pow_boundary (A:=4) (B:=3))

/-- One crown collecting the dimension-free upgrade. -/
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
