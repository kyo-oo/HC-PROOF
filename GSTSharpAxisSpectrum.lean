import Mathlib
import GSTTruncatedWorldCohomologyRing

/-!
# GST SHARP AXIS SPECTRUM AND ENRICHED-WORLD RIGIDITY

Equal-cardinality GST rectangles are canonically equivalent as bare state
universes.  The enriched cohomology cosmology remembers more.

For every positive A x B world, the native axis operators and the abstract
cohomology generators have exact, not merely bounded, nilpotence spectra:

    H^n = 0  iff  B <= n,
    V^n = 0  iff  A <= n.

Thus the exponents A and B are intrinsic invariants of the labeled
cohomology algebra.  Two equal-cardinality rectangles can be state-chart
equivalent while remaining different as enriched H/V worlds.

This cleanly separates:
* bare world recoordination, governed only by cardinality;
* enriched cohomology equivalence, which remembers axis depth.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

namespace GSTSharpAxisSpectrum

open GSTWorldCosmology
open GSTUniversalLefschetzCosmology
open GSTTruncatedWorldCohomologyRing

/-- Origin cell of a positive rectangular world. -/
def originCell
    {A B : Nat} (hA : 0 < A) (hB : 0 < B) :
    WorldCell A B :=
  (⟨0,hA⟩, ⟨0,hB⟩)

/-- Cell n steps along the digit ray from the origin. -/
def digitRayCell
    {A B n : Nat} (hA : 0 < A) (hn : n < B) :
    WorldCell A B :=
  (⟨0,hA⟩, ⟨n,hn⟩)

/-- Cell n steps along the carry ray from the origin. -/
def carryRayCell
    {A B n : Nat} (hn : n < A) (hB : 0 < B) :
    WorldCell A B :=
  (⟨n,hn⟩, ⟨0,hB⟩)

/-- The n-th digit power sends the origin basis to value one at the n-th
digit-ray cell whenever that cell is still inside the world. -/
theorem digitEndo_pow_origin_ray
    {A B n : Nat} (hA : 0 < A) (hn : n < B) :
    ((digitEndo A B)^n)
        (basis (originCell hA (by omega)))
        (digitRayCell hA hn) = 1 := by
  rw [digitEndo_pow_apply]
  simp [digitShiftN, basis, originCell, digitRayCell]

/-- The n-th carry power sends the origin basis to value one at the n-th
carry-ray cell whenever that cell is still inside the world. -/
theorem carryEndo_pow_origin_ray
    {A B n : Nat} (hn : n < A) (hB : 0 < B) :
    ((carryEndo A B)^n)
        (basis (originCell (by omega) hB))
        (carryRayCell hn hB) = 1 := by
  rw [carryEndo_pow_apply]
  simp [carryShiftN, basis, originCell, carryRayCell]

/-- Every digit power strictly below B is nonzero. -/
theorem digitEndo_pow_ne_zero
    {A B n : Nat} (hA : 0 < A) (hn : n < B) :
    (digitEndo A B)^n ≠ 0 := by
  intro hz
  have hval := congrArg
    (fun F : Module.End ℤ (WorldCoef A B) =>
      F (basis (originCell hA (by omega)))
        (digitRayCell hA hn)) hz
  rw [digitEndo_pow_origin_ray hA hn] at hval
  simp at hval

/-- Every carry power strictly below A is nonzero. -/
theorem carryEndo_pow_ne_zero
    {A B n : Nat} (hn : n < A) (hB : 0 < B) :
    (carryEndo A B)^n ≠ 0 := by
  intro hz
  have hval := congrArg
    (fun F : Module.End ℤ (WorldCoef A B) =>
      F (basis (originCell (by omega) hB))
        (carryRayCell hn hB)) hz
  rw [carryEndo_pow_origin_ray hn hB] at hval
  simp at hval

/-- **EXACT DIGIT NILPOTENCE SPECTRUM.** -/
theorem digitEndo_pow_eq_zero_iff
    {A B n : Nat} (hA : 0 < A) :
    (digitEndo A B)^n = 0 ↔ B ≤ n := by
  constructor
  · intro hz
    by_contra h
    have hn : n < B := by omega
    exact digitEndo_pow_ne_zero hA hn hz
  · intro hBn
    exact pow_eq_zero_of_le hBn
      (digitEndo_pow_depth (A:=A) (B:=B))

/-- **EXACT CARRY NILPOTENCE SPECTRUM.** -/
theorem carryEndo_pow_eq_zero_iff
    {A B n : Nat} (hB : 0 < B) :
    (carryEndo A B)^n = 0 ↔ A ≤ n := by
  constructor
  · intro hz
    by_contra h
    have hn : n < A := by omega
    exact carryEndo_pow_ne_zero hn hB hz
  · intro hAn
    exact pow_eq_zero_of_le hAn
      (carryEndo_pow_depth (A:=A) (B:=B))

/-- The abstract cohomology generator H has no premature nilpotence. -/
theorem H_pow_ne_zero
    {A B n : Nat} (hA : 0 < A) (hn : n < B) :
    (H A B)^n ≠ 0 := by
  intro hz
  have hop := congrArg (worldOperatorHom A B) hz
  have hop' :
      (hOp A B)^n = 0 := by
    simpa using hop
  have hval :
      (digitEndo A B)^n = 0 := by
    exact congrArg
      (fun F : WorldOperatorRing A B =>
        (F : Module.End ℤ (WorldCoef A B))) hop'
  exact digitEndo_pow_ne_zero hA hn hval

/-- The abstract cohomology generator V has no premature nilpotence. -/
theorem V_pow_ne_zero
    {A B n : Nat} (hn : n < A) (hB : 0 < B) :
    (V A B)^n ≠ 0 := by
  intro hz
  have hop := congrArg (worldOperatorHom A B) hz
  have hop' :
      (vOp A B)^n = 0 := by
    simpa using hop
  have hval :
      (carryEndo A B)^n = 0 := by
    exact congrArg
      (fun F : WorldOperatorRing A B =>
        (F : Module.End ℤ (WorldCoef A B))) hop'
  exact carryEndo_pow_ne_zero hn hB hval

/-- **EXACT H-GENERATOR NILPOTENCE SPECTRUM.** -/
theorem H_pow_eq_zero_iff
    {A B n : Nat} (hA : 0 < A) :
    (H A B)^n = 0 ↔ B ≤ n := by
  constructor
  · intro hz
    by_contra h
    exact H_pow_ne_zero hA (by omega) hz
  · intro hBn
    exact pow_eq_zero_of_le hBn (H_pow_depth A B)

/-- **EXACT V-GENERATOR NILPOTENCE SPECTRUM.** -/
theorem V_pow_eq_zero_iff
    {A B n : Nat} (hB : 0 < B) :
    (V A B)^n = 0 ↔ A ≤ n := by
  constructor
  · intro hz
    by_contra h
    exact V_pow_ne_zero (by omega) hB hz
  · intro hAn
    exact pow_eq_zero_of_le hAn (V_pow_depth A B)

/-- The labeled H spectrum alone reconstructs the digit depth B. -/
theorem H_spectrum_recovers_cols
    {A B C D : Nat}
    (hA : 0 < A) (hC : 0 < C)
    (hSpectrum :
      ∀ n : Nat,
        ((H A B)^n = 0) ↔ ((H C D)^n = 0)) :
    B = D := by
  have hDB : D ≤ B := by
    have hz : (H A B)^B = 0 := H_pow_depth A B
    have hz' : (H C D)^B = 0 := (hSpectrum B).mp hz
    exact (H_pow_eq_zero_iff hC).mp hz'
  have hBD : B ≤ D := by
    have hz : (H C D)^D = 0 := H_pow_depth C D
    have hz' : (H A B)^D = 0 := (hSpectrum D).mpr hz
    exact (H_pow_eq_zero_iff hA).mp hz'
  omega

/-- The labeled V spectrum alone reconstructs the carry depth A. -/
theorem V_spectrum_recovers_rows
    {A B C D : Nat}
    (hB : 0 < B) (hD : 0 < D)
    (hSpectrum :
      ∀ n : Nat,
        ((V A B)^n = 0) ↔ ((V C D)^n = 0)) :
    A = C := by
  have hCA : C ≤ A := by
    have hz : (V A B)^A = 0 := V_pow_depth A B
    have hz' : (V C D)^A = 0 := (hSpectrum A).mp hz
    exact (V_pow_eq_zero_iff hD).mp hz'
  have hAC : A ≤ C := by
    have hz : (V C D)^C = 0 := V_pow_depth C D
    have hz' : (V A B)^C = 0 := (hSpectrum C).mpr hz
    exact (V_pow_eq_zero_iff hB).mp hz'
  omega

/-- **ENRICHED-WORLD RIGIDITY.**
For positive worlds, equality of the two labeled generator spectra forces
equality of the rectangular world dimensions. -/
theorem enriched_world_shape_rigid
    {A B C D : Nat}
    (hA : 0 < A) (hB : 0 < B)
    (hC : 0 < C) (hD : 0 < D)
    (hH :
      ∀ n : Nat,
        ((H A B)^n = 0) ↔ ((H C D)^n = 0))
    (hV :
      ∀ n : Nat,
        ((V A B)^n = 0) ↔ ((V C D)^n = 0)) :
    A = C ∧ B = D := by
  exact ⟨
    V_spectrum_recovers_rows hB hD hV,
    H_spectrum_recovers_cols hA hC hH⟩

/-- Swapping the two generator spectra reconstructs the transposed shape. -/
theorem enriched_world_shape_rigid_up_to_swap
    {A B C D : Nat}
    (hA : 0 < A) (hB : 0 < B)
    (hC : 0 < C) (hD : 0 < D)
    (hHV :
      ∀ n : Nat,
        ((H A B)^n = 0) ↔ ((V C D)^n = 0))
    (hVH :
      ∀ n : Nat,
        ((V A B)^n = 0) ↔ ((H C D)^n = 0)) :
    A = D ∧ B = C := by
  have hAD : A = D := by
    have hDA : D ≤ A := by
      have hz : (V A B)^A = 0 := V_pow_depth A B
      have hz' : (H C D)^A = 0 := (hVH A).mp hz
      exact (H_pow_eq_zero_iff hC).mp hz'
    have hAD' : A ≤ D := by
      have hz : (H C D)^D = 0 := H_pow_depth C D
      have hz' : (V A B)^D = 0 := (hVH D).mpr hz
      exact (V_pow_eq_zero_iff hB).mp hz'
    omega
  have hBC : B = C := by
    have hCB : C ≤ B := by
      have hz : (H A B)^B = 0 := H_pow_depth A B
      have hz' : (V C D)^B = 0 := (hHV B).mp hz
      exact (V_pow_eq_zero_iff hD).mp hz'
    have hBC' : B ≤ C := by
      have hz : (V C D)^C = 0 := V_pow_depth C D
      have hz' : (H A B)^C = 0 := (hHV C).mpr hz
      exact (H_pow_eq_zero_iff hA).mp hz'
    omega
  exact ⟨hAD, hBC⟩

/-- Crown separating bare cardinal equivalence from enriched cohomological
shape information. -/
theorem sharp_axis_spectrum_crown :
    (∀ A B n, 0 < A ->
      ((H A B)^n = 0 ↔ B ≤ n))
    ∧ (∀ A B n, 0 < B ->
      ((V A B)^n = 0 ↔ A ≤ n))
    ∧ (∀ A B C D,
      0 < A -> 0 < B -> 0 < C -> 0 < D ->
      (∀ n, ((H A B)^n = 0) ↔ ((H C D)^n = 0)) ->
      (∀ n, ((V A B)^n = 0) ↔ ((V C D)^n = 0)) ->
      A = C ∧ B = D) := by
  exact ⟨
    fun A B n hA => H_pow_eq_zero_iff hA,
    fun A B n hB => V_pow_eq_zero_iff hB,
    fun A B C D hA hB hC hD hH hV =>
      enriched_world_shape_rigid hA hB hC hD hH hV⟩

#check digitEndo_pow_eq_zero_iff
#check carryEndo_pow_eq_zero_iff
#check H_pow_eq_zero_iff
#check V_pow_eq_zero_iff
#check H_spectrum_recovers_cols
#check V_spectrum_recovers_rows
#check enriched_world_shape_rigid
#check enriched_world_shape_rigid_up_to_swap
#check sharp_axis_spectrum_crown

#print axioms H_pow_eq_zero_iff
#print axioms V_pow_eq_zero_iff
#print axioms enriched_world_shape_rigid
#print axioms enriched_world_shape_rigid_up_to_swap
#print axioms sharp_axis_spectrum_crown

end GSTSharpAxisSpectrum
