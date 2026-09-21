import Mathlib
import GSTTransferBridge
import GSTHodgeAssaultV2
import GSTClayOfficialV2

/-!
# TRANSFER BRIDGE V2 — ALL-WEIGHT EXACT ADDRESS CLASSIFICATION

The address map remains the exact twelve-coordinate bridge.  This layer
strengthens its internal classification to every natural weight and makes
the live-sector coefficient unique.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

namespace GSTTransferBridgeV2

open GSTWaveCohomology
open GSTLefschetzCrown
open GSTHodgeAssault
open GSTHodgeAssaultV2
open GSTClayOfficial
open GSTClayOfficialV2
open GSTTransferBridge

/-- Monomials whose address degree is outside the twelve-cell basis vanish. -/
theorem clMono_zero_of_twelve_le (n : Nat) (hn : 12 ≤ n) :
    clMono n = fun _ => 0 := by
  funext i
  unfold clMono
  rw [if_neg]
  omega

/-- Above weight two, the classical-address Hodge condition forces zero. -/
theorem clHodge_zero_of_three_le
    (p : Nat) (hp : 3 ≤ p) (φ : ClRing)
    (hφ : isClHodge p φ) :
    φ = fun _ => 0 := by
  funext i
  exact hφ i (by omega)

/-- Zero belongs to every classical-address Hodge sector. -/
theorem zero_isClHodge (p : Nat) :
    isClHodge p (fun _ => 0) := by
  intro i hi
  rfl

/-- **ALL-WEIGHT HODGE TRANSPORT.**  The address support condition and the
GST diagonal support condition agree for every natural weight. -/
theorem transfer_hodge_iff_all_weights (p : Nat) (f : WaveCoef) :
    isClHodge p (addr f) ↔ isHodgeClass p f := by
  by_cases hp : p < 3
  · exact transfer_hodge_iff p hp f
  · have hp3 : 3 ≤ p := by omega
    constructor
    · intro hcl
      have hazero := clHodge_zero_of_three_le p hp3 (addr f) hcl
      have haddr0 : addr f = addr (fun _ : WaveCell => (0:ℤ)) := by
        rw [hazero]
        rfl
      have hf0 := addr_injective haddr0
      rw [hf0]
      exact zero_isHodgeClass p
    · intro hf
      have hf0 := hodge_class_zero_of_three_le p hp3 f hf
      rw [hf0]
      intro i hi
      rfl

/-- **ALL-WEIGHT ADDRESS CLASSIFICATION.**  Every address-Hodge class is
exactly a scalar multiple of its degree-4p monomial.  For p >= 3 this is
the zero-sector statement. -/
theorem transferred_hodge_all_weights (p : Nat) (φ : ClRing) :
    isClHodge p φ ↔
      ∃ z : ℤ, ∀ i : Fin 12, φ i = z * clMono (4*p) i := by
  by_cases hp : p < 3
  · constructor
    · intro hφ
      exact transferred_hodge_conjecture p hp φ hφ
    · rintro ⟨z,hz⟩
      intro i hine
      rw [hz i]
      unfold clMono
      rw [if_neg hine, mul_zero]
  · have hp3 : 3 ≤ p := by omega
    constructor
    · intro hφ
      have hzero := clHodge_zero_of_three_le p hp3 φ hφ
      refine ⟨0, ?_⟩
      intro i
      rw [hzero]
      simp
    · rintro ⟨z,hz⟩
      have hm0 : clMono (4*p) = fun _ => 0 :=
        clMono_zero_of_twelve_le (4*p) (by omega)
      have hzero : φ = fun _ => 0 := by
        funext i
        rw [hz i, hm0]
        simp
      rw [hzero]
      exact zero_isClHodge p

/-- On a live address sector, the coefficient is read directly at degree 4p. -/
theorem transferred_coefficient_exact
    (p : Nat) (hp : p < 3) (φ : ClRing)
    (hφ : isClHodge p φ) :
    ∀ i : Fin 12,
      φ i = φ ⟨4*p, by omega⟩ * clMono (4*p) i := by
  obtain ⟨z,hz⟩ := transferred_hodge_conjecture p hp φ hφ
  have hdiag := hz ⟨4*p, by omega⟩
  have hmono : clMono (4*p) ⟨4*p, by omega⟩ = (1:ℤ) := by
    simp [clMono]
  rw [hmono, mul_one] at hdiag
  intro i
  rw [hz i, hdiag]

/-- The live-sector coefficient is unique. -/
theorem transferred_coefficient_unique
    (p : Nat) (hp : p < 3) (φ : ClRing)
    (z w : ℤ)
    (hz : ∀ i : Fin 12, φ i = z * clMono (4*p) i)
    (hw : ∀ i : Fin 12, φ i = w * clMono (4*p) i) :
    z = w := by
  have hz0 := hz ⟨4*p, by omega⟩
  have hw0 := hw ⟨4*p, by omega⟩
  simp [clMono] at hz0 hw0
  omega

/-- Above weight two every address-Hodge class is zero and its rationalization
is therefore zero as well. -/
theorem transferred_zero_sector
    (p : Nat) (hp : 3 ≤ p) (φ : ClRing)
    (hφ : isClHodge p φ) :
    φ = fun _ => 0 :=
  clHodge_zero_of_three_le p hp φ hφ

/-- Cup transport can be iterated simultaneously along both native axes. -/
theorem addr_mixed_cup_iterate
    (a b : Nat) (g : WaveCoef) :
    addr ((Nat.iterate cupDigit a) ((Nat.iterate cupCarry b) g)) =
      (Nat.iterate clCupD a) ((Nat.iterate clCupV b) (addr g)) := by
  rw [addr_cupDigit_iterate, addr_cupCarry_iterate]

theorem transfer_v2_crown :
    (∀ p f, isClHodge p (addr f) ↔ isHodgeClass p f)
    ∧ (∀ p φ, isClHodge p φ ↔
      ∃ z : ℤ, ∀ i : Fin 12, φ i = z * clMono (4*p) i)
    ∧ (∀ p, p < 3 → ∀ φ, isClHodge p φ →
      ∀ i : Fin 12,
        φ i = φ ⟨4*p, by omega⟩ * clMono (4*p) i) := by
  exact ⟨transfer_hodge_iff_all_weights,
    transferred_hodge_all_weights,
    transferred_coefficient_exact⟩

#check clMono_zero_of_twelve_le
#check clHodge_zero_of_three_le
#check transfer_hodge_iff_all_weights
#check transferred_hodge_all_weights
#check transferred_coefficient_exact
#check transferred_coefficient_unique
#check transferred_zero_sector
#check addr_mixed_cup_iterate
#check transfer_v2_crown

#print axioms transfer_hodge_iff_all_weights
#print axioms transferred_hodge_all_weights
#print axioms transferred_coefficient_exact
#print axioms transferred_coefficient_unique
#print axioms transfer_v2_crown

end GSTTransferBridgeV2
