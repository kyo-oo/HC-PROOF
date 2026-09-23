import Mathlib
import waves.GSTNCohomology
import waves.GSTWaveCohomologyV2

/-!
# WAVE II V2 — UNCONDITIONAL RANK AND UNIVERSAL INTERFERENCE

This upgrade removes redundant hypotheses from the N-cohomology rank law,
promotes the interference decomposition to arbitrary test amplitudes, and
extracts exact Ω-cut witnesses and digit-two mode classification.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

namespace GSTNCohomologyV2

open GST2DMixedEmergence
open GSTCanonicalSevenAxisBridge
open GSTWaveCohomology
open GSTWaveCohomologyV2
open GSTNCohomology

/-- A tower window is empty exactly at depth zero. -/
theorem towerWindow_nil_iff (R p N : Nat) :
    towerWindow R p N = [] ↔ N = 0 := by
  constructor
  · intro h
    have hlen := towerWindow_length R p N
    rw [h] at hlen
    simp at hlen
    exact hlen.symm
  · intro h
    subst N
    simp [towerWindow]

/-- Positive depth is exactly nonemptiness, not merely sufficient for it. -/
theorem towerWindow_nonempty_iff (R p N : Nat) :
    towerWindow R p N ≠ [] ↔ 0 < N := by
  constructor
  · intro hne
    have hN : N ≠ 0 := by
      intro hz
      apply hne
      exact (towerWindow_nil_iff R p N).2 hz
    omega
  · intro hpos hnil
    have hz := (towerWindow_nil_iff R p N).1 hnil
    omega

/-- Canonical isolated channel readouts, defined at every depth. -/
def canonicalNCohoBasis (R : Nat) (s : NShape) (N : Nat) :
    Fin s.holes → nCohoClasses R s N :=
  fun i => (fun j => if j = i then towerWindow R (s.channel j) N else [], 0)

/-- Every N-shape has its prescribed readout at each hole at every depth,
including zero. Distinctness is certified separately at positive depth. -/
theorem ncoho_rank_unconditional (R : Nat) (s : NShape) (N : Nat) :
    ∀ i : Fin s.holes,
      (canonicalNCohoBasis R s N i).1 i =
        towerWindow R (s.channel i) N := by
  intro i
  simp [canonicalNCohoBasis]

/-- Distinct holes have distinct canonical readouts at every positive depth. -/
theorem canonicalNCohoBasis_injective (R : Nat) (s : NShape) (N : Nat)
    (hN : 0 < N) : Function.Injective (canonicalNCohoBasis R s N) := by
  intro i j hij
  by_contra hne
  have hcoord := congrArg (fun z : nCohoClasses R s N => z.1 i) hij
  have hz : towerWindow R (s.channel i) N = [] := by
    simpa [canonicalNCohoBasis, hne] using hcoord
  exact (towerWindow_nonempty_iff R (s.channel i) N).2 hN hz

/-- Diagonal readout availability needs no nonempty-window hypothesis.
The stronger injectivity conclusion of `ncoho_rank` uses nonemptiness. -/
theorem ncoho_rank_absorbed (R : Nat) (s : NShape) (N : Nat) :
    ∃ (basis : Fin s.holes → nCohoClasses R s N),
      ∀ i : Fin s.holes, (basis i).1 i =
        towerWindow R (s.channel i) N := by
  exact ⟨canonicalNCohoBasis R s N, ncoho_rank_unconditional R s N⟩

/-- Pair Wave I with an arbitrary integer amplitude field on the vertical
channel. -/
def weightedInterference (R lo hi : Nat) (A : Nat → ℤ) : ℤ :=
  ∑ p ∈ Finset.Icc lo hi, waveTwoForm (cellOf R p) * A p

def weightedHorizontal (R lo hi : Nat) (A : Nat → ℤ) : ℤ :=
  ∑ p ∈ Finset.Icc lo hi, horizontalCoboundary (cellOf R p) * A p

def weightedVertical (R lo hi : Nat) (A : Nat → ℤ) : ℤ :=
  ∑ p ∈ Finset.Icc lo hi, verticalCoboundary (cellOf R p) * A p

def weightedSource (R lo hi : Nat) (A : Nat → ℤ) : ℤ :=
  ∑ p ∈ Finset.Icc lo hi, waveSource (cellOf R p) * A p

/-- **UNIVERSAL INTERFERENCE LAW.**  Wave-I decomposition pairs exactly
with every integer amplitude field, not only Wave II. -/
theorem weighted_interference_decomposition
    (R lo hi : Nat) (A : Nat → ℤ) :
    weightedInterference R lo hi A =
      weightedHorizontal R lo hi A +
      weightedVertical R lo hi A +
      weightedSource R lo hi A := by
  have hsplit : ∀ p ∈ Finset.Icc lo hi,
      waveTwoForm (cellOf R p) * A p =
        horizontalCoboundary (cellOf R p) * A p
        + (verticalCoboundary (cellOf R p) * A p
          + waveSource (cellOf R p) * A p) := by
    intro p hp
    rw [wave_cell_decomposition]
    ring
  unfold weightedInterference weightedHorizontal weightedVertical weightedSource
  rw [Finset.sum_congr rfl hsplit]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  ring

/-- Wave II's original interference is the canonical-amplitude specialization
of the universal pairing. -/
theorem interference_is_weighted (R lo hi : Nat) :
    interference R lo hi =
      weightedInterference R lo hi (waveIIAmplitude R) := by
  rfl

/-- The original reaction law is absorbed by the universal law. -/
theorem interference_decomposition_absorbed (R lo hi : Nat) :
    interference R lo hi =
      horizontalPairing R lo hi +
      verticalPairing R lo hi +
      sourcePairing R lo hi := by
  simpa [interference_is_weighted, weightedInterference,
    weightedHorizontal, weightedVertical, weightedSource,
    horizontalPairing, verticalPairing, sourcePairing] using
      weighted_interference_decomposition R lo hi (waveIIAmplitude R)

/-- **EXACT Ω-CUT SIGNATURE.**  Every Ω class-two exponent carries a
specified Happy witness at its own cut row, not merely an existential row. -/
theorem shape_signature_exact_cut (R : Nat)
    (hclass : GSTGraphV2OmegaWaveLaw.omegaClassTwo R) :
    ∃ a core : Nat,
      1 ≤ a ∧ core % 3 = 2 ∧ R = 3^a * core ∧
      GSTU2DEventTransport.HappyCell
        (carry4 (4^R) (a+1)) (digit3 (4^R) (a+1)) := by
  rcases hclass with ⟨a, core, ha, hcore, hR⟩
  refine ⟨a, core, ha, hcore, hR, ?_⟩
  rw [hR]
  exact GSTGraphV2OmegaWaveLaw.omega_cut_happy_gate a core ha hcore

/-- On a digit-two row, Wave I's mode belongs to an exact three-value
spectrum. -/
theorem digit_two_mode_classification (R p : Nat)
    (hbig2 : digit3 R p = 2) :
    (twoWaveFrame R p).1 = -56 ∨
    (twoWaveFrame R p).1 = -112 ∨
    (twoWaveFrame R p).1 = 70 := by
  have hC4 : carry4 R p < 4 := (cellOf R p).hcarry
  have hcases :
      carry4 R p = 0 ∨ carry4 R p = 1 ∨
      carry4 R p = 2 ∨ carry4 R p = 3 := by omega
  unfold twoWaveFrame
  simp only [waveTwoForm, cellOf]
  rw [hbig2]
  rcases hcases with h0 | h1 | h2 | h3
  · left
    rw [h0]
    decide
  · right; left
    rw [h1]
    decide
  · left
    rw [h2]
    decide
  · right; right
    rw [h3]
    decide

/-- The old nonvanishing refinement follows from the exact mode spectrum. -/
theorem two_wave_frame_refines_absorbed (R p : Nat)
    (hbig2 : digit3 R p = 2) :
    (twoWaveFrame R p).1 ≠ 0 := by
  rcases digit_two_mode_classification R p hbig2 with h | h | h <;>
    rw [h] <;> decide

theorem wave_II_v2_crown :
    (∀ R p N, towerWindow R p N ≠ [] ↔ 0 < N)
    ∧ (∀ R s N i,
      (canonicalNCohoBasis R s N i).1 i =
        towerWindow R (s.channel i) N)
    ∧ (∀ R lo hi A,
      weightedInterference R lo hi A =
        weightedHorizontal R lo hi A +
        weightedVertical R lo hi A +
        weightedSource R lo hi A) := by
  refine ⟨towerWindow_nonempty_iff, ?_, weighted_interference_decomposition⟩
  intro R s N i
  exact ncoho_rank_unconditional R s N i

#check towerWindow_nil_iff
#check towerWindow_nonempty_iff
#check ncoho_rank_unconditional
#check ncoho_rank_absorbed
#check weighted_interference_decomposition
#check shape_signature_exact_cut
#check digit_two_mode_classification
#check two_wave_frame_refines_absorbed
#check wave_II_v2_crown

#print axioms ncoho_rank_unconditional
#print axioms weighted_interference_decomposition
#print axioms shape_signature_exact_cut
#print axioms digit_two_mode_classification
#print axioms wave_II_v2_crown

/-- Testing against every amplitude detects exactly the vanishing mode
field on the chosen interval. -/
theorem weighted_interference_separates (R lo hi : Nat) :
    (∀ A : Nat → ℤ, weightedInterference R lo hi A = 0) ↔
      ∀ p ∈ Finset.Icc lo hi, waveTwoForm (cellOf R p) = 0 := by
  classical
  constructor
  · intro h p hp
    have ht := h (fun k => if k = p then 1 else 0)
    have heval : weightedInterference R lo hi (fun k => if k = p then 1 else 0) =
        waveTwoForm (cellOf R p) := by
      unfold weightedInterference
      rw [Finset.sum_eq_single p]
      · simp
      · intro b hb hbp
        simp [hbp]
      · intro hnot
        exact (hnot hp).elim
    rwa [heval] at ht
  · intro h A
    unfold weightedInterference
    apply Finset.sum_eq_zero
    intro p hp
    rw [h p hp, zero_mul]

/-- A Kronecker amplitude probes one local mode exactly. -/
theorem weightedInterference_delta
    (R lo hi p : Nat) (hp : p ∈ Finset.Icc lo hi) :
    weightedInterference R lo hi (fun k => if k = p then 1 else 0) =
      waveTwoForm (cellOf R p) := by
  classical
  unfold weightedInterference
  rw [Finset.sum_eq_single p]
  · simp
  · intro b hb hbp
    simp [hbp]
  · intro hnot
    exact (hnot hp).elim

/-- Pairing the field difference with itself measures its exact squared
discrepancy. Cancellation between distinct channels cannot hide a mismatch. -/
theorem weighted_interference_energy (R S lo hi : Nat) :
    weightedInterference R lo hi (fun p => waveTwoForm (cellOf R p) - waveTwoForm (cellOf S p)) -
      weightedInterference S lo hi (fun p => waveTwoForm (cellOf R p) - waveTwoForm (cellOf S p)) =
      ∑ p ∈ Finset.Icc lo hi, (waveTwoForm (cellOf R p) - waveTwoForm (cellOf S p))^2 := by
  unfold weightedInterference
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  ring

/-- A single difference-amplitude experiment separates two given worlds
exactly; universal quantification over all probe amplitudes is unnecessary. -/
theorem weighted_interference_single_probe (R S lo hi : Nat) :
    weightedInterference R lo hi (fun p => waveTwoForm (cellOf R p) - waveTwoForm (cellOf S p)) =
      weightedInterference S lo hi (fun p => waveTwoForm (cellOf R p) - waveTwoForm (cellOf S p)) ↔
      ∀ p ∈ Finset.Icc lo hi, waveTwoForm (cellOf R p) = waveTwoForm (cellOf S p) := by
  rw [← sub_eq_zero, weighted_interference_energy]
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun p _ => sq_nonneg _)]
  simp only [sq_eq_zero_iff, sub_eq_zero]

/-- **COMPLETE INTERFERENCE TOMOGRAPHY.**  Two worlds have identical response
to every integer amplitude field exactly when their local Wave-I mode fields
agree pointwise on the observed interval. -/
theorem weighted_interference_ext (R S lo hi : Nat) :
    (∀ A : Nat → ℤ,
      weightedInterference R lo hi A = weightedInterference S lo hi A) ↔
      ∀ p ∈ Finset.Icc lo hi,
        waveTwoForm (cellOf R p) = waveTwoForm (cellOf S p) := by
  classical
  constructor
  · intro h
    exact (weighted_interference_single_probe R S lo hi).1 (h _)
  · intro h A
    unfold weightedInterference
    apply Finset.sum_congr rfl
    intro p hp
    rw [h p hp]

#check weightedInterference_delta
#check weighted_interference_ext
#print axioms weightedInterference_delta
#print axioms weighted_interference_ext

end GSTNCohomologyV2
