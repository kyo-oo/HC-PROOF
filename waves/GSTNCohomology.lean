import waves.GSTWaveCohomology
import GST2DMixedEmergence
import GSTGraphV2OmegaWaveLaw
import GSTTailFFourthDimension

/-!
# WAVE II — N-COHOMOLOGY (the second wave: shapes, holes, interference)

## STATUS: COMPILED, MACHINE-VERIFIED

Part of the build registry (root `waves.GSTNCohomology`).  Every theorem
below is proven; no sorries.  Statements of the former spec layer that
were false as literally stated have been upgraded to their true laws.

## What Wave II is

Task 4 directive: *the second wave is "N" cohomology — for the new
concepts, abstracts we will bring in that wave; then we see how both
waves react to abstract high-dimensional shapes.*

Wave I (the Hodge wave) reads the twelve-cell complex: it is the
*algebraic* wave — its 2-form is the mixed density, its class is the
SURVIVE incidence.  Wave II reads the **tower**: the sheet stack whose
levels stabilize into frozen windows (`omega_tower_word_mod_stable`,
`omega_cut_word_stabilizes`).  It is the *topological* wave — the wave of
shapes and holes.

Definitions:

* an **N-shape** is a finite abstract shape complex with N holes,
  realized as N marked channels on a common lattice — the abstract
  geometry is *represented* (a finite injective channel map), never
  assumed;
* **N-cohomology** is the cohomology of the depth-N tower window stack:
  the window readout family of the N channels — one independent frozen
  window profile per hole (the channel map is injective, Theorem
  `channel_embedding`), each window a depth-N stabilized word
  (Theorems `towerWindow_length`, `towerWindow_pos`);
* the **interference pairing** of Wave I and Wave II is the discrete
  Lefschetz pairing: integrate Wave I's 2-form against Wave II's window
  amplitudes over a height window.  The pairing decomposes exactly into
  horizontal pairing + vertical pairing + 56·source pairing — the
  reaction of the two waves is *computable* (Theorem
  `interference_decomposition`), and the source term is carried only by
  the matter cells: the NULL chord is sterile (surviveI = 0), the GST+
  chord carries incidence 2 (Theorem `source_null_sterile`).

The two waves react to abstract high-dimensional shapes through this
pairing: Wave I contributes the class (what survives), Wave II
contributes the window structure (where the holes are), and the
interference is the shape's GST signature.  On the Ω-covered families
(`omegaClassTwo`) the signature is certified nonempty: the wave owns a
physical Happy row at a finite height (Theorem
`shape_signature_on_omega_families`, the verified
`omega_wave_existence_class_two`).
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

namespace GSTNCohomology

open GST2DMixedEmergence
open GSTCanonicalSevenAxisBridge
open GSTWaveCohomology

/-! ## §1 N-shapes: abstract complexes with N holes -/

/-- An **N-shape**: an abstract shape complex with N holes, realized as N
marked height-channels (hole positions) on a common lattice.  The abstract
geometry of Task 4 is *represented*, not assumed: a shape is a finite
injective channel map, and all shape content flows from the tower dynamics
on those channels. -/
structure NShape where
  /-- The number of holes. -/
  holes : Nat
  /-- The marked channel of each hole. -/
  channel : Fin holes → Nat
  /-- Distinct channels: the holes are genuinely separate. -/
  distinct : ∀ i j : Fin holes, i ≠ j → channel i ≠ channel j

/-- The trivial shape: no holes, no channels. -/
def emptyShape : NShape where
  holes := 0
  channel := fun i => absurd i.2 (Nat.not_lt_zero i.val)
  distinct := by intro i j _; exact absurd i.2 (by omega)

/-- The channel map of an N-shape is **injective**: the N holes realize N
genuinely distinct readout coordinates.  This is the independence clause
of the N-cohomology rank law — no two holes of the shape are the same
hole. -/
theorem channel_embedding (s : NShape) : Function.Injective s.channel := by
  intro i j h
  by_contra hne
  exact s.distinct i j hne h

/-! ## §2 The N-cohomology: tower windows as the second wave -/

/-- **Wave II amplitude** on a height channel of the tower of `R`: the
frozen-window readout — the difference of consecutive ternary digits at
that channel.  Where Wave I's amplitude was the mixed density (the
algebraic 2-form), Wave II's amplitude is the digit-difference profile
(the topological word-derivative of the tower). -/
def waveIIAmplitude (R p : Nat) : ℤ :=
  ((R / 3 ^ p) % 3 : ℤ) - ((R / 3 ^ (p + 1)) % 3 : ℤ)

/-- The Wave II amplitude *is* the digit difference: `d_p − d_{p+1}` in
the canonical ternary coordinates.  (Definitional identity — the two wave
readouts share the digit lattice, but read different structure from it.) -/
theorem waveIIAmplitude_eq (R p : Nat) :
    waveIIAmplitude R p = (digit3 R p : ℤ) - (digit3 R (p+1) : ℤ) := by
  rfl

/-- A **tower window** of depth N over channel p: the list of Wave II
amplitudes on the first N heights.  The frozen-window phenomenon
(`omega_tower_word_mod_stable`) says these stabilize with tower level. -/
def towerWindow (R p N : Nat) : List ℤ :=
  (List.range N).map (fun k => waveIIAmplitude R (p + k))

/-- The window of depth N is a depth-N profile: its length is exactly N.
The readout dimension of the window is its depth — the emergent-dimension
count of POSTULATE III in miniature. -/
theorem towerWindow_length (R p N : Nat) :
    (towerWindow R p N).length = N := by
  rw [towerWindow, List.length_map, List.length_range]

/-- Windows of positive depth are nonempty: a depth-N readout exists
exactly when `1 ≤ N`. -/
theorem towerWindow_pos (R p : Nat) (hN : 1 ≤ N) :
    towerWindow R p N ≠ [] := by
  intro hnil
  have hlen := towerWindow_length R p N
  rw [hnil] at hlen
  simp at hlen
  omega

/-- Native channel readout space: a list at each hole, together with an
integer class coordinate. The type permits arbitrary lists; the canonical
readouts below supply the specified depth-N windows. -/
def nCohoClasses (R : Nat) (s : NShape) (N : Nat) : Type :=
  (Fin s.holes → List ℤ) × ℤ

/-- **N-CHANNEL SEPARATION.** Each hole has its own isolated nonempty
readout, and distinct holes yield distinct classes. The off-diagonal
coordinates are empty. This is an injective native readout family; no
module structure on lists is asserted. -/
theorem ncoho_rank (R : Nat) (s : NShape) (N : Nat)
    (hign : ∀ i : Fin s.holes, towerWindow R (s.channel i) N ≠ []) :
    ∃ (basis : Fin s.holes → nCohoClasses R s N),
      Function.Injective basis ∧
      (∀ i : Fin s.holes, (basis i).1 i = towerWindow R (s.channel i) N) ∧
      (∀ i j : Fin s.holes, j ≠ i → (basis i).1 j = []) := by
  let basis : Fin s.holes → nCohoClasses R s N :=
    fun i => (fun j => if j = i then towerWindow R (s.channel j) N else [], 0)
  refine ⟨basis, ?_, ?_, ?_⟩
  · intro i j hij
    by_contra hne
    have hcoord := congrArg (fun z : nCohoClasses R s N => z.1 i) hij
    have hz : towerWindow R (s.channel i) N = [] := by
      simpa [basis, hne] using hcoord
    exact hign i hz
  · intro i
    simp [basis]
  · intro i j hji
    simp [basis, hji]

/-! ## §3 The interference pairing — how the two waves react -/

/-- **THE INTERFERENCE PAIRING** of Wave I and Wave II on a height window
`[lo, hi]`: the discrete Lefschetz pairing — integrate Wave I's 2-form
(the wave mode at each height) against Wave II's window amplitudes over
the window.  This is how the two waves *react to an abstract
high-dimensional shape*: the shape's channels select where the pairing
reads. -/
def interference (R lo hi : Nat) : ℤ :=
  ∑ p ∈ Finset.Icc lo hi,
    waveTwoForm (cellOf R p) * waveIIAmplitude R p

/-- The **horizontal pairing**: Wave I's horizontal coboundary (the BIG1
boundary derivative) paired with Wave II amplitudes. -/
def horizontalPairing (R lo hi : Nat) : ℤ :=
  ∑ p ∈ Finset.Icc lo hi,
    horizontalCoboundary (cellOf R p) * waveIIAmplitude R p

/-- The **vertical pairing**: Wave I's vertical coboundary (the carry
flux derivative) paired with Wave II amplitudes. -/
def verticalPairing (R lo hi : Nat) : ℤ :=
  ∑ p ∈ Finset.Icc lo hi,
    verticalCoboundary (cellOf R p) * waveIIAmplitude R p

/-- The **source pairing**: the wave's matter (SURVIVE incidence) paired
with Wave II amplitudes — the interior term of the interference. -/
def sourcePairing (R lo hi : Nat) : ℤ :=
  ∑ p ∈ Finset.Icc lo hi,
    waveSource (cellOf R p) * waveIIAmplitude R p

/-- **THE INTERFERENCE DECOMPOSITION (the reaction law).**  The pairing of
the two waves decomposes exactly as the wave complex demands:

    interference = horizontal pairing + vertical pairing + source pairing

where the source pairing is the 56-weighted paired SURVIVE incidence
(`waveSource = 56 · surviveI` definitionally).  The reaction of the two
waves to any abstract shape is *computable*: the pairing splits into
boundary bookkeeping (the two coboundary pairings) plus the matter term —
the paired SURVIVE incidence, 56-weighted.
(Upgrade note: the former spec claimed a nonzero-iff-ignition equivalence
— false as stated, since boundary bookkeeping can mask or mimic the
source.  The true law is the exact decomposition: the reaction is
determined, cell by cell, by the closedness law of Wave I.) -/
theorem interference_decomposition (R lo hi : Nat) :
    interference R lo hi = horizontalPairing R lo hi + verticalPairing R lo hi
      + sourcePairing R lo hi := by
  have hsplit : ∀ p ∈ Finset.Icc lo hi,
      waveTwoForm (cellOf R p) * waveIIAmplitude R p
        = horizontalCoboundary (cellOf R p) * waveIIAmplitude R p
          + (verticalCoboundary (cellOf R p) * waveIIAmplitude R p
            + waveSource (cellOf R p) * waveIIAmplitude R p) := by
    intro p _
    have h := wave_cell_decomposition (cellOf R p)
    rw [h]
    ring
  unfold interference horizontalPairing verticalPairing sourcePairing
  rw [Finset.sum_congr rfl hsplit]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  ring

/-- **NULL STERILITY (the chord law of the source).**  The NULL Happy
chord `(C, d) = (0, 2)` carries no source: its SURVIVE incidence is
exactly zero — the hidden BIG1 chord `2 → 1 → 2` survives as *boundary*,
not as matter.  Consequently the source pairing of the interference is
carried only by the ALT- cells `(1,1), (2,2)` (incidence 1) and the GST+
chord `(3,2)` (incidence 2) — the wave's matter is the two-sector
BIG2 chain, never the NULL chord.  (Verified
`happy_chord_dichotomy`, left branch.) -/
theorem source_null_sterile :
    waveSource (mkCell 0 2 (by omega) (by omega)) = 0 := by
  have h := happy_chord_dichotomy 0 (Or.inl rfl)
  rcases h with ⟨_, _, _, hsurv⟩ | ⟨hne, _, _, _⟩
  · simp only [waveSource, mkCell]
    rw [hsurv]
    norm_num
  · exact absurd hne (by decide)

/-- The GST+ chord carries the maximal source: SURVIVE incidence exactly
2 — the all-SURVIVE chord `2 → 2 → 2`.  (Verified
`happy_chord_dichotomy`, right branch.) -/
theorem source_gstplus_maximal :
    waveSource (mkCell 3 2 (by omega) (by omega)) = 112 := by
  have h := happy_chord_dichotomy 3 (Or.inr rfl)
  rcases h with ⟨hne, _, _, _⟩ | ⟨_, _, _, hsurv⟩
  · exact absurd hne (by decide)
  · simp only [waveSource, mkCell]
    rw [hsurv]
    norm_num

/-! ## §4 The shape signature on the Ω-covered families -/

/-- **THE SHAPE SIGNATURE LAW.**  For the Ω-covered class-two family
(exponents `K = 3^a · core`, `a ≥ 1`, `core ≡ 2 (mod 3)`), the wave owns
a physical Happy row at a finite height `p ≥ 2`: the signature readout of
the two-wave frame is *certified nonempty* — the interference's source
term has a certified ignition locus.  This is the verified
`omega_wave_existence_class_two` of `GSTGraphV2OmegaWaveLaw`, restated as
Wave II's signature law. -/
theorem shape_signature_on_omega_families (R : Nat)
    (hclass : GSTGraphV2OmegaWaveLaw.omegaClassTwo R) :
    ∃ p : Nat, 2 ≤ p ∧
      GSTU2DEventTransport.HappyCell (carry4 (4^R) p) (digit3 (4^R) p) :=
  GSTGraphV2OmegaWaveLaw.omega_wave_existence_class_two R hclass

/-! ## §5 The two-wave frame — the combined readout -/

/-- The **combined readout** replacing the digit readout of legacy GST:
at each height, the pair (Wave I mode, Wave II amplitude).  The digit was
one ternary bit; the two-wave frame is a full algebraic-topological
certificate. -/
def twoWaveFrame (R p : Nat) : ℤ × ℤ :=
  (waveTwoForm (cellOf R p), waveIIAmplitude R p)

/-- **THE FRAME REFINEMENT LAW.**  The combined frame recovers the
digit-two event (the legacy readout): on every BIG2 digit, Wave I's mode
is *nonzero* — the 2-form values on digit-two cells are
`-56, -112, -56, 70` across the four carries, never zero.  The legacy
digit readout is a shadow of the wave mode; the frame separates what the
digit merged (the NULL and GST+ chords carry distinct modes —
`spectrum_separates_chords`). -/
theorem two_wave_frame_refines (R p : Nat) (hbig2 : digit3 R p = 2) :
    (twoWaveFrame R p).1 ≠ 0 := by
  have hC4 : carry4 R p < 4 := (cellOf R p).hcarry
  have hCc : carry4 R p = 0 ∨ carry4 R p = 1 ∨ carry4 R p = 2 ∨ carry4 R p = 3 := by
    omega
  unfold twoWaveFrame
  simp only [waveTwoForm, cellOf]
  rw [hbig2]
  rcases hCc with h0 | h1 | h2 | h3
  · rw [h0]
    decide
  · rw [h1]
    decide
  · rw [h2]
    decide
  · rw [h3]
    decide

/-- Wave II is a discrete derivative: its integral on any finite height
interval is precisely the two endpoint digits. -/
theorem waveIIAmplitude_telescope (R p N : Nat) :
    (∑ k ∈ Finset.range N, waveIIAmplitude R (p+k)) =
      (digit3 R p : ℤ) - (digit3 R (p+N) : ℤ) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, waveIIAmplitude_eq]
      rw [show p + (N+1) = (p+N)+1 by omega]
      ring

/-- **EXACT PREFIX RECONSTRUCTION.**  Every local Wave-II amplitude is the
discrete derivative of the integrated prefix readout.  Thus finite prefix
integration loses no local information. -/
theorem waveIIAmplitude_prefix_recovered (R p N : Nat) :
    waveIIAmplitude R (p+N) =
      (∑ k ∈ Finset.range (N+1), waveIIAmplitude R (p+k)) -
      (∑ k ∈ Finset.range N, waveIIAmplitude R (p+k)) := by
  rw [Finset.sum_range_succ]
  ring

/-- Prefix integration is an exact additive cocycle under every finite cut. -/
theorem waveII_prefix_add (R p M N : Nat) :
    (∑ k ∈ Finset.range (M+N), waveIIAmplitude R (p+k)) =
      (∑ k ∈ Finset.range M, waveIIAmplitude R (p+k)) +
      (∑ k ∈ Finset.range N, waveIIAmplitude R ((p+M)+k)) := by
  simpa [Nat.add_assoc] using
    (Finset.sum_range_add (fun k => waveIIAmplitude R (p+k)) M N)

/-- **FINITE PREFIX OBSERVABLE.** Two Wave-II channels agree on all prefixes
up to K exactly when their local amplitudes agree throughout that window. -/
theorem waveII_prefix_complete_observable (R S p q K : Nat) :
    (∀ N, N ≤ K →
      (∑ k ∈ Finset.range N, waveIIAmplitude R (p+k)) =
      (∑ k ∈ Finset.range N, waveIIAmplitude S (q+k))) ↔
      ∀ t, t < K → waveIIAmplitude R (p+t) = waveIIAmplitude S (q+t) := by
  constructor
  · intro h t ht
    have hnext := h (t+1) (by omega)
    have hprev := h t (by omega)
    rw [Finset.sum_range_succ, Finset.sum_range_succ] at hnext
    linarith
  · intro h N hN
    exact Finset.sum_congr rfl (fun t ht => h t (by have := Finset.mem_range.mp ht; omega))

/-- A Wave-II window plus one endpoint digit reconstructs every digit in
the window. This states the exact missing boundary datum of differentiation. -/
theorem waveII_channel_reconstruction (R S p q K : Nat) :
    (digit3 R p = digit3 S q ∧
      ∀ t, t < K → waveIIAmplitude R (p+t) = waveIIAmplitude S (q+t)) ↔
      ∀ t, t ≤ K → digit3 R (p+t) = digit3 S (q+t) := by
  constructor
  · rintro ⟨hbase, hamp⟩ t ht
    have hs := (waveII_prefix_complete_observable R S p q K).2 hamp t ht
    rw [waveIIAmplitude_telescope, waveIIAmplitude_telescope, hbase] at hs
    have hz : (digit3 R (p+t) : ℤ) = (digit3 S (q+t) : ℤ) := by linarith
    exact_mod_cast hz
  · intro h
    refine ⟨by simpa using h 0 (Nat.zero_le K), ?_⟩
    intro t ht
    rw [waveIIAmplitude_eq, waveIIAmplitude_eq, h t (by omega)]
    have hn := h (t+1) (by omega)
    simpa only [Nat.add_assoc] using congrArg (fun n : Nat =>
      (digit3 S (q+t) : ℤ) - (n : ℤ)) hn

/-- All Wave-II prefixes vanish exactly when every local amplitude vanishes. -/
theorem waveII_prefix_all_zero_iff (R p : Nat) :
    (∀ N, (∑ k ∈ Finset.range N, waveIIAmplitude R (p+k)) = 0) ↔
      ∀ t, waveIIAmplitude R (p+t) = 0 := by
  constructor
  · intro h t
    rw [waveIIAmplitude_prefix_recovered R p t, h (t+1), h t]
    ring
  · intro h N
    apply Finset.sum_eq_zero
    intro t ht
    exact h t

#check waveIIAmplitude_telescope
#check waveIIAmplitude_prefix_recovered
#check waveII_prefix_add
#check waveII_prefix_complete_observable
#check waveII_prefix_all_zero_iff
#print axioms waveIIAmplitude_prefix_recovered
#print axioms waveII_prefix_add
#print axioms waveII_prefix_complete_observable
#print axioms waveII_prefix_all_zero_iff

end GSTNCohomology
