import GSTGraphV2Ontological

/-!
# GST GRAPH V2 — UNCONDITIONAL REVERSE ONTOLOGICAL EXISTENCE

The original Hodge/de-Rham absorption isolated a strong reverse-window
statement asking a positive production window to force one *specific* source
cell to be Happy.  That localization is stronger than positivity itself needs.

The pure ontological current already proves a more primitive reverse theorem
without any postulate: every non-Happy physical cell has nonpositive density,
and all reverse-base-seven / vertical base-three weights are positive.
Therefore a strictly positive finite ontological window cannot be assembled
entirely from bad cells.  At least one genuine Happy cell must occur somewhere
inside the observed block.

This file proves that reverse-existence theorem first.  It is the correct
unconditional contradiction primitive to combine later with canonical
renormalization / no-erasure if one wants to localize the witness to a chosen
boundary cell.
-/

set_option maxHeartbeats 50000000
set_option maxRecDepth 1000000

noncomputable section

namespace GSTGraphV2OntologicalReverseExistence

open GST2DMixedEmergence
open GSTGraphV2InfiniteControl
open GSTGraphV2Ontological

/-- If every density in one horizontal reverse-base-seven row is nonpositive,
the whole encoded row is nonpositive. -/
theorem reverseOntCode_nonpositive_of_density_nonpositive
    (C d : Nat → Nat) :
    ∀ N : Nat,
      (∀ t, t < N → ontDensity (C t) (d t) ≤ 0) →
      reverseOntCode C d N ≤ 0 := by
  intro N hbad
  induction N with
  | zero => simp [reverseOntCode]
  | succ N ih =>
      rw [reverseOntCode]
      have hprefix : reverseOntCode C d N ≤ 0 :=
        ih (fun t ht => hbad t (by omega))
      have hlast : ontDensity (C N) (d N) ≤ 0 := hbad N (by omega)
      nlinarith

/-- If every physical cell in a finite rectangular observation is non-Happy,
then the full base-three weighted ontological prefix is nonpositive. -/
theorem weightedOntPrefix_nonpositive_of_no_happy
    (C d : Nat → Nat → Nat)
    (N : Nat) :
    ∀ K : Nat,
      (∀ t p, t < N → p < K → C t p < 4) →
      (∀ t p, t < N → p < K → d t p < 3) →
      (∀ t p, t < N → p < K → ¬ HappyCell (C t p) (d t p)) →
      weightedOntPrefix C d N K ≤ 0 := by
  intro K hC hd hbad
  induction K with
  | zero => simp [weightedOntPrefix]
  | succ K ih =>
      rw [weightedOntPrefix]
      have hprefix : weightedOntPrefix C d N K ≤ 0 :=
        ih
          (fun t p ht hp => hC t p ht (by omega))
          (fun t p ht hp => hd t p ht (by omega))
          (fun t p ht hp => hbad t p ht (by omega))
      have hrow :
          reverseOntCode (fun t => C t K) (fun t => d t K) N ≤ 0 := by
        apply reverseOntCode_nonpositive_of_density_nonpositive
        intro t ht
        exact ontDensity_nonpositive_of_not_happy
          (C t K) (d t K)
          (hC t K ht (by omega))
          (hd t K ht (by omega))
          (hbad t K ht (by omega))
      have hweight : (0 : Int) ≤ ((3^K : Nat) : Int) := by positivity
      have hweighted :
          (((3^K : Nat) : Int)) *
              reverseOntCode (fun t => C t K) (fun t => d t K) N ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hweight hrow
      linarith

/-- **UNCONDITIONAL REVERSE EXISTENCE.**
A strictly positive physical weighted window contains at least one Happy cell. -/
theorem weightedOntPrefix_positive_exists_happy
    (C d : Nat → Nat → Nat)
    (N K : Nat)
    (hC : ∀ t p, t < N → p < K → C t p < 4)
    (hd : ∀ t p, t < N → p < K → d t p < 3)
    (hpos : 0 < weightedOntPrefix C d N K) :
    ∃ t p, t < N ∧ p < K ∧ HappyCell (C t p) (d t p) := by
  by_contra hnone
  push_neg at hnone
  have hnonpos := weightedOntPrefix_nonpositive_of_no_happy
    C d N K hC hd
    (fun t p ht hp => hnone t p ht hp)
  exact (not_lt_of_ge hnonpos) hpos

/-- Graph-V2 specialization: every positive finite production window contains
an actual Happy graph cell somewhere in that window. -/
theorem graphOntWindow_positive_exists_happy
    (E N b K : Nat)
    (hpos : 0 < graphOntWindow E N b K) :
    ∃ t p, t < N ∧ p < K ∧
      HappyCell
        (graph E t (b+p)).seven.carry
        (graph E t (b+p)).seven.digit := by
  unfold graphOntWindow at hpos
  exact weightedOntPrefix_positive_exists_happy
    (fun t j => (graph E t (b+j)).seven.carry)
    (fun t j => (graph E t (b+j)).seven.digit)
    N K
    (fun t p ht hp => graph_carry_lt_four E t (b+p))
    (fun t p ht hp => graph_digit_lt_three E t (b+p))
    hpos

/-- For a nonzero-height Hodge-style window `q+1`, positivity gives a concrete
Happy witness with vertical coordinate at most `q`. -/
theorem graphOntWindow_positive_exists_happy_below_top
    (E N b q : Nat)
    (hpos : 0 < graphOntWindow E N b (q+1)) :
    ∃ t p, t < N ∧ p ≤ q ∧
      HappyCell
        (graph E t (b+p)).seven.carry
        (graph E t (b+p)).seven.digit := by
  obtain ⟨t,p,ht,hp,hHappy⟩ :=
    graphOntWindow_positive_exists_happy E N b (q+1) hpos
  exact ⟨t,p,ht,by omega,hHappy⟩

#check reverseOntCode_nonpositive_of_density_nonpositive
#check weightedOntPrefix_nonpositive_of_no_happy
#check weightedOntPrefix_positive_exists_happy
#check graphOntWindow_positive_exists_happy
#check graphOntWindow_positive_exists_happy_below_top

#print axioms reverseOntCode_nonpositive_of_density_nonpositive
#print axioms weightedOntPrefix_nonpositive_of_no_happy
#print axioms weightedOntPrefix_positive_exists_happy
#print axioms graphOntWindow_positive_exists_happy
#print axioms graphOntWindow_positive_exists_happy_below_top

end GSTGraphV2OntologicalReverseExistence
