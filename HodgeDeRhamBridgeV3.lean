import HodgeDeRhamBridgeV2
import GSTGraphV2OntologicalReverseExistence

/-!
# HODGE / DE RHAM BRIDGE V3 — POSTULATE-FREE REVERSE EXISTENCE

The historical absorption introduced `ReverseOntologicalWindow`, asking every
positive production window to force one designated boundary source to be
Happy.  The full localization statement is stronger than positivity alone.

Graph-V2's later pure ontological current gives an unconditional theorem at the
right logical strength: because every bad physical cell has nonpositive
density and all finite window weights are positive, every strictly positive
production window contains an actual Happy cell somewhere in its observed
support.

This file installs that theorem into the Hodge/de-Rham absorption.  The
resulting reverse-existence crown has no postulate argument.  The older
`ReverseOntologicalWindow` is retained only for source-localization; it is no
longer needed to infer existence of a signature-sector witness from positive
ontological current.
-/

set_option maxHeartbeats 50000000
set_option maxRecDepth 1000000

noncomputable section

namespace HodgeDeRhamBridgeV3

open GST2DMixedEmergence
open GSTGraphV2InfiniteControl
open GSTGraphV2Ontological
open GSTGraphV2OntologicalReverseExistence
open HodgeDeRhamBridge

/-- **POSTULATE-FREE REVERSE HODGE EXISTENCE.**
A positive production window contains a genuine signature-sector cell. -/
theorem positive_window_has_signature_cell
    (E N b K : Nat)
    (hpos : 0 < graphOntWindow E N b K) :
    ∃ t p, t < N ∧ p < K ∧
      HappyCell
        (graph E t (b+p)).seven.carry
        (graph E t (b+p)).seven.digit :=
  graphOntWindow_positive_exists_happy E N b K hpos

/-- Every positive production window therefore contains a cell carrying at
least the exact ontological Hodge threshold `42`. -/
theorem positive_window_has_density_ge_42
    (E N b K : Nat)
    (hpos : 0 < graphOntWindow E N b K) :
    ∃ t p, t < N ∧ p < K ∧
      (42 : Int) ≤ ontDensity
        (graph E t (b+p)).seven.carry
        (graph E t (b+p)).seven.digit := by
  obtain ⟨t,p,ht,hp,hHappy⟩ := positive_window_has_signature_cell E N b K hpos
  exact ⟨t,p,ht,hp,ontDensity_ge_42_of_happy _ _ hHappy⟩

/-- Conversely, if every observed cell is outside the signature sector, the
whole production window is nonpositive. -/
theorem no_signature_cell_forces_nonpositive_window
    (E N b K : Nat)
    (hbad : ∀ t p, t < N → p < K →
      ¬ HappyCell
        (graph E t (b+p)).seven.carry
        (graph E t (b+p)).seven.digit) :
    graphOntWindow E N b K ≤ 0 := by
  unfold graphOntWindow
  exact weightedOntPrefix_nonpositive_of_no_happy
    (fun t j => (graph E t (b+j)).seven.carry)
    (fun t j => (graph E t (b+j)).seven.digit)
    N K
    (fun t p ht hp => graph_carry_lt_four E t (b+p))
    (fun t p ht hp => graph_digit_lt_three E t (b+p))
    hbad

/-- Exact contraposition form: positive current is incompatible with an
all-bad observed Hodge window. -/
theorem positive_window_iff_not_all_bad
    (E N b K : Nat) :
    0 < graphOntWindow E N b K →
      ¬ (∀ t p, t < N → p < K →
        ¬ HappyCell
          (graph E t (b+p)).seven.carry
          (graph E t (b+p)).seven.digit) := by
  intro hpos hbad
  exact (not_lt_of_ge (no_signature_cell_forces_nonpositive_window E N b K hbad)) hpos

/-- V3 absorption crown: the forward source theorem from the original
ontological bridge and the new unconditional reverse-existence theorem coexist
without identifying them.  A designated Happy source forces positivity; any
positive window in turn contains at least one genuine Happy witness. -/
theorem hodge_derham_v3_reverse_existence_crown :
    (∀ E N b q : Nat, 1 ≤ N →
      HappyCell
        (graph E 0 (b+q)).seven.carry
        (graph E 0 (b+q)).seven.digit →
      0 < graphOntWindow E N b (q+1))
    ∧ (∀ E N b K : Nat,
      0 < graphOntWindow E N b K →
      ∃ t p, t < N ∧ p < K ∧
        HappyCell
          (graph E t (b+p)).seven.carry
          (graph E t (b+p)).seven.digit) := by
  exact ⟨forward_window_of_happy_source,
    positive_window_has_signature_cell⟩

#check positive_window_has_signature_cell
#check positive_window_has_density_ge_42
#check no_signature_cell_forces_nonpositive_window
#check positive_window_iff_not_all_bad
#check hodge_derham_v3_reverse_existence_crown

#print axioms positive_window_has_signature_cell
#print axioms positive_window_has_density_ge_42
#print axioms no_signature_cell_forces_nonpositive_window
#print axioms hodge_derham_v3_reverse_existence_crown

end HodgeDeRhamBridgeV3
