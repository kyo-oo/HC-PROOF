import HodgeDeRhamBridge

/-!
# HODGE–DE RHAM ONTOLOGICAL SHELL RIGIDITY

The original absorption layer isolated `ReverseOntologicalWindow` as the
universal reverse direction it still wanted: positivity of a whole accumulated
production window should force the top source cell to be Happy.

The cumulative statement is stronger than the actual Graph-V2 arithmetic.
A lower positive row can survive inside the accumulated prefix even when the
new top row is neutral.  The correct reverse observable is therefore not the
whole prefix but the **new vertical shell** added at the top level.

For horizontal width one this shell is completely local.  The recursive
`weightedOntPrefix` law gives

  shell(E,b,q)
    = graphOntWindow E 1 b (q+1) - graphOntWindow E 1 b q
    = 3^q * ontDensity(source at height b+q).

Since `3^q` is strictly positive and the physical ontological density has the
exact spectral gap

  Happy <-> density > 0 <-> density >= 42,

shell positivity is **unconditionally equivalent** to Happy at the new source.
This gives a proved reverse Hodge/ontological classifier with no postulate and
no contamination from lower rows.

The file also records a concrete counterexample to the older cumulative
reverse-window proposition, so downstream Hodge work cannot accidentally use a
false bridge.  Nothing in the existing architecture is deleted: the new shell
law is an additive, strictly sharper replacement observable.
-/

set_option maxHeartbeats 30000000
set_option maxRecDepth 1000000

noncomputable section

namespace HodgeDeRhamOntologicalShellRigidity

open GST2DMixedEmergence
open GSTU2DEventTransport
open GSTCanonicalSevenAxisBridge
open GSTGraphV2InfiniteControl
open GSTGraphV2Ontological
open HodgeDeRhamBridge

/-- The one-row vertical shell added when the ontological observation depth is
extended from `q` to `q+1`.  Horizontal width is deliberately fixed to one so
the shell reads the source cell itself, with no later horizontal contamination. -/
def graphOntShell (E b q : Nat) : Int :=
  graphOntWindow E 1 b (q+1) - graphOntWindow E 1 b q

/-- **EXACT ONTOLOGICAL SHELL LAW.**
The new shell is exactly `3^q` times the ontological density of the new source
cell.  All previously accumulated rows cancel identically. -/
theorem graphOntShell_exact (E b q : Nat) :
    graphOntShell E b q =
      (((3^q : Nat) : Int)) *
        ontDensity
          (graph E 0 (b+q)).seven.carry
          (graph E 0 (b+q)).seven.digit := by
  simp [graphOntShell, graphOntWindow, weightedOntPrefix, reverseOntCode]

/-- The shell is positive exactly when its new physical source is Happy.  This
is the unconditional reverse direction that cumulative-window positivity could
not provide. -/
theorem graphOntShell_positive_iff_happy
    (E b q : Nat) :
    0 < graphOntShell E b q ↔
      HappyCell
        (graph E 0 (b+q)).seven.carry
        (graph E 0 (b+q)).seven.digit := by
  rw [graphOntShell_exact]
  have hpow : (0 : Int) < (((3^q : Nat) : Int)) := by positivity
  have hphys := happy_iff_ontDensity_positive
    (graph E 0 (b+q)).seven.carry
    (graph E 0 (b+q)).seven.digit
    (graph_carry_lt_four E 0 (b+q))
    (graph_digit_lt_three E 0 (b+q))
  constructor
  · intro hprod
    have hdens :
        0 < ontDensity
          (graph E 0 (b+q)).seven.carry
          (graph E 0 (b+q)).seven.digit := by
      rcases (mul_pos_iff.mp hprod) with hpp | hnn
      · exact hpp.2
      · exact False.elim ((not_lt_of_ge (le_of_lt hpow)) hnn.1)
    exact hphys.mpr hdens
  · intro hHappy
    have hdens := hphys.mp hHappy
    exact mul_pos hpow hdens

/-- Equivalent orientation matching the Hodge-de Rham dictionary: Happy is
exactly positivity of the newly exposed shell. -/
theorem happy_iff_graphOntShell_positive
    (E b q : Nat) :
    HappyCell
        (graph E 0 (b+q)).seven.carry
        (graph E 0 (b+q)).seven.digit ↔
      0 < graphOntShell E b q :=
  (graphOntShell_positive_iff_happy E b q).symm

/-- Exact shell spectral gap.  A positive shell is not arbitrarily small: its
source density is at least 42, so the shell is at least `42 * 3^q`. -/
theorem graphOntShell_ge_threshold_of_happy
    (E b q : Nat)
    (hHappy : HappyCell
      (graph E 0 (b+q)).seven.carry
      (graph E 0 (b+q)).seven.digit) :
    (42 : Int) * (((3^q : Nat) : Int)) ≤ graphOntShell E b q := by
  rw [graphOntShell_exact]
  have h42 := ontDensity_ge_42_of_happy
    (graph E 0 (b+q)).seven.carry
    (graph E 0 (b+q)).seven.digit hHappy
  have hnonneg : (0 : Int) ≤ (((3^q : Nat) : Int)) := by positivity
  nlinarith

/-- Conversely, every non-Happy source has a nonpositive shell. -/
theorem graphOntShell_nonpositive_of_not_happy
    (E b q : Nat)
    (hbad : ¬ HappyCell
      (graph E 0 (b+q)).seven.carry
      (graph E 0 (b+q)).seven.digit) :
    graphOntShell E b q ≤ 0 := by
  rw [graphOntShell_exact]
  have hdens := ontDensity_nonpositive_of_not_happy
    (graph E 0 (b+q)).seven.carry
    (graph E 0 (b+q)).seven.digit
    (graph_carry_lt_four E 0 (b+q))
    (graph_digit_lt_three E 0 (b+q)) hbad
  have hnonneg : (0 : Int) ≤ (((3^q : Nat) : Int)) := by positivity
  exact mul_nonpos_of_nonneg_of_nonpos hnonneg hdens

/-- **CUMULATIVE REVERSE-WINDOW COUNTEREXAMPLE.**
For `E=2`, width one and rows `0,1`, the lower row is the Happy state `(0,2)`
and contributes 84, while the new top source is the neutral non-Happy state
`(2,0)`.  The accumulated two-row window is therefore positive although its
top source is not Happy. -/
theorem cumulative_reverse_window_counterexample :
    0 < graphOntWindow 2 1 0 2
      ∧ ¬ HappyCell
        (graph 2 0 1).seven.carry
        (graph 2 0 1).seven.digit := by
  constructor <;>
    norm_num [graphOntWindow, weightedOntPrefix, reverseOntCode,
      graph, cell, vertex, carry4, digit3,
      ontDensity, ontDigitPotential, ontCarryPotential,
      outDigit, nextCarry, HappyCell]

/-- Hence the old cumulative reverse-window proposition is false on the exact
Graph-V2 definitions.  The proved shell theorem above is the correct local
reverse classifier. -/
theorem not_ReverseOntologicalWindow :
    ¬ ReverseOntologicalWindow := by
  intro hR
  rcases cumulative_reverse_window_counterexample with ⟨hpos, hbad⟩
  exact hbad (hR 2 1 0 1 hpos)

/-- **SHELL RIGIDITY CROWN.**  The correct reverse bridge is theorem-level,
not postulated: each newly exposed shell is positive exactly at a Happy source,
with an exact `42 * 3^q` positive threshold and nonpositive bad sector. -/
theorem ontological_shell_rigidity_crown :
    (∀ E b q,
      (0 < graphOntShell E b q ↔
        HappyCell
          (graph E 0 (b+q)).seven.carry
          (graph E 0 (b+q)).seven.digit))
    ∧ (∀ E b q,
      HappyCell
          (graph E 0 (b+q)).seven.carry
          (graph E 0 (b+q)).seven.digit →
        (42 : Int) * (((3^q : Nat) : Int)) ≤ graphOntShell E b q)
    ∧ (∀ E b q,
      ¬ HappyCell
          (graph E 0 (b+q)).seven.carry
          (graph E 0 (b+q)).seven.digit →
        graphOntShell E b q ≤ 0) := by
  exact ⟨graphOntShell_positive_iff_happy,
    graphOntShell_ge_threshold_of_happy,
    graphOntShell_nonpositive_of_not_happy⟩

#check graphOntShell
#check graphOntShell_exact
#check graphOntShell_positive_iff_happy
#check happy_iff_graphOntShell_positive
#check graphOntShell_ge_threshold_of_happy
#check graphOntShell_nonpositive_of_not_happy
#check cumulative_reverse_window_counterexample
#check not_ReverseOntologicalWindow
#check ontological_shell_rigidity_crown

#print axioms graphOntShell_exact
#print axioms graphOntShell_positive_iff_happy
#print axioms graphOntShell_ge_threshold_of_happy
#print axioms graphOntShell_nonpositive_of_not_happy
#print axioms not_ReverseOntologicalWindow
#print axioms ontological_shell_rigidity_crown

end HodgeDeRhamOntologicalShellRigidity
