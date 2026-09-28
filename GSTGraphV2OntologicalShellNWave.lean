import HodgeDeRhamOntologicalShellRigidity
import GSTGraphV2CanonicalNWave

/-!
# GST GRAPH V2 — ONTOLOGICAL SHELL N-WAVE RIGIDITY

`HodgeDeRhamOntologicalShellRigidity` replaced the false cumulative reverse
window by the exact newly exposed vertical shell.  The first version was
written at horizontal origin zero because that is the form needed to diagnose
the old Hodge/de-Rham absorption statement.

The canonical n-wave geometry is stronger: it preserves the complete physical
carry/digit cell under arbitrary finite origin stripping, with the accumulated
horizontal phase retained exactly.  This file therefore lifts shell rigidity
to arbitrary horizontal phase and proves that the shell observable is exactly
transported through every canonical n-wave layer.

The result is an all-depth reverse classifier:

* local shell positivity is equivalent to Happy at every `(E,x,b,q)`;
* the exact shell value is invariant under canonical n-wave recoordination;
* positivity / nonpositivity and the `42 * 3^q` spectral gap survive every
  n-wave depth;
* after exhausting the finite origin, the same shell is literally observed on
  the shifted unit-energy sheet.

No Hodge conjecture statement, cycle-class surjectivity, or operator
externalization is assumed.  This is pure Graph-V2 ontological geometry.
-/

set_option maxHeartbeats 40000000
set_option maxRecDepth 1000000

noncomputable section

namespace GSTGraphV2OntologicalShellNWave

open GSTCanonicalSevenAxisBridge
open GSTGraphV2InfiniteControl
open GSTGraphV2Ontological
open GSTGraphV2CanonicalEscape
open GSTGraphV2CanonicalNWave
open HodgeDeRhamOntologicalShellRigidity

/-- Local vertical shell at arbitrary horizontal phase.  Unlike an accumulated
window, it contains only the newly exposed row. -/
def graphOntShellAt (E x b q : Nat) : Int :=
  (((3^q : Nat) : Int)) *
    ontDensity
      (graph E x (b+q)).seven.carry
      (graph E x (b+q)).seven.digit

/-- At horizontal origin zero the phase-local shell is exactly the shell from
the corrected Hodge/de-Rham bridge. -/
theorem graphOntShellAt_zero (E b q : Nat) :
    graphOntShellAt E 0 b q = graphOntShell E b q := by
  rw [graphOntShell_exact]
  rfl

/-- The local shell can also be read as the increment of the old width-one
window after absorbing the horizontal phase into the energy. -/
theorem graphOntShellAt_eq_shifted_window_increment
    (E x b q : Nat) :
    graphOntShellAt E x b q =
      graphOntWindow (4^x * E) 1 b (q+1) -
        graphOntWindow (4^x * E) 1 b q := by
  rw [← graphOntShellAt_zero (4^x * E) b q]
  unfold graphOntShellAt
  congr 1
  · rfl
  · congr 1
    · change carry4 (4^0 * (4^x * E)) (b+q) =
        carry4 (4^x * E) (b+q)
      simp
    · change digit3 (4^0 * (4^x * E)) (b+q) =
        digit3 (4^x * E) (b+q)
      simp

/-- **LOCAL SHELL REVERSE CLASSIFIER.**
At arbitrary horizontal phase, positive shell is exactly the Happy sector. -/
theorem graphOntShellAt_positive_iff_happy
    (E x b q : Nat) :
    0 < graphOntShellAt E x b q ↔
      HappyCell
        (graph E x (b+q)).seven.carry
        (graph E x (b+q)).seven.digit := by
  unfold graphOntShellAt
  have hpow : (0 : Int) < (((3^q : Nat) : Int)) := by positivity
  have hphys := happy_iff_ontDensity_positive
    (graph E x (b+q)).seven.carry
    (graph E x (b+q)).seven.digit
    (graph_carry_lt_four E x (b+q))
    (graph_digit_lt_three E x (b+q))
  constructor
  · intro hprod
    have hdens :
        0 < ontDensity
          (graph E x (b+q)).seven.carry
          (graph E x (b+q)).seven.digit := by
      rcases (mul_pos_iff.mp hprod) with hpp | hnn
      · exact hpp.2
      · exact False.elim ((not_lt_of_ge (le_of_lt hpow)) hnn.1)
    exact hphys.mpr hdens
  · intro hHappy
    exact mul_pos hpow (hphys.mp hHappy)

/-- Exact local shell threshold. -/
theorem graphOntShellAt_ge_threshold_of_happy
    (E x b q : Nat)
    (hHappy : HappyCell
      (graph E x (b+q)).seven.carry
      (graph E x (b+q)).seven.digit) :
    (42 : Int) * (((3^q : Nat) : Int)) ≤ graphOntShellAt E x b q := by
  unfold graphOntShellAt
  have h42 := ontDensity_ge_42_of_happy
    (graph E x (b+q)).seven.carry
    (graph E x (b+q)).seven.digit hHappy
  have hnonneg : (0 : Int) ≤ (((3^q : Nat) : Int)) := by positivity
  nlinarith

/-- Exact bad-sector sign at arbitrary horizontal phase. -/
theorem graphOntShellAt_nonpositive_of_not_happy
    (E x b q : Nat)
    (hbad : ¬ HappyCell
      (graph E x (b+q)).seven.carry
      (graph E x (b+q)).seven.digit) :
    graphOntShellAt E x b q ≤ 0 := by
  unfold graphOntShellAt
  have hdens := ontDensity_nonpositive_of_not_happy
    (graph E x (b+q)).seven.carry
    (graph E x (b+q)).seven.digit
    (graph_carry_lt_four E x (b+q))
    (graph_digit_lt_three E x (b+q)) hbad
  have hnonneg : (0 : Int) ≤ (((3^q : Nat) : Int)) := by positivity
  exact mul_nonpos_of_nonneg_of_nonpos hnonneg hdens

/-- **N-WAVE SHELL INVARIANCE.**
The exact local shell value is transported through every canonical n-wave
layer because n-wave recoordination preserves the full physical carry/digit
cell at the observed row. -/
theorem canonical_n_wave_shell_exact
    (s n K x b q : Nat) :
    graphOntShellAt (canonicalEnergy s n) x b q =
      graphOntShellAt (nWaveEnergy s n K)
        (nWaveShift s n K + x) b q := by
  unfold graphOntShellAt
  have hphys := canonical_n_wave_physical s n K x (b+q)
  rw [hphys.1, hphys.2]

/-- Shell positivity is therefore an exact n-wave invariant. -/
theorem canonical_n_wave_shell_positive_iff
    (s n K x b q : Nat) :
    0 < graphOntShellAt (canonicalEnergy s n) x b q ↔
      0 < graphOntShellAt (nWaveEnergy s n K)
        (nWaveShift s n K + x) b q := by
  rw [canonical_n_wave_shell_exact]

/-- Happy / shell positivity commute with arbitrary n-wave recoordination. -/
theorem canonical_n_wave_shell_happy_crown
    (s n K x b q : Nat) :
    (0 < graphOntShellAt (canonicalEnergy s n) x b q ↔
      HappyCell
        (graph (canonicalEnergy s n) x (b+q)).seven.carry
        (graph (canonicalEnergy s n) x (b+q)).seven.digit)
    ∧
    (0 < graphOntShellAt (nWaveEnergy s n K)
        (nWaveShift s n K + x) b q ↔
      HappyCell
        (graph (nWaveEnergy s n K)
          (nWaveShift s n K + x) (b+q)).seven.carry
        (graph (nWaveEnergy s n K)
          (nWaveShift s n K + x) (b+q)).seven.digit)
    ∧
    graphOntShellAt (canonicalEnergy s n) x b q =
      graphOntShellAt (nWaveEnergy s n K)
        (nWaveShift s n K + x) b q := by
  exact ⟨
    graphOntShellAt_positive_iff_happy _ _ _ _,
    graphOntShellAt_positive_iff_happy _ _ _ _,
    canonical_n_wave_shell_exact s n K x b q⟩

/-- Once the origin has been exhausted, the exact shell is literally a shifted
unit-energy shell. -/
theorem canonical_n_wave_terminal_shell_exact
    (s n K x b q : Nat)
    (hK : n / 3^K = 0) :
    graphOntShellAt (canonicalEnergy s n) x b q =
      graphOntShellAt 1 (nWaveShift s n K + x) b q := by
  rw [canonical_n_wave_shell_exact]
  rw [canonical_n_wave_terminal_energy s n K hK]

/-- Terminal shell positivity/Happy classification after complete finite-origin
stripping. -/
theorem canonical_n_wave_terminal_shell_positive_iff_happy
    (s n K x b q : Nat)
    (hK : n / 3^K = 0) :
    0 < graphOntShellAt (canonicalEnergy s n) x b q ↔
      HappyCell
        (graph 1 (nWaveShift s n K + x) (b+q)).seven.carry
        (graph 1 (nWaveShift s n K + x) (b+q)).seven.digit := by
  rw [canonical_n_wave_terminal_shell_exact s n K x b q hK]
  exact graphOntShellAt_positive_iff_happy 1
    (nWaveShift s n K + x) b q

/-- **ALL-DEPTH ONTOLOGICAL SHELL CROWN.** -/
theorem ontological_shell_n_wave_crown :
    (∀ E x b q,
      (0 < graphOntShellAt E x b q ↔
        HappyCell
          (graph E x (b+q)).seven.carry
          (graph E x (b+q)).seven.digit))
    ∧
    (∀ s n K x b q,
      graphOntShellAt (canonicalEnergy s n) x b q =
        graphOntShellAt (nWaveEnergy s n K)
          (nWaveShift s n K + x) b q)
    ∧
    (∀ s n K x b q,
      n / 3^K = 0 →
        graphOntShellAt (canonicalEnergy s n) x b q =
          graphOntShellAt 1 (nWaveShift s n K + x) b q) := by
  exact ⟨graphOntShellAt_positive_iff_happy,
    canonical_n_wave_shell_exact,
    canonical_n_wave_terminal_shell_exact⟩

#check graphOntShellAt
#check graphOntShellAt_eq_shifted_window_increment
#check graphOntShellAt_positive_iff_happy
#check graphOntShellAt_ge_threshold_of_happy
#check graphOntShellAt_nonpositive_of_not_happy
#check canonical_n_wave_shell_exact
#check canonical_n_wave_shell_positive_iff
#check canonical_n_wave_terminal_shell_exact
#check canonical_n_wave_terminal_shell_positive_iff_happy
#check ontological_shell_n_wave_crown

#print axioms graphOntShellAt_eq_shifted_window_increment
#print axioms graphOntShellAt_positive_iff_happy
#print axioms canonical_n_wave_shell_exact
#print axioms canonical_n_wave_terminal_shell_exact
#print axioms ontological_shell_n_wave_crown

end GSTGraphV2OntologicalShellNWave
