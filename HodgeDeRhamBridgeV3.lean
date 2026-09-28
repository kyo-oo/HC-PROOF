import HodgeDeRhamBridgeV2
import GSTGraphV2OntologicalShellNWave

/-!
# HC ABSORPTION V3 — UNCONDITIONAL GRADED SHELL ABSORPTION

The first Hodge/de-Rham absorption used positivity of an accumulated
ontological window as the hoped-for reverse Hodge classifier.  The exact
Graph-V2 arithmetic shows that cumulative positivity can be inherited from a
lower row, so it does not classify the newly exposed source.

The correct graded observable is the local ontological shell: the vertical
increment contributed by the new row alone.  Shell rigidity is theorem-level
and unconditional.  At every horizontal phase and every depth,

  shell > 0  <->  Happy source
             <->  density = 84 or density = 42.

Moreover canonical n-wave recoordination preserves the exact shell value, so
this reverse classifier survives arbitrary finite origin stripping and lands
unchanged on the terminal unit-energy sheet.

This file rebuilds the absorption crown around that local graded derivative.
There is no `ReverseOntologicalWindow` premise.  The finite comparison and Tate
skew laws from V2 remain intact, while the reverse Hodge/signature classifier
is now a proved all-depth shell theorem rather than a cumulative postulate.

This is still an internal GST/Hodge-de-Rham absorption theorem: no claim is
made here that an arbitrary external classical cycle-class map has been
identified with the shell current.  That semantic connection is attacked in
the classical primitive-defect layer separately.
-/

set_option maxHeartbeats 40000000
set_option maxRecDepth 1000000

noncomputable section

namespace HodgeDeRhamBridgeV3

open GST2DMixedEmergence
open GSTU2DEventTransport
open GSTGraphV2SixAdicOntologicalGeometry
open GSTGraphV2SixAdicSynchronizedShadows
open GSTGraphV2InfiniteControl
open GSTGraphV2Ontological
open GSTGraphV2CanonicalNWave
open GSTGraphV2OntologicalShellNWave
open HodgeDeRhamBridge
open HodgeDeRhamBridgeV2

/-- **UNCONDITIONAL REVERSE HODGE SHELL.**
The local graded production shell is positive exactly on the signature sector,
at arbitrary horizontal phase and arbitrary observation depth. -/
theorem shell_hodge_characterization
    (E x b q : Nat) :
    0 < graphOntShellAt E x b q ↔
      HappyCell
        (graph E x (b+q)).seven.carry
        (graph E x (b+q)).seven.digit :=
  graphOntShellAt_positive_iff_happy E x b q

/-- The shell classifier can be stated directly in terms of the exact positive
Hodge-current values. -/
theorem shell_positive_iff_exact_signature_current
    (E x b q : Nat) :
    0 < graphOntShellAt E x b q ↔
      ontDensity
          (graph E x (b+q)).seven.carry
          (graph E x (b+q)).seven.digit = 84
      ∨ ontDensity
          (graph E x (b+q)).seven.carry
          (graph E x (b+q)).seven.digit = 42 := by
  rw [shell_hodge_characterization]
  exact signature_current_exact
    (graph E x (b+q)).seven.carry
    (graph E x (b+q)).seven.digit
    (graph_carry_lt_four E x (b+q))
    (graph_digit_lt_three E x (b+q))

/-- Exact quantized shell spectrum: a positive Hodge shell has one of exactly
two amplitudes, `84 * 3^q` or `42 * 3^q`. -/
theorem positive_shell_exact
    (E x b q : Nat) :
    0 < graphOntShellAt E x b q ↔
      graphOntShellAt E x b q =
          (((3^q : Nat) : Int)) * 84
      ∨ graphOntShellAt E x b q =
          (((3^q : Nat) : Int)) * 42 := by
  constructor
  · intro hpos
    rcases (shell_positive_iff_exact_signature_current E x b q).mp hpos with
      h84 | h42
    · left
      simp [graphOntShellAt, h84]
    · right
      simp [graphOntShellAt, h42]
  · rintro (h84 | h42)
    · rw [h84]
      positivity
    · rw [h42]
      positivity

/-- The exact shell spectral gap in the Hodge direction. -/
theorem signature_shell_injects_threshold
    (E x b q : Nat)
    (hSig : HappyCell
      (graph E x (b+q)).seven.carry
      (graph E x (b+q)).seven.digit) :
    (42 : Int) * (((3^q : Nat) : Int)) ≤ graphOntShellAt E x b q :=
  graphOntShellAt_ge_threshold_of_happy E x b q hSig

/-- Every nonsignature source has nonpositive new shell.  Lower positive rows
cannot contaminate this statement because the shell has already subtracted the
previous prefix. -/
theorem nonsignature_shell_nonpositive
    (E x b q : Nat)
    (hbad : ¬ HappyCell
      (graph E x (b+q)).seven.carry
      (graph E x (b+q)).seven.digit) :
    graphOntShellAt E x b q ≤ 0 :=
  graphOntShellAt_nonpositive_of_not_happy E x b q hbad

/-- **N-WAVE HODGE SHELL NATURALITY.**
The exact graded Hodge/signature current is unchanged by every canonical
n-wave recoordination. -/
theorem n_wave_hodge_shell_naturality
    (s n K x b q : Nat) :
    graphOntShellAt (GSTGraphV2CanonicalEscape.canonicalEnergy s n) x b q =
      graphOntShellAt (nWaveEnergy s n K)
        (nWaveShift s n K + x) b q :=
  canonical_n_wave_shell_exact s n K x b q

/-- Consequently signature detection by shell positivity is invariant through
every canonical n-wave layer. -/
theorem n_wave_signature_iff
    (s n K x b q : Nat) :
    HappyCell
        (graph (GSTGraphV2CanonicalEscape.canonicalEnergy s n) x (b+q)).seven.carry
        (graph (GSTGraphV2CanonicalEscape.canonicalEnergy s n) x (b+q)).seven.digit
      ↔
    HappyCell
        (graph (nWaveEnergy s n K)
          (nWaveShift s n K + x) (b+q)).seven.carry
        (graph (nWaveEnergy s n K)
          (nWaveShift s n K + x) (b+q)).seven.digit := by
  exact GSTGraphV2CanonicalNWave.canonical_n_wave_happy_iff
    s n K x (b+q)

/-- Terminal form: once the finite origin is exhausted, the complete graded
Hodge-shell signal is read on a translated unit-energy graph. -/
theorem terminal_unit_shell_hodge_characterization
    (s n K x b q : Nat)
    (hK : n / 3^K = 0) :
    0 < graphOntShellAt
        (GSTGraphV2CanonicalEscape.canonicalEnergy s n) x b q ↔
      HappyCell
        (graph 1 (nWaveShift s n K + x) (b+q)).seven.carry
        (graph 1 (nWaveShift s n K + x) (b+q)).seven.digit :=
  canonical_n_wave_terminal_shell_positive_iff_happy
    s n K x b q hK

/-- The cumulative reverse-window postulate is not needed by the V3 crown;
the exact shell reverse law, comparison theorem, twist law and n-wave
naturality are all unconditional. -/
theorem absorption_v3_crown :
    (∀ E x b q,
      (0 < graphOntShellAt E x b q ↔
        HappyCell
          (graph E x (b+q)).seven.carry
          (graph E x (b+q)).seven.digit))
    ∧ (∀ E x b q,
      (0 < graphOntShellAt E x b q ↔
        graphOntShellAt E x b q = (((3^q : Nat) : Int)) * 84
        ∨ graphOntShellAt E x b q = (((3^q : Nat) : Int)) * 42))
    ∧ (∀ k t x y,
      SixAdicIsoAt k ((4 : Int)^t * x) ((4 : Int)^t * y) ↔
        DyadicShadowAt (k-2*t) x y ∧ TriadicShadowAt k x y)
    ∧ (∀ s n K x b q,
      graphOntShellAt (GSTGraphV2CanonicalEscape.canonicalEnergy s n) x b q =
        graphOntShellAt (nWaveEnergy s n K)
          (nWaveShift s n K + x) b q) := by
  exact ⟨
    shell_hodge_characterization,
    positive_shell_exact,
    finite_twist_skew_truncated,
    n_wave_hodge_shell_naturality⟩

#check shell_hodge_characterization
#check shell_positive_iff_exact_signature_current
#check positive_shell_exact
#check signature_shell_injects_threshold
#check nonsignature_shell_nonpositive
#check n_wave_hodge_shell_naturality
#check n_wave_signature_iff
#check terminal_unit_shell_hodge_characterization
#check absorption_v3_crown

#print axioms shell_hodge_characterization
#print axioms positive_shell_exact
#print axioms n_wave_hodge_shell_naturality
#print axioms terminal_unit_shell_hodge_characterization
#print axioms absorption_v3_crown

end HodgeDeRhamBridgeV3
