import Mathlib
import GSTGraphV2ScaleEquivariance
import GSTGraphV2Ontological

/-!
# GST GRAPH V2 — SCALE-ONTOLOGICAL INVARIANCE

The scale-equivariance crown transports the complete physical packet through
every finite U-cut.  The ontological-current layer independently proves that
Happy cells are exactly the positive sector of the pure ontological density.

This file fuses those two legacy theorem families.

Consequences:
* arbitrary U-cuts preserve carry and digit exactly;
* arbitrary U-cuts preserve Happy status exactly;
* the pure ontological density is invariant under arbitrary U-cuts;
* positivity of ontological current is therefore a scale invariant;
* the same laws are coherent under two-stage K-then-L cuts;
* canonical N-wave renormalization inherits the whole result.

No fixed cutoff, terminal horizon, or new arithmetic carrier is introduced.
-/

set_option maxHeartbeats 20000000
set_option maxRecDepth 1000000

namespace GSTGraphV2ScaleOntologicalInvariant

open GST2DMixedEmergence
open GSTGraphV2InfiniteControl
open GSTGraphV2CanonicalNWave
open GSTGraphV2ScaleEquivariance
open GSTGraphV2Ontological

/-- Carry is an exact scale invariant under every finite U-cut. -/
theorem u_cut_carry_exact
    (t n K x p : Nat) :
    (graph (4^(3^t*n)) x p).seven.carry =
      (graph (uTailEnergy t n K)
        (uPhaseShift t n K + x) p).seven.carry := by
  have h := congrArg PhysicalPacket.carry
    (physicalPacket_u_cut_exact t n K x p)
  simpa [physicalPacket] using h

/-- Digit is an exact scale invariant under every finite U-cut. -/
theorem u_cut_digit_exact
    (t n K x p : Nat) :
    (graph (4^(3^t*n)) x p).seven.digit =
      (graph (uTailEnergy t n K)
        (uPhaseShift t n K + x) p).seven.digit := by
  have h := congrArg PhysicalPacket.digit
    (physicalPacket_u_cut_exact t n K x p)
  simpa [physicalPacket] using h

/-- **ARBITRARY-CUT HAPPY INVARIANCE.**
Happy status is not tied to one presentation of a perfect-power world:
every finite U-cut preserves it exactly. -/
theorem u_cut_happy_iff
    (t n K x p : Nat) :
    HappyCell
        (graph (4^(3^t*n)) x p).seven.carry
        (graph (4^(3^t*n)) x p).seven.digit
      ↔
    HappyCell
        (graph (uTailEnergy t n K)
          (uPhaseShift t n K + x) p).seven.carry
        (graph (uTailEnergy t n K)
          (uPhaseShift t n K + x) p).seven.digit := by
  have hc := u_cut_carry_exact t n K x p
  have hd := u_cut_digit_exact t n K x p
  rw [hc, hd]

/-- **ONTOLOGICAL CURRENT SCALE INVARIANCE.**
The pure ontological density itself, not merely its sign, is exactly
preserved by arbitrary finite U-cuts. -/
theorem u_cut_ontDensity_exact
    (t n K x p : Nat) :
    ontDensity
        (graph (4^(3^t*n)) x p).seven.carry
        (graph (4^(3^t*n)) x p).seven.digit
      =
    ontDensity
        (graph (uTailEnergy t n K)
          (uPhaseShift t n K + x) p).seven.carry
        (graph (uTailEnergy t n K)
          (uPhaseShift t n K + x) p).seven.digit := by
  rw [u_cut_carry_exact, u_cut_digit_exact]

/-- Positivity of the ontological current is therefore an exact scale
invariant on the entire Graph-V2 plane. -/
theorem u_cut_ontDensity_positive_iff
    (t n K x p : Nat) :
    0 <
      ontDensity
        (graph (4^(3^t*n)) x p).seven.carry
        (graph (4^(3^t*n)) x p).seven.digit
      ↔
    0 <
      ontDensity
        (graph (uTailEnergy t n K)
          (uPhaseShift t n K + x) p).seven.carry
        (graph (uTailEnergy t n K)
          (uPhaseShift t n K + x) p).seven.digit := by
  rw [u_cut_ontDensity_exact]

/-- The ontological characterization of Happy is itself compatible with every
finite U-cut. -/
theorem u_cut_happy_iff_positive_iff
    (t n K x p : Nat) :
    HappyCell
        (graph (4^(3^t*n)) x p).seven.carry
        (graph (4^(3^t*n)) x p).seven.digit
      ↔
    0 <
      ontDensity
        (graph (uTailEnergy t n K)
          (uPhaseShift t n K + x) p).seven.carry
        (graph (uTailEnergy t n K)
          (uPhaseShift t n K + x) p).seven.digit := by
  rw [u_cut_happy_iff]
  apply happy_iff_ontDensity_positive
  · exact graph_carry_lt_four _ _ _
  · exact graph_digit_lt_three _ _ _

/-- Carry is coherent under the exact two-stage K-then-L scale action. -/
theorem u_cut_two_stage_carry_exact
    (t n K L x p : Nat) :
    (graph (4^(3^t*n)) x p).seven.carry =
      (graph
        (uTailEnergy (t+K) (originSuffix n K) L)
        (uPhaseShift t n K +
          uPhaseShift (t+K) (originSuffix n K) L + x) p).seven.carry := by
  have h := congrArg PhysicalPacket.carry
    (physicalPacket_u_cut_two_stage t n K L x p)
  simpa [physicalPacket] using h

/-- Digit is coherent under the exact two-stage K-then-L scale action. -/
theorem u_cut_two_stage_digit_exact
    (t n K L x p : Nat) :
    (graph (4^(3^t*n)) x p).seven.digit =
      (graph
        (uTailEnergy (t+K) (originSuffix n K) L)
        (uPhaseShift t n K +
          uPhaseShift (t+K) (originSuffix n K) L + x) p).seven.digit := by
  have h := congrArg PhysicalPacket.digit
    (physicalPacket_u_cut_two_stage t n K L x p)
  simpa [physicalPacket] using h

/-- **SEMIGROUP HAPPY COHERENCE.**
Happy status is preserved by the full two-stage scale action. -/
theorem u_cut_two_stage_happy_iff
    (t n K L x p : Nat) :
    HappyCell
        (graph (4^(3^t*n)) x p).seven.carry
        (graph (4^(3^t*n)) x p).seven.digit
      ↔
    HappyCell
        (graph
          (uTailEnergy (t+K) (originSuffix n K) L)
          (uPhaseShift t n K +
            uPhaseShift (t+K) (originSuffix n K) L + x) p).seven.carry
        (graph
          (uTailEnergy (t+K) (originSuffix n K) L)
          (uPhaseShift t n K +
            uPhaseShift (t+K) (originSuffix n K) L + x) p).seven.digit := by
  rw [u_cut_two_stage_carry_exact, u_cut_two_stage_digit_exact]

/-- Ontological density is coherent under the full two-stage scale action. -/
theorem u_cut_two_stage_ontDensity_exact
    (t n K L x p : Nat) :
    ontDensity
        (graph (4^(3^t*n)) x p).seven.carry
        (graph (4^(3^t*n)) x p).seven.digit
      =
    ontDensity
        (graph
          (uTailEnergy (t+K) (originSuffix n K) L)
          (uPhaseShift t n K +
            uPhaseShift (t+K) (originSuffix n K) L + x) p).seven.carry
        (graph
          (uTailEnergy (t+K) (originSuffix n K) L)
          (uPhaseShift t n K +
            uPhaseShift (t+K) (originSuffix n K) L + x) p).seven.digit := by
  rw [u_cut_two_stage_carry_exact, u_cut_two_stage_digit_exact]

/-- Canonical N-wave renormalization preserves the ontological density
exactly, upgrading the earlier carry/digit and Happy projections. -/
theorem canonical_n_wave_ontDensity_exact
    (s n K x p : Nat) :
    ontDensity
        (graph (canonicalEnergy s n) x p).seven.carry
        (graph (canonicalEnergy s n) x p).seven.digit
      =
    ontDensity
        (graph (nWaveEnergy s n K)
          (nWaveShift s n K + x) p).seven.carry
        (graph (nWaveEnergy s n K)
          (nWaveShift s n K + x) p).seven.digit := by
  simpa [canonicalEnergy, nWaveEnergy, nWaveShift] using
    (u_cut_ontDensity_exact (s+1) n K x p)

/-- Canonical N-wave renormalization preserves the positive ontological
sector exactly. -/
theorem canonical_n_wave_ontDensity_positive_iff
    (s n K x p : Nat) :
    0 <
      ontDensity
        (graph (canonicalEnergy s n) x p).seven.carry
        (graph (canonicalEnergy s n) x p).seven.digit
      ↔
    0 <
      ontDensity
        (graph (nWaveEnergy s n K)
          (nWaveShift s n K + x) p).seven.carry
        (graph (nWaveEnergy s n K)
          (nWaveShift s n K + x) p).seven.digit := by
  rw [canonical_n_wave_ontDensity_exact]

/-- Capstone: the complete scale action preserves both the physical Happy
sector and its exact ontological-current certificate. -/
theorem scale_ontological_invariance_crown :
    (∀ t n K x p,
      HappyCell
          (graph (4^(3^t*n)) x p).seven.carry
          (graph (4^(3^t*n)) x p).seven.digit
        ↔
      HappyCell
          (graph (uTailEnergy t n K)
            (uPhaseShift t n K + x) p).seven.carry
          (graph (uTailEnergy t n K)
            (uPhaseShift t n K + x) p).seven.digit)
    ∧ (∀ t n K x p,
      ontDensity
          (graph (4^(3^t*n)) x p).seven.carry
          (graph (4^(3^t*n)) x p).seven.digit
        =
      ontDensity
          (graph (uTailEnergy t n K)
            (uPhaseShift t n K + x) p).seven.carry
          (graph (uTailEnergy t n K)
            (uPhaseShift t n K + x) p).seven.digit)
    ∧ (∀ t n K L x p,
      HappyCell
          (graph (4^(3^t*n)) x p).seven.carry
          (graph (4^(3^t*n)) x p).seven.digit
        ↔
      HappyCell
          (graph
            (uTailEnergy (t+K) (originSuffix n K) L)
            (uPhaseShift t n K +
              uPhaseShift (t+K) (originSuffix n K) L + x) p).seven.carry
          (graph
            (uTailEnergy (t+K) (originSuffix n K) L)
            (uPhaseShift t n K +
              uPhaseShift (t+K) (originSuffix n K) L + x) p).seven.digit) := by
  exact ⟨u_cut_happy_iff, u_cut_ontDensity_exact,
    u_cut_two_stage_happy_iff⟩

#check u_cut_carry_exact
#check u_cut_digit_exact
#check u_cut_happy_iff
#check u_cut_ontDensity_exact
#check u_cut_ontDensity_positive_iff
#check u_cut_happy_iff_positive_iff
#check u_cut_two_stage_happy_iff
#check u_cut_two_stage_ontDensity_exact
#check canonical_n_wave_ontDensity_exact
#check canonical_n_wave_ontDensity_positive_iff
#check scale_ontological_invariance_crown

#print axioms u_cut_happy_iff
#print axioms u_cut_ontDensity_exact
#print axioms u_cut_happy_iff_positive_iff
#print axioms u_cut_two_stage_happy_iff
#print axioms canonical_n_wave_ontDensity_exact
#print axioms scale_ontological_invariance_crown

end GSTGraphV2ScaleOntologicalInvariant
