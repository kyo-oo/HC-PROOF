import Mathlib
import GSTGraphV2CanonicalNWave

/-!
# GST GRAPH V2 — SCALE EQUIVARIANCE CROWN

The canonical U-cut already transports a perfect-power graph through an
arbitrary finite ternary-origin cut.  This layer promotes that pointwise
transport to a compositional law.

The central result is that U-cuts form an exact finite-cut action:
a K-cut followed by an L-cut is identical to one (K+L)-cut.  The consumed
origin prefixes add as horizontal phase, the residual origin composes by
successive suffix, and the complete physical Graph-V2 packet is transported
on the entire Nat x Nat observation plane.

No terminal cutoff and no finite support hypothesis is used.
-/

set_option maxHeartbeats 20000000
set_option maxRecDepth 1000000

namespace GSTGraphV2ScaleEquivariance

open GSTGraphV2InfiniteControl
open GSTGraphV2HandwrittenExponentialCascade
open GSTGraphV2PerfectPowerBlock
open GSTGraphV2CanonicalNWave
open GSTCanonicalSevenAxisBridge

/-- Successive origin suffixes compose exactly. -/
theorem originSuffix_add (n K L : Nat) :
    originSuffix n (K + L) =
      originSuffix (originSuffix n K) L := by
  unfold originSuffix
  rw [pow_add, ← Nat.div_div_eq_div_mul]

/-- A long consumed origin prefix is the old prefix plus the newly exposed
prefix of the old suffix, placed at its exact ternary depth. -/
theorem originPrefix_add (n K L : Nat) :
    originPrefix n (K + L) =
      originPrefix n K +
        3^K * originPrefix (originSuffix n K) L := by
  unfold originPrefix originSuffix
  rw [pow_add, Nat.mod_mul]

/-- **PHASE COCYCLE.**  Horizontal phase accumulated by a (K+L)-cut is
exactly the K-phase plus the L-phase seen from the K-times renormalized
world. -/
theorem uPhaseShift_add (t n K L : Nat) :
    uPhaseShift t n (K + L) =
      uPhaseShift t n K +
        uPhaseShift (t + K) (originSuffix n K) L := by
  unfold uPhaseShift
  rw [originPrefix_add, pow_add]
  ring

/-- Residual exponents compose under successive cuts. -/
theorem uTailExponent_add (t n K L : Nat) :
    uTailExponent t n (K + L) =
      uTailExponent (t + K) (originSuffix n K) L := by
  unfold uTailExponent
  rw [originSuffix_add]
  simp [Nat.add_assoc]

/-- **RESIDUAL-WORLD SEMIGROUP LAW.**  Cutting K+L origin trits in one move
produces exactly the same live world as cutting K first and L afterwards. -/
theorem uTailEnergy_add (t n K L : Nat) :
    uTailEnergy t n (K + L) =
      uTailEnergy (t + K) (originSuffix n K) L := by
  unfold uTailEnergy
  rw [uTailExponent_add]

/-- The absolute perfect-power energy admits the exact two-stage cut
factorization. -/
theorem u_absolute_energy_two_stage
    (t n K L x : Nat) :
    4^x * 4^(3^t * n) =
      4^(uPhaseShift t n K +
          uPhaseShift (t + K) (originSuffix n K) L + x) *
        uTailEnergy (t + K) (originSuffix n K) L := by
  have h := u_absolute_energy_exact t n (K + L) x
  rw [uPhaseShift_add, uTailEnergy_add] at h
  simpa [Nat.add_assoc] using h

/-- The complete Graph-V2 information that is invariant under horizontal
re-coordination.  Coordinate labels themselves are deliberately excluded;
all arithmetic/physical observables are retained. -/
@[ext] structure PhysicalPacket where
  carry : Nat
  digit : Nat
  space : Space
  descent : Nat
  nextDescent : Nat
  eventCode : Nat
  uCharge : Int
  mixedCharge : Int
  crossingCharge : Int
  survive : Int
  deriving Repr

/-- Physical packet at one point of the enriched infinite graph. -/
def physicalPacket (E x p : Nat) : PhysicalPacket :=
  let c := graph E x p
  {
    carry := c.seven.carry
    digit := c.seven.digit
    space := c.seven.space
    descent := c.seven.descent
    nextDescent := c.seven.nextDescent
    eventCode := c.eventCode
    uCharge := c.uCharge
    mixedCharge := c.mixedCharge
    crossingCharge := c.crossingCharge
    survive := c.survive
  }

/-- Every physical observable, not merely carry/digit, is transported by one
arbitrary U-cut. -/
theorem physicalPacket_u_cut_exact
    (t n K x p : Nat) :
    physicalPacket (4^(3^t*n)) x p =
      physicalPacket (uTailEnergy t n K)
        (uPhaseShift t n K + x) p := by
  have h := graph_u_block_observables_exact t n K x p
  rcases h with
    ⟨hcarry, hdigit, hspace, hdescent, hnext, hevent,
      hu, hmixed, hcross, hsurvive⟩
  ext <;>
    simp [physicalPacket, hcarry, hdigit, hspace, hdescent, hnext,
      hevent, hu, hmixed, hcross, hsurvive]

/-- **GLOBAL PLANE EQUIVARIANCE.**  An arbitrary U-cut transports the
complete physical packet on the entire infinite horizontal/vertical graph,
not just at a chosen cell. -/
theorem u_cut_plane_equivariance
    (t n K : Nat) :
    (fun x p => physicalPacket (4^(3^t*n)) x p) =
      (fun x p => physicalPacket (uTailEnergy t n K)
        (uPhaseShift t n K + x) p) := by
  funext x p
  exact physicalPacket_u_cut_exact t n K x p

/-- **TWO-STAGE GRAPH ACTION.**  Applying a K-cut and then an L-cut to the
residual world transports the same physical packet as one coherent action,
with the two phase contributions accumulated explicitly. -/
theorem physicalPacket_u_cut_two_stage
    (t n K L x p : Nat) :
    physicalPacket (4^(3^t*n)) x p =
      physicalPacket
        (uTailEnergy (t + K) (originSuffix n K) L)
        (uPhaseShift t n K +
          uPhaseShift (t + K) (originSuffix n K) L + x) p := by
  have h1 := physicalPacket_u_cut_exact t n K x p
  have h2 := physicalPacket_u_cut_exact
    (t + K) (originSuffix n K) L
    (uPhaseShift t n K + x) p
  calc
    physicalPacket (4^(3^t*n)) x p
        = physicalPacket (uTailEnergy t n K)
            (uPhaseShift t n K + x) p := h1
    _ = physicalPacket
          (uTailEnergy (t + K) (originSuffix n K) L)
          (uPhaseShift (t + K) (originSuffix n K) L +
            (uPhaseShift t n K + x)) p := by
          simpa [uTailEnergy, uTailExponent] using h2
    _ = physicalPacket
          (uTailEnergy (t + K) (originSuffix n K) L)
          (uPhaseShift t n K +
            uPhaseShift (t + K) (originSuffix n K) L + x) p := by
          simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- **CUT SEMIGROUP COHERENCE.**  The direct (K+L)-cut and the two-stage
K-then-L cut are literally the same Graph-V2 physical re-coordination. -/
theorem u_cut_semigroup_coherence
    (t n K L x p : Nat) :
    physicalPacket (uTailEnergy t n (K + L))
        (uPhaseShift t n (K + L) + x) p =
      physicalPacket
        (uTailEnergy (t + K) (originSuffix n K) L)
        (uPhaseShift t n K +
          uPhaseShift (t + K) (originSuffix n K) L + x) p := by
  rw [uTailEnergy_add, uPhaseShift_add]

/-- Canonical perfect-power worlds inherit the complete packet transport, not
only the carry/digit projection of the earlier n-wave theorem. -/
theorem canonical_n_wave_packet_exact
    (s n K x p : Nat) :
    physicalPacket (canonicalEnergy s n) x p =
      physicalPacket (nWaveEnergy s n K)
        (nWaveShift s n K + x) p := by
  simpa [canonicalEnergy, nWaveEnergy, nWaveShift] using
    (physicalPacket_u_cut_exact (s+1) n K x p)

/-- **CANONICAL N-WAVE PLANE EQUIVARIANCE.**  Every finite canonical
renormalization depth is an exact re-coordinate of the full infinite physical
Graph-V2 plane. -/
theorem canonical_n_wave_plane_equivariance
    (s n K : Nat) :
    (fun x p => physicalPacket (canonicalEnergy s n) x p) =
      (fun x p => physicalPacket (nWaveEnergy s n K)
        (nWaveShift s n K + x) p) := by
  funext x p
  exact canonical_n_wave_packet_exact s n K x p

/-- One capstone receipt for the strengthened scale-equivariant cosmology. -/
theorem scale_equivariance_crown :
    (∀ t n K L,
      uPhaseShift t n (K+L) =
        uPhaseShift t n K +
          uPhaseShift (t+K) (originSuffix n K) L)
    ∧ (∀ t n K L,
      uTailEnergy t n (K+L) =
        uTailEnergy (t+K) (originSuffix n K) L)
    ∧ (∀ t n K,
      (fun x p => physicalPacket (4^(3^t*n)) x p) =
        (fun x p => physicalPacket (uTailEnergy t n K)
          (uPhaseShift t n K + x) p))
    ∧ (∀ s n K,
      (fun x p => physicalPacket (canonicalEnergy s n) x p) =
        (fun x p => physicalPacket (nWaveEnergy s n K)
          (nWaveShift s n K + x) p)) :=
  ⟨uPhaseShift_add, uTailEnergy_add,
    u_cut_plane_equivariance, canonical_n_wave_plane_equivariance⟩

#check originSuffix_add
#check originPrefix_add
#check uPhaseShift_add
#check uTailExponent_add
#check uTailEnergy_add
#check u_absolute_energy_two_stage
#check physicalPacket_u_cut_exact
#check u_cut_plane_equivariance
#check physicalPacket_u_cut_two_stage
#check u_cut_semigroup_coherence
#check canonical_n_wave_packet_exact
#check canonical_n_wave_plane_equivariance
#check scale_equivariance_crown

#print axioms uPhaseShift_add
#print axioms uTailEnergy_add
#print axioms physicalPacket_u_cut_exact
#print axioms u_cut_plane_equivariance
#print axioms physicalPacket_u_cut_two_stage
#print axioms u_cut_semigroup_coherence
#print axioms canonical_n_wave_plane_equivariance
#print axioms scale_equivariance_crown

end GSTGraphV2ScaleEquivariance
