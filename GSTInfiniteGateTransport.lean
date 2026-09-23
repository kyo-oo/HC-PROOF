import GSTInfiniteBadTransport

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTV2

/-!
# Happy-gate information transport

A Happy Gate is not an information endpoint.  Its visible digit-two event is
re-encoded into the next carry while the parent bad language and the shared
coupled invariant continue at the next natural observation depth.
-/

/-- At a Happy cell the visible output is still digit two. -/
theorem happy_output_two
    (carry d : Nat) (h : Happy carry d) :
    cellOutput carry d = 2 := by
  rcases h with ⟨rfl, hcarry⟩
  rcases hcarry with rfl | rfl <;>
    norm_num [cellOutput, cellMass]

/-- The same Happy cell transports its information into a nonzero next carry,
exactly 2 in NULL and 3 in GST+. -/
theorem happy_next_carry_two_or_three
    (carry d : Nat) (h : Happy carry d) :
    cellNextCarry carry d = 2 ∨ cellNextCarry carry d = 3 := by
  rcases h with ⟨rfl, hcarry⟩
  rcases hcarry with rfl | rfl
  · left
    norm_num [cellNextCarry, cellMass]
  · right
    norm_num [cellNextCarry, cellMass]

/-- In particular, a Happy event cannot disappear into zero transported carry. -/
theorem happy_next_carry_ne_zero
    (carry d : Nat) (h : Happy carry d) :
    cellNextCarry carry d ≠ 0 := by
  rcases happy_next_carry_two_or_three carry d h with h2 | h3 <;> omega

/-- Full one-step conservation identity specialized to a Happy event.  The
visible digit-two and latent next carry together are exactly the same local
mass as before the gate. -/
theorem happy_mass_reencoded
    (carry d : Nat) (h : Happy carry d) :
    cellMass carry d = 2 + 3 * cellNextCarry carry d := by
  rw [cell_mass_conservation, happy_output_two carry d h]

/-- State after a certified child Happy Gate.  The gate information has not
been discarded: it survives simultaneously as visible output two and a
nonzero latent carry while the parent's exact bad suffix remains active. -/
structure LatentGateTransfer
    (A : Nat) (initial : CoupledState) (j : Nat) : Prop where
  childHappy :
    Happy
      (coupledOrbit A initial j).childCarry
      ((coupledOrbit A initial j).childTail % 3)
  visibleOutputTwo :
    cellOutput
      (coupledOrbit A initial j).childCarry
      ((coupledOrbit A initial j).childTail % 3) = 2
  nextCarryTwoOrThree :
    (coupledOrbit A initial (j+1)).childCarry = 2 ∨
      (coupledOrbit A initial (j+1)).childCarry = 3
  nextCarryNonzero :
    (coupledOrbit A initial (j+1)).childCarry ≠ 0
  nextInvariant :
    CoupledInvariant A (coupledOrbit A initial (j+1))
  nextParentBadSuffix :
    SeededBadTrace
      (coupledOrbit A initial (j+1)).parentSeed
      ((coupledOrbit A initial (j+1)).parentWord A)

/-- A child Happy Gate inside an all-depth bad coupled controller produces the
next latent-information state automatically.  This is the production
replacement for treating a gate as a terminal creation/destruction event. -/
theorem coupled_happy_transports_information
    (A : Nat) (initial : CoupledState) (j : Nat)
    (hcontrol : InfiniteBadCoupledControl A initial)
    (hHappy :
      Happy
        (coupledOrbit A initial j).childCarry
        ((coupledOrbit A initial j).childTail % 3)) :
    LatentGateTransfer A initial j := by
  have hnext := happy_next_carry_two_or_three
    (coupledOrbit A initial j).childCarry
    ((coupledOrbit A initial j).childTail % 3) hHappy
  have hnext0 := happy_next_carry_ne_zero
    (coupledOrbit A initial j).childCarry
    ((coupledOrbit A initial j).childTail % 3) hHappy
  refine {
    childHappy := hHappy
    visibleOutputTwo := happy_output_two
      (coupledOrbit A initial j).childCarry
      ((coupledOrbit A initial j).childTail % 3) hHappy
    nextCarryTwoOrThree := ?_
    nextCarryNonzero := ?_
    nextInvariant := hcontrol.coupled.invariantAll (j+1)
    nextParentBadSuffix := hcontrol.parentBadSuffix (j+1)
  }
  · simpa [coupledOrbit, coupledStep] using hnext
  · simpa [coupledOrbit, coupledStep] using hnext0

/-- On a physical digit-two input the emitted digit and latent carry recover
Happy exactly; the converse is essential when reading a transported gate. -/
theorem happy_iff_output_and_next (carry : Nat) :
    Happy carry 2 ↔ cellOutput carry 2 = 2 ∧
      (cellNextCarry carry 2 = 2 ∨ cellNextCarry carry 2 = 3) := by
  constructor
  · intro h
    exact ⟨happy_output_two carry 2 h, happy_next_carry_two_or_three carry 2 h⟩
  · rintro ⟨hout, hn⟩
    have hm := cell_mass_conservation carry 2
    rw [hout] at hm
    unfold cellMass at hm
    refine ⟨rfl, ?_⟩
    rcases hn with hn | hn <;> rw [hn] at hm <;> omega


end GSTV2
