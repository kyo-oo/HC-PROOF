import Mathlib
import GSTInfiniteFourPowerNavigation
import GSTTailFProof
import GSTClimbTruthValue
import GSTCanonicalTailLTE
import GSTFinalPurePowerResidueTransplant

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# THE ACT — the exact missing object, named once (base module)

The base of the climb-family stack, extracted so that every module above
it (the diagonal read, the completed prefaced read, the cascade, the
collapse) can build on these objects without circularity:

* **§0 THE ACT.**  `the_act` names the exact object whose absence is the
  whole conditionality of `hTailF`: the even-exponent statement
  `∀ K ≥ 8, noTernaryTwo (4^K) = false`.  `the_act_iff_hTailF`: through the
  repo's own green unconditional iff, the act and `hTailF`'s target are ONE
  object — whatever proves the act proves `hTailF`, and nothing weaker
  than the act does.

* **§1 THE ANSWER.  Erdős closed ⇒ hTailF closed.**
  `hTailF_of_full_erdos`: if the full ternary statement
  (`∀ n ≥ 9, noTernaryTwo (2^n) = false`) is proven — by boss, by any
  construction, inside this repo or outside it — then `hTailF` closes in
  ONE line through this green bridge.  `the_act_iff_full_erdos`: the act
  and the full statement are one object, because the repo's own
  odd-exponent half is already green.  `climb_gives_the_act`: the climb,
  the input `hTailF` currently consumes, carries strictly MORE than the
  act (the pair demand: digit two with x4-carry zero or three) — the
  conditional route through the climb is overkill, not necessity.

* **§2 THE FRONT LAW.**  At the valuation cut `v`, row `v+1` of
  `4^(3^v·a)` is exactly `a % 3`: the power-of-four ternary digit stream
  reads the reduced exponent trit directly — the zeroth level of the
  diagonal read, the seed of the whole ladder above it.
-/

namespace GSTTheAct

open GSTCanonicalSevenAxisBridge (digit3)

/-! ## §0 THE ACT — the exact missing object, named once -/

/-- THE ACT: every `4^K` from `K = 8` onward owns a ternary digit two.
This is the exact content whose absence is the whole conditionality of
`hTailF` — no more, no less. -/
def the_act : Prop := ∀ K : Nat, 8 ≤ K → noTernaryTwo (4^K) = false

/-- **THE IDENTITY.**  Through the repo's own green unconditional iff,
the act and `hTailF`'s target are one object: whatever proves the act
proves `hTailF`, and nothing weaker than the act does. -/
theorem the_act_iff_hTailF :
    the_act ↔ GSTGraphV2OmegaWaveLaw.four_power_omega_shadow_wave_tailF :=
  erdos_even_conjecture_iff_tailF

/-! ## §1 THE ANSWER — Erdős closed ⇒ hTailF closed -/

/-- The full ternary statement restricted to even exponents yields the act. -/
theorem the_act_of_full_erdos
    (hFull : ∀ n : Nat, 9 ≤ n → noTernaryTwo (2^n) = false) : the_act := by
  intro K hK
  have h4 : 4^K = 2^(2*K) := (GSTClimbTruthValue.two_pow_two_mul K).symm
  rw [h4]
  exact hFull (2 * K) (by omega)

/-- **THE ANSWER.  Erdős closed ⇒ hTailF closed, one green line.**
If the full ternary statement is proven anywhere — by boss, by any
construction, inside this repo or outside it — `hTailF` closes through
this bridge.  The conditionality of `hTailF` is exactly the act, not the
climb: the climb is overkill. -/
theorem hTailF_of_full_erdos
    (hFull : ∀ n : Nat, 9 ≤ n → noTernaryTwo (2^n) = false) :
    GSTGraphV2OmegaWaveLaw.four_power_omega_shadow_wave_tailF :=
  the_act_iff_hTailF.mp (the_act_of_full_erdos hFull)

/-- The act plus the repo's green odd-exponent half and the verified
below-floor instances assemble the FULL ternary statement. -/
theorem full_erdos_of_the_act
    (hOdd : erdos_ternary_2_conjecture_odd) (h : the_act) :
    ∀ n : Nat, 9 ≤ n → noTernaryTwo (2^n) = false := by
  intro n hn
  rcases Nat.even_or_odd n with ⟨K, hK⟩ | ⟨k, hk⟩
  · have hK2 : n = 2 * K := by omega
    rw [hK2, GSTClimbTruthValue.two_pow_two_mul]
    rcases Nat.lt_or_ge K 8 with hK8 | hK8
    · have hK5 : 5 ≤ K := by omega
      interval_cases K
      · exact GSTClimbTruthValue.no22_four_pow_five
      · exact GSTClimbTruthValue.no22_four_pow_six
      · exact GSTClimbTruthValue.no22_four_pow_seven
    · exact h K hK8
  · exact hOdd n hn (by omega)

/-- **THE ACT AND THE FULL STATEMENT ARE ONE OBJECT** — the odd-exponent
half is already green, so the even half is the whole remaining content. -/
theorem the_act_iff_full_erdos
    (hOdd : erdos_ternary_2_conjecture_odd) :
    the_act ↔ (∀ n : Nat, 9 ≤ n → noTernaryTwo (2^n) = false) :=
  ⟨full_erdos_of_the_act hOdd, the_act_of_full_erdos⟩

/-- The climb carries strictly more than the act: whoever proves the
climb proves the act (the pair demand subsumes digit-two existence).
The climb is an overkill route to `hTailF`, not a necessity. -/
theorem climb_gives_the_act
    (hClimb : GSTInfiniteFourPowerNavigation.four_power_happy_climb) :
    the_act :=
  GSTClimbTruthValue.climb_implies_erdos hClimb

/-! ## §2 THE FRONT LAW — the seed of the diagonal read -/

/-- **THE FRONT LAW.**  At the valuation cut `v`, row `v+1` of `4^(3^v * a)`
is exactly `a % 3`: the power-of-four ternary digit stream reads the
reduced exponent trit directly.  Built on the repo's own green laws —
the exact LTE identity and the one-digit exponent lift. -/
theorem front_law (v : Nat) : ∀ a : Nat,
    digit3 (4^(3^v * a)) (v + 1) = a % 3 := by
  intro a
  induction a with
  | zero =>
      have h1 : 1 < 3^(v+1) := by
        have h3 : 3^1 ≤ 3^(v+1) :=
          Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
        norm_num at h3
        omega
      have hz : 3^v * 0 = 0 := by ring
      rw [hz, Nat.pow_zero]
      unfold digit3
      rw [Nat.div_eq_of_lt h1]
  | succ a ih =>
      have hA := GSTCanonicalTailLTE.pow4_three_power_lte_exact v
      have hc := GSTCanonicalTailLTE.lteCoeff_mod3_one v
      have hstep := GSTFinalPurePowerResidueTransplant.pow4_exponent_lift_one_digit
        v (3^v * a) (GSTCanonicalTailLTE.lteCoeff v) hA hc
      rw [show 3^v * (a + 1) = 3^v * a + 3^v by ring, hstep, ih]
      omega

#print axioms the_act_iff_hTailF
#print axioms the_act_of_full_erdos
#print axioms hTailF_of_full_erdos
#print axioms full_erdos_of_the_act
#print axioms the_act_iff_full_erdos
#print axioms climb_gives_the_act
#print axioms front_law

end GSTTheAct
