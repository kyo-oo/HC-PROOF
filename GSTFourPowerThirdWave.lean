import GSTFourPowerDirectExistence
import GSTFourPowerExponentTritObstruction

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# The Third Wave: band reformulation of the four-power direct existence law

For every row `p`, the third-wave gate records a row digit two together with
its exact outer-quarter prefix band.  The file identifies this geometric gate
with the common-two existence predicate and then links the same gate to the
recursive exponent-prefix killing-trit geometry.
-/

namespace GSTFourPowerThirdWave

open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence
open GSTFourPowerExponentTritObstruction

/-- Outer quarter-band condition on the row-`p` prefix of `4^K`. -/
def prefixBand (K p : Nat) : Prop :=
  4 * (4^K % 3^p) < 3^p ∨ 3 * 3^p ≤ 4 * (4^K % 3^p)

/-- The row-`p` gate of the third wave. -/
def thirdWaveRow (K p : Nat) : Prop :=
  digit3 (4^K) p = 2 ∧ prefixBand K p

/-- The third wave of `K`: some positive row gate fires. -/
def thirdWave (K : Nat) : Prop :=
  ∃ p : Nat, 1 ≤ p ∧ thirdWaveRow K p

/-- Row law in the lowest quarter band. -/
theorem digit3_four_mul_of_lt (R p : Nat)
    (hband : 4 * (R % 3^p) < 3^p) :
    digit3 (4 * R) p = (4 * (R / 3^p)) % 3 := by
  have hpow : 0 < 3^p := Nat.pow_pos (by decide)
  have hR : R % 3^p + 3^p * (R / 3^p) = R := Nat.mod_add_div R (3^p)
  have h4R : 4 * R = 4 * (R % 3^p) + 3^p * (4 * (R / 3^p)) := by
    calc
      4 * R = 4 * (R % 3^p + 3^p * (R / 3^p)) := by rw [hR]
      _ = 4 * (R % 3^p) + 3^p * (4 * (R / 3^p)) := by ring
  unfold digit3
  rw [h4R, Nat.add_mul_div_left _ _ hpow, Nat.div_eq_of_lt hband]
  omega

/-- Row law in the highest quarter band. -/
theorem digit3_four_mul_of_ge (R p : Nat)
    (hband : 3 * 3^p ≤ 4 * (R % 3^p)) :
    digit3 (4 * R) p = (4 * (R / 3^p) + 3) % 3 := by
  have hpow : 0 < 3^p := Nat.pow_pos (by decide)
  have hs : 4 * (R % 3^p) =
      (4 * (R % 3^p) - 3 * 3^p) + 3^p * 3 := by omega
  have hslt : 4 * (R % 3^p) - 3 * 3^p < 3^p := by omega
  have hdiv : 4 * (R % 3^p) / 3^p = 3 := by
    rw [hs, Nat.add_mul_div_left _ _ hpow, Nat.div_eq_of_lt hslt]
  have hR : R % 3^p + 3^p * (R / 3^p) = R := Nat.mod_add_div R (3^p)
  have h4R : 4 * R = 4 * (R % 3^p) + 3^p * (4 * (R / 3^p)) := by
    calc
      4 * R = 4 * (R % 3^p + 3^p * (R / 3^p)) := by rw [hR]
      _ = 4 * (R % 3^p) + 3^p * (4 * (R / 3^p)) := by ring
  unfold digit3
  rw [h4R, Nat.add_mul_div_left _ _ hpow, hdiv]
  omega

/-- Row law in the second quarter band. -/
theorem digit3_four_mul_of_mid1 (R p : Nat)
    (hlo : 3^p ≤ 4 * (R % 3^p)) (hhi : 4 * (R % 3^p) < 2 * 3^p) :
    digit3 (4 * R) p = (4 * (R / 3^p) + 1) % 3 := by
  have hpow : 0 < 3^p := Nat.pow_pos (by decide)
  have hs : 4 * (R % 3^p) =
      (4 * (R % 3^p) - 3^p) + 3^p * 1 := by omega
  have hslt : 4 * (R % 3^p) - 3^p < 3^p := by omega
  have hdiv : 4 * (R % 3^p) / 3^p = 1 := by
    rw [hs, Nat.add_mul_div_left _ _ hpow, Nat.div_eq_of_lt hslt]
  have hR : R % 3^p + 3^p * (R / 3^p) = R := Nat.mod_add_div R (3^p)
  have h4R : 4 * R = 4 * (R % 3^p) + 3^p * (4 * (R / 3^p)) := by
    calc
      4 * R = 4 * (R % 3^p + 3^p * (R / 3^p)) := by rw [hR]
      _ = 4 * (R % 3^p) + 3^p * (4 * (R / 3^p)) := by ring
  unfold digit3
  rw [h4R, Nat.add_mul_div_left _ _ hpow, hdiv]
  omega

/-- Row law in the third quarter band. -/
theorem digit3_four_mul_of_mid2 (R p : Nat)
    (hlo : 2 * 3^p ≤ 4 * (R % 3^p)) (hhi : 4 * (R % 3^p) < 3 * 3^p) :
    digit3 (4 * R) p = (4 * (R / 3^p) + 2) % 3 := by
  have hpow : 0 < 3^p := Nat.pow_pos (by decide)
  have hs : 4 * (R % 3^p) =
      (4 * (R % 3^p) - 2 * 3^p) + 3^p * 2 := by omega
  have hslt : 4 * (R % 3^p) - 2 * 3^p < 3^p := by omega
  have hdiv : 4 * (R % 3^p) / 3^p = 2 := by
    rw [hs, Nat.add_mul_div_left _ _ hpow, Nat.div_eq_of_lt hslt]
  have hR : R % 3^p + 3^p * (R / 3^p) = R := Nat.mod_add_div R (3^p)
  have h4R : 4 * R = 4 * (R % 3^p) + 3^p * (4 * (R / 3^p)) := by
    calc
      4 * R = 4 * (R % 3^p + 3^p * (R / 3^p)) := by rw [hR]
      _ = 4 * (R % 3^p) + 3^p * (4 * (R / 3^p)) := by ring
  unfold digit3
  rw [h4R, Nat.add_mul_div_left _ _ hpow, hdiv]
  omega

/-- Row-pair overlap is exactly the third-wave outer-band gate. -/
theorem row_pair_iff_band (K p : Nat) :
    (digit3 (4^K) p = 2 ∧ digit3 (4^(K+1)) p = 2) ↔
      thirdWaveRow K p := by
  have hpow4 : 4^(K+1) = 4 * 4^K := by
    rw [Nat.pow_succ]
    ring
  unfold thirdWaveRow prefixBand
  constructor
  · rintro ⟨hd, hd2⟩
    refine ⟨hd, ?_⟩
    rw [hpow4] at hd2
    by_cases h1 : 4 * (4^K % 3^p) < 3^p
    · exact Or.inl h1
    · by_cases h3 : 3 * 3^p ≤ 4 * (4^K % 3^p)
      · exact Or.inr h3
      · by_cases h2 : 4 * (4^K % 3^p) < 2 * 3^p
        · rw [digit3_four_mul_of_mid1 (4^K) p (by omega) h2] at hd2
          exfalso
          unfold digit3 at hd
          omega
        · rw [digit3_four_mul_of_mid2 (4^K) p (by omega) (by omega)] at hd2
          exfalso
          unfold digit3 at hd
          omega
  · rintro ⟨hd, hband⟩
    refine ⟨hd, ?_⟩
    rw [hpow4]
    rcases hband with hlow | hhigh
    · rw [digit3_four_mul_of_lt (4^K) p hlow]
      unfold digit3 at hd
      omega
    · rw [digit3_four_mul_of_ge (4^K) p hhigh]
      unfold digit3 at hd
      omega

/-- The third wave is the direct existence law exponent by exponent. -/
theorem thirdWave_iff_commonTwo (K : Nat) :
    thirdWave K ↔ CommonTwo K := by
  constructor
  · rintro ⟨p, hp1, hd, hband⟩
    exact ⟨p, hp1, (row_pair_iff_band K p).mpr ⟨hd, hband⟩⟩
  · rintro ⟨p, hp1, hd, hd2⟩
    exact ⟨p, hp1, (row_pair_iff_band K p).mp ⟨hd, hd2⟩⟩

/-- The full direct-existence law restated in wave language. -/
theorem fourPowerDirectExistence_iff_thirdWave :
    FourPowerDirectExistence ↔ ∀ K : Nat, 5 ≤ K → K ≠ 7 → thirdWave K := by
  constructor
  · intro h K hK5 hK7
    exact (thirdWave_iff_commonTwo K).mpr (h K hK5 hK7)
  · intro h K hK5 hK7
    exact (thirdWave_iff_commonTwo K).mp (h K hK5 hK7)

/-- Every established row-two overlap class fires the third wave. -/
theorem thirdWave_of_mod9_five_or_six (K : Nat)
    (hres : K % 9 = 5 ∨ K % 9 = 6) : thirdWave K := by
  obtain ⟨p, hp1, hd, hd2⟩ := commonTwo_of_mod9_five_or_six K hres
  exact ⟨p, hp1, (row_pair_iff_band K p).mp ⟨hd, hd2⟩⟩

/-- Every established row-three overlap class fires the third wave. -/
theorem thirdWave_of_mod27_row_three (K : Nat)
    (hres : K % 27 = 14 ∨ K % 27 = 18 ∨ K % 27 = 19 ∨ K % 27 = 25) :
    thirdWave K := by
  obtain ⟨p, hp1, hd, hd2⟩ := commonTwo_of_mod27_row_three K hres
  exact ⟨p, hp1, (row_pair_iff_band K p).mp ⟨hd, hd2⟩⟩

/-- **THIRD-WAVE / KILLING-TRIT EQUIVALENCE.**  The geometric third wave
fires exactly when some exponent-prefix scale hits its unique killing trit. -/
theorem thirdWave_iff_exists_killingTrit_hit (K : Nat) :
    thirdWave K ↔
      ∃ p : Nat,
        digit3 (4^(exponentPrefix K p)) (p+1) =
          digit3 (4^((exponentPrefix K p)+1)) (p+1) ∧
        exponentTrit K p = killingTrit K p := by
  rw [thirdWave_iff_commonTwo]
  exact commonTwo_iff_exists_killingTrit_hit K

/-- A gate is determined by a finite exponent class uniformly at every row
and with arbitrary offsets. -/
theorem thirdWaveRow_reduce_offset (K p t : Nat) :
    thirdWaveRow (K+t) p ↔ thirdWaveRow (K % 3^p+t) p := by
  rw [← row_pair_iff_band, ← row_pair_iff_band]
  rw [pow4_digit_reduce_offset p K t]
  have hs := pow4_digit_reduce_offset p K (t+1)
  simpa only [Nat.add_assoc] using
    Iff.of_eq (congrArg (fun d : Nat => d = 2) hs)

/-- Every gate produces an infinite family of gates at its original row. -/
theorem thirdWaveRow_period (K p u : Nat) :
    thirdWaveRow (K + 3^p*u) p ↔ thirdWaveRow K p := by
  rw [← row_pair_iff_band, ← row_pair_iff_band, pow4_digit_period]
  rw [show K + 3^p*u + 1 = (K+1) + 3^p*u by omega, pow4_digit_period]

#print axioms row_pair_iff_band
#print axioms thirdWave_iff_commonTwo
#print axioms fourPowerDirectExistence_iff_thirdWave
#print axioms thirdWave_iff_exists_killingTrit_hit
#print axioms thirdWaveRow_reduce_offset
#print axioms thirdWaveRow_period

end GSTFourPowerThirdWave
