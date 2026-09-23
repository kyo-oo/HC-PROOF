from pathlib import Path


def replace_once(path: str, old: str, new: str) -> None:
    p = Path(path)
    text = p.read_text()
    count = text.count(old)
    if count != 1:
        raise SystemExit(f"{path}: expected exactly one target, found {count}")
    p.write_text(text.replace(old, new))


replace_once(
    "GSTFinalPrefixOneStep6Infinite.lean",
    """  induction m with
  | zero => simp [reverseMixedCode]
  | succ m ih =>
      simp only [Nat.add_assoc, reverseMixedCode, ih, pow_succ]
      ring
""",
    """  induction m with
  | zero => simp [reverseMixedCode]
  | succ m ih =>
      simp only [Nat.add_succ, reverseMixedCode, pow_succ]
      rw [ih]
      ring
""",
)

replace_once(
    "GSTGraphV2OmegaWaveLaw.lean",
    """theorem omega_observed_digit_iff_interval
    (s core k d : Nat) (hk : 1 ≤ k) (hks : k ≤ s+1) :
    digit3 (4^(3^s * core)) (s+k) = d ↔
      d * 3^(k-1) ≤ (omegaCutWord s 1 * core) % 3^k ∧
      (omegaCutWord s 1 * core) % 3^k < (d+1) * 3^(k-1) := by
  rw [omega_observed_digit s core k hk hks]
  set r := (omegaCutWord s 1 * core) % 3^k
  set m := 3^(k-1)
  have hm : 0 < m := by dsimp [m]; positivity
  constructor
  · intro h
    have he := Nat.mod_add_div r m
    have hb := Nat.mod_lt r hm
    rw [h] at he
    constructor <;> nlinarith
  · rintro ⟨hlo, hhi⟩
    have he : r = (r-d*m) + m*d := by omega
    have hb : r-d*m < m := by nlinarith
    rw [he, Nat.add_mul_div_left _ _ hm, Nat.div_eq_of_lt hb]
    simp
""",
    """theorem omega_observed_digit_iff_interval
    (s core k d : Nat) (hk : 1 ≤ k) (hks : k ≤ s+1) :
    digit3 (4^(3^s * core)) (s+k) = d ↔
      d * 3^(k-1) ≤ (omegaCutWord s 1 * core) % 3^k ∧
      (omegaCutWord s 1 * core) % 3^k < (d+1) * 3^(k-1) := by
  rw [omega_observed_digit s core k hk hks]
  set r := (omegaCutWord s 1 * core) % 3^k
  set m := 3^(k-1)
  have hm : 0 < m := by dsimp [m]; positivity
  constructor
  · intro h
    have he := Nat.mod_add_div r m
    have hb := Nat.mod_lt r hm
    rw [h] at he
    have he' : r % m + d * m = r := by
      simpa [Nat.mul_comm] using he
    constructor
    · omega
    · calc
        r = r % m + d * m := he'.symm
        _ < m + d * m := Nat.add_lt_add_right hb (d * m)
        _ = (d + 1) * m := by simp [Nat.add_mul, Nat.add_comm]
  · rintro ⟨hlo, hhi⟩
    exact Nat.div_eq_of_lt_le hlo hhi
""",
)
