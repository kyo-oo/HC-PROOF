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
    """  | succ m ih =>
      simp only [Nat.add_succ, reverseMixedCode, pow_succ]
      rw [ih]
      ring
""",
    """  | succ m ih =>
      simp only [Nat.add_succ, reverseMixedCode, pow_succ]
      have ih' :
          reverseMixedCode C d (Nat.add n m) =
            (4 : Int)^m * reverseMixedCode C d n +
              reverseMixedCode (fun i => C (n+i)) (fun i => d (n+i)) m := by
        simpa only using ih
      rw [ih']
      ring
""",
)

replace_once(
    "GSTGraphV2CanonicalDescentOntology.lean",
    """  exact prefix_slice_quotient_exact (s+2) 1 (canonicalTail (s+1) n) q
    (one_prefix_bounds (s+2) (by omega)).1
""",
    """  exact GSTGraphV2InfiniteControl.prefix_slice_quotient_exact
    (s+2) 1 (canonicalTail (s+1) n) q
    (one_prefix_bounds (s+2) (by omega)).1
""",
)

replace_once(
    "GSTTailFProof.lean",
    """theorem tower_observation_iff_interval (s core j d : Nat) :
    digit3 (4^(3^s*core)) (s+1+j) = d ↔
      d * 3^j ≤ omegaCutWord s core % 3^(j+1) ∧
      omegaCutWord s core % 3^(j+1) < (d+1)*3^j := by
  have hprefix : (1:Nat) < 3^(s+1) := by
    have h := Nat.pow_le_pow_of_le (by decide : 1 < (3:Nat))
      (show 1 ≤ s+1 by omega)
    norm_num at h
    omega
  rw [omega_cut_factor s core,
    prefix_slice_digit_exact (s+1) 1 (omegaCutWord s core) j hprefix]
  unfold digit3
  rw [digit3_window]
  set r := omegaCutWord s core % 3^(j+1)
  set m := 3^j
  have hm : 0 < m := Nat.pow_pos (by decide)
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
    """theorem tower_observation_iff_interval (s core j d : Nat) :
    digit3 (4^(3^s*core)) (s+1+j) = d ↔
      d * 3^j ≤ omegaCutWord s core % 3^(j+1) ∧
      omegaCutWord s core % 3^(j+1) < (d+1)*3^j := by
  have hprefix : (1:Nat) < 3^(s+1) := by
    have h := Nat.pow_le_pow_of_le (by decide : 1 < (3:Nat))
      (show 1 ≤ s+1 by omega)
    norm_num at h
    omega
  rw [omega_cut_factor s core,
    GSTGraphV2InfiniteControl.prefix_slice_digit_exact
      (s+1) 1 (omegaCutWord s core) j hprefix]
  unfold digit3
  rw [digit3_window]
  set r := omegaCutWord s core % 3^(j+1)
  set m := 3^j
  have hm : 0 < m := Nat.pow_pos (by decide)
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

replace_once(
    "waves/GSTVortexSingularityV2.lean",
    """theorem core_rotation_no_early_return (C d k : Nat)
    (hC : C < 4) (hd : d < 3) (hk : 0 < k) (hk5 : k < 5)
    (haxis : ¬ ((C = 0 ∧ d = 0) ∨ (C = 3 ∧ d = 2))) :
    coreRotate^[k] (C,d) ≠ (C,d) := by
  interval_cases C <;> interval_cases d <;> interval_cases k <;>
    norm_num at haxis ⊢ <;> decide
""",
    """theorem core_rotation_no_early_return (C d k : Nat)
    (hC : C < 4) (hd : d < 3) (hk : 0 < k) (hk5 : k < 5)
    (haxis : ¬ ((C = 0 ∧ d = 0) ∨ (C = 3 ∧ d = 2))) :
    coreRotate^[k] (C,d) ≠ (C,d) := by
  have hk' : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
  rcases hk' with rfl | rfl | rfl | rfl <;>
    interval_cases C <;> interval_cases d <;>
    norm_num [coreRotate, Function.iterate_succ_apply] at haxis ⊢
""",
)
