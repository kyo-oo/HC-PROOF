from pathlib import Path


def replace_once(path: str, old: str, new: str) -> None:
    p = Path(path)
    text = p.read_text()
    n = text.count(old)
    if n != 1:
        raise SystemExit(f"{path}: expected exactly one target, found {n}")
    p.write_text(text.replace(old, new))

replace_once(
    "GSTGhostRayExclusion.lean",
    """    rw [hpow] at heq
    constructor <;> omega
""",
    """    rw [hpow] at heq
    generalize hr : (GSTTowerFire.c (k-1) * u) % 3^k = r at heq ⊢
    generalize ha : (GSTTowerFire.c 1 * u) % 9 = a at heq
    generalize hpw : 3^(k-1) = p at heq ⊢
    have ha_lt : a < 9 := by
      rw [← ha]
      exact Nat.mod_lt _ (by decide)
    have hp_ge : 9 ≤ p := by
      simpa [hpw] using hp
    constructor <;> omega
""",
)

replace_once(
    "GSTHodgeAssaultV2.lean",
    """    have h0 : ¬ (C = 0 ∧ d = 0) := by omega
    have h1 : ¬ (C = 1 ∧ d = 1) := by omega
    have h2 : ¬ (C = 2 ∧ d = 2) := by omega
""",
    """    have hoff : C ≠ d := hc
    have h0 : ¬ (C = 0 ∧ d = 0) := by
      rintro ⟨hC0, hd0⟩
      exact hoff (hC0.trans hd0.symm)
    have h1 : ¬ (C = 1 ∧ d = 1) := by
      rintro ⟨hC1, hd1⟩
      exact hoff (hC1.trans hd1.symm)
    have h2 : ¬ (C = 2 ∧ d = 2) := by
      rintro ⟨hC2, hd2⟩
      exact hoff (hC2.trans hd2.symm)
""",
)
