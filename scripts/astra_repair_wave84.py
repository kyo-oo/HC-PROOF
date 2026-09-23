from pathlib import Path


def replace_once(path: str, old: str, new: str) -> None:
    p = Path(path)
    text = p.read_text()
    count = text.count(old)
    if count != 1:
        raise SystemExit(f"{path}: expected exactly one target, found {count}")
    p.write_text(text.replace(old, new))


# 1) Keep reverseMixedCode_add on the native recursion orientation.
replace_once(
    "GSTFinalPrefixOneStep6Infinite.lean",
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
    """  | succ m ih =>
      rw [Nat.add_succ, reverseMixedCode, reverseMixedCode, ih, pow_succ]
      ring
""",
)

# 2) Let simp_all discharge both axial contradictions and finite non-axis computations.
replace_once(
    "waves/GSTVortexSingularityV2.lean",
    """  rcases hk' with rfl | rfl | rfl | rfl <;>
    interval_cases C <;> interval_cases d <;>
    norm_num [coreRotate, Function.iterate_succ_apply] at haxis ⊢
""",
    """  rcases hk' with rfl | rfl | rfl | rfl <;>
    interval_cases C <;> interval_cases d <;>
    simp_all [coreRotate, Function.iterate_succ_apply]
""",
)

# 3) Ghost-ray reverse implication is Presburger arithmetic over Nat bounds.
replace_once(
    "GSTGhostRayExclusion.lean",
    """    constructor <;> nlinarith
""",
    """    constructor <;> omega
""",
)

# 4a) Merge the orphaned consecutive Worldtrace doc comments.
replace_once(
    "GSTWorldtraceArithmetic.lean",
    """/-- **THE GENERAL PAIR-READ KILL.**  The family dies outright through
the repo's own kill chain. -/
/-- The residue kill zone is necessary as well as sufficient, already from
depth two; it exactly classifies the pair-read digit. -/
""",
    """/-- **THE GENERAL PAIR-READ EXACT CLASSIFIER.**  The residue kill zone is
necessary as well as sufficient, already from depth two; it exactly classifies
the pair-read digit and therefore the corresponding kill channel. -/
""",
)

# 4b) Factor the row-two converse into a direct one-variable residue fact,
# avoiding the old omega call over two unrelated symbolic products.
replace_once(
    "GSTWorldtraceArithmetic.lean",
    """theorem pair_read_fire_iff (T u j : Nat) (hj : 2 ≤ j)
    (hT : 4^T < 3^(j+2)) :
    digit3 (4^(T + 3^(j+1)*u)) (j+4) = 2 ↔
      18 ≤ (4^T * u * 16) % 27 := by
  rw [pair_read_formula T u j (by omega) hT]
  have hres := pair_residue_mod27 T u j hj
  change (4^T * u * GSTTowerFire.c (j+1)) / 9 % 3 = 2 ↔ _
  omega
""",
    """theorem digit3_row_two_iff_residue (x : Nat) :
    digit3 x 2 = 2 ↔ 18 ≤ x % 27 := by
  constructor
  · intro hx
    have hlt : x % 27 < 27 := Nat.mod_lt _ (by decide : 0 < 27)
    change x / 9 % 3 = 2 at hx
    omega
  · exact digit3_row_two_of_residue x

theorem pair_read_fire_iff (T u j : Nat) (hj : 2 ≤ j)
    (hT : 4^T < 3^(j+2)) :
    digit3 (4^(T + 3^(j+1)*u)) (j+4) = 2 ↔
      18 ≤ (4^T * u * 16) % 27 := by
  rw [pair_read_formula T u j (by omega) hT]
  rw [digit3_row_two_iff_residue]
  rw [pair_residue_mod27 T u j hj]
""",
)
