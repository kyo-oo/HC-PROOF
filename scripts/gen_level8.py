#!/usr/bin/env python3
"""
gen_level8.py — S098 THE EIGHTH CASCADE LEVEL (the main repo, the boss's
worldtrace arithmetic, one storey deeper).

Computes, two-method:
  - the noise d(r) = digit3 (4^r) 9 for every level-7 survivor parent r
    (method A: direct 4^r mod 3^11; method B: the quintic blade
    4 + 252m + 15876C(m,2) + 1000188C(m,3) + 63011844C(m,4) + 3969746172C(m,5)
    mod 59049, r = 1+3m) — both must agree;
  - the 128 dead classes mod 19683 (dead child t = 2 - d);
  - the 256 survivors mod 19683;
  - emits the complete Lean section (level-8 storey) to stdout.
English only.
"""
from math import comb

# ---- extract the 128 level-7 survivors from the Lean source ----
import re
src = open("GSTWorldtraceArithmetic.lean").read()
# the last conjunct of the_worldtrace_receipt_seven: cantorian_dust_mod_6561's list
start = src.index("theorem cantarian_dust_mod_6561")
seg = src[start:start + 20000]
end = seg.index(":=")
body = seg[:end]
parents = [int(x) for x in re.findall(r"K % 6561 = (\d+)", body)]
assert len(parents) == 128, f"parent count {len(parents)}"
assert parents[0] == 1 and parents[1] == 4

M3_11 = 3 ** 11          # 177147: row-9 read window
M3_10 = 3 ** 10          # 59049: the quintic blade modulus


def digit9_direct(r):
    """Method A: 4^r mod 3^11, digit 9."""
    return (pow(4, r, M3_11) // (3 ** 9)) % 3


def digit9_blade(r):
    """Method B: the quintic blade at m = (r-1)/3, digit 9."""
    assert r % 3 == 1
    m = (r - 1) // 3
    v = (4 + 252 * m + 15876 * comb(m, 2) + 1000188 * comb(m, 3)
         + 63011844 * comb(m, 4) + 3969746172 * comb(m, 5)) % M3_10
    # digit 9 of the blade value: needs mod 3^11 window on the representative
    v11 = v % M3_11
    return (v11 // (3 ** 9)) % 3


dead = []       # (parent r, dead child class r + 6561*t)
survivors = []
CHECKS = 0
for r in parents:
    dA = digit9_direct(r)
    dB = digit9_blade(r)
    assert dA == dB, f"TWO-METHOD FAIL at r={r}: {dA} vs {dB}"
    t = 2 - dA
    dead.append((r, t, r + 6561 * t))
    for tt in (0, 1, 2):
        if tt != t:
            survivors.append(r + 6561 * tt)
    CHECKS += 1

assert len(dead) == 128 and len(survivors) == 256
# sanity: the true Cantorian dust exponents 1 and 4 must survive every
# level (K = 40, 121, ... are only lower-level survivors — the cascade
# killing them at level 8 is CORRECT behavior: 4^40 fires at row 9)
for k in (1, 4):
    assert k in survivors, f"true Cantorian exponent {k} died?!"
killed_known = [k for k in (40, 121, 364, 523) if k not in survivors]
print(f"level-7 survivors killed at level 8 (correct cascade kills): "
      f"{killed_known}")

# survivors sorted, dead sorted by class value
dead_sorted = sorted(set(c for (_, _, c) in dead))
assert len(dead_sorted) == 128
survivors_sorted = sorted(set(survivors))
assert len(survivors_sorted) == 256

# ---- the noise receipt map for the Lean generator: parent -> m0 ----
def m0(r):
    assert r % 3 == 1
    return (r - 1) // 3

dead_by_class = {c: (r, t) for (r, t, c) in dead}

# ---- emit the Lean ----
L = []
A = L.append
A("/-! ## §5b The eighth cascade level — the map doubles to 256 -/")
A("")
A("/-- **THE SIX-TERM LADDER.**  The binomial expansion carried one term")
A("deeper: the tail begins at the sixth power. -/")
A("theorem one_add_pow_six_term (x j : Nat) :")
A("    ∃ R : Nat, (1+x)^j = 1 + j*x + Nat.choose j 2 * x * x")
A("      + Nat.choose j 3 * x * x * x + Nat.choose j 4 * x * x * x * x")
A("      + Nat.choose j 5 * x * x * x * x * x")
A("      + x*x*x*x*x*x*R := by")
A("  induction j with")
A("  | zero =>")
A("    have h02 : Nat.choose 0 2 = 0 := by decide")
A("    have h03 : Nat.choose 0 3 = 0 := by decide")
A("    have h04 : Nat.choose 0 4 = 0 := by decide")
A("    have h05 : Nat.choose 0 5 = 0 := by decide")
A("    refine ⟨0, ?_⟩")
A("    rw [Nat.pow_zero, h02, h03, h04, h05]")
A("    ring")
A("  | succ j ih =>")
A("    obtain ⟨R, hR⟩ := ih")
A("    have hc2 : Nat.choose (j+1) 2 = j + Nat.choose j 2 := by")
A("      rw [Nat.choose_succ_succ j 1, wt_choose_one j]")
A("    have hc3 : Nat.choose (j+1) 3 = Nat.choose j 2 + Nat.choose j 3 :=")
A("      Nat.choose_succ_succ j 2")
A("    have hc4 : Nat.choose (j+1) 4 = Nat.choose j 3 + Nat.choose j 4 :=")
A("      Nat.choose_succ_succ j 3")
A("    have hc5 : Nat.choose (j+1) 5 = Nat.choose j 4 + Nat.choose j 5 :=")
A("      Nat.choose_succ_succ j 4")
A("    rw [Nat.pow_succ, hR, hc2, hc3, hc4, hc5]")
A("    refine ⟨Nat.choose j 5 + R + x*R, ?_⟩")
A("    ring")
A("")
A("/-- **THE QUINTIC BLADE.**  Three windows deeper: `4^(1+3m)` is the")
A("quintic blade mod 59049 — the order-five worldtrace.  (63^6 =")
A("3^12 * 7^6 dies mod 3^10 = 59049.) -/")
A("theorem wt_quintic_mod59049 (m : Nat) :")
A("    4^(1+3*m) ≡ 4 + 252*m + 15876*Nat.choose m 2")
A("      + 1000188*Nat.choose m 3 + 63011844*Nat.choose m 4")
A("      + 3969746172*Nat.choose m 5 [MOD 59049] := by")
A("  obtain ⟨R, hR⟩ := one_add_pow_six_term 63 m")
A("  have h64 : (64:Nat) = 1 + 63 := by decide")
A("  have hexp : 4 * (1 + m*63 + Nat.choose m 2 * 63 * 63")
A("        + Nat.choose m 3 * 63 * 63 * 63 + Nat.choose m 4 * 63 * 63 * 63 * 63")
A("        + Nat.choose m 5 * 63 * 63 * 63 * 63 * 63")
A("        + 63*63*63*63*63*63*R)")
A("      = 4 + 252*m + 15876*Nat.choose m 2 + 1000188*Nat.choose m 3")
A("        + 63011844*Nat.choose m 4 + 3969746172*Nat.choose m 5")
A("        + 250094008836*R := by ring")
A("  rw [wt_rebase, h64, hR, hexp]")
A("  show (4 + 252*m + 15876*Nat.choose m 2 + 1000188*Nat.choose m 3")
A("        + 63011844*Nat.choose m 4 + 3969746172*Nat.choose m 5")
A("        + 250094008836*R) % 59049")
A("     = (4 + 252*m + 15876*Nat.choose m 2 + 1000188*Nat.choose m 3")
A("        + 63011844*Nat.choose m 4 + 3969746172*Nat.choose m 5) % 59049")
A("  have hd : 59049 ∣ 250094008836*R := by")
A("    refine ⟨4235364*R, ?_⟩")
A("    ring")
A("  have hz : 250094008836*R % 59049 = 0 := Nat.mod_eq_zero_of_dvd hd")
A("  omega")
A("")
A("/-- **ROW NINE IS THE QUINTIC.**  For EVERY m: the ninth row of the")
A("dust power is the ninth row of the quintic blade. -/")
A("theorem wt_row_nine_read (m : Nat) :")
A("    digit3 (4^(1+3*m)) 9")
A("      = digit3 (4 + 252*m + 15876*Nat.choose m 2 + 1000188*Nat.choose m 3")
A("          + 63011844*Nat.choose m 4 + 3969746172*Nat.choose m 5) 9 := by")
A("  have h59049 : (3:Nat)^(9+1) = 59049 := by decide")
A("  have h := wt_quintic_mod59049 m")
A("  rw [← h59049] at h")
A("  exact digit3_eq_of_mod_next _ _ _ h")
A("")
A("/-- **THE QUINTIC KILL DEMO.**  The quintic blade reads digit two at")
A("row nine on the first self-firing parent (its dead child is itself," )
A("`t = 0`), without computing any deep power of four. -/")
DEMO_R = next(r for (r, t, c) in dead if t == 0)
A(f"theorem wt_quintic_fire_demo : digit3 (4^(1+3*{m0(DEMO_R)})) 9 = 2 := by")
A("  rw [wt_row_nine_read]")
A("  decide")
A("")
A("/-- **THE UNIFORM KILL, LEVEL-EIGHT FORM.**  `K ≡ r + 6561*t mod 19683`")
A("fires at row nine when the noise receipt holds.  All arithmetic")
A("literal. -/")
A("theorem fire_of_mod19683 (K r t : Nat)")
A("    (hr : r < 6561) (ht : t < 3)")
A("    (hnoise : (digit3 (4^r) 9 + t) % 3 = 2)")
A("    (hclass : K % 19683 = r + 6561 * t) :")
A("    digit3 (4^K) 9 = 2 := by")
A("  have h19683 : (3:Nat)^(8+1) = 19683 := by decide")
A("  have h6561 : (3:Nat)^8 = 6561 := by decide")
A("  have hK : K % 3^(8+1) = r + 3^8 * t := by")
A("    rw [h19683, h6561]")
A("    exact hclass")
A("  have hr' : r < 3^8 := by")
A("    rw [h6561]")
A("    exact hr")
A("  exact feedback_fire_of_class 8 r t K hr' ht hnoise hK")
A("")
# dust_fire_row_nine: the 128-entry disjunction + dispatch
A("/-- **CASCADE LEVEL EIGHT (row nine).**  Every exponent in one of the")
A("one hundred twenty-eight dead classes mod 19683 fires its digit two")
A("at row nine.  Generated from the worldtrace noise receipts")
A("(`noise_8(r) = digit3 (4^r) 9`, dead child `t = 2 - noise`, dead class")
A("`r + 6561*t`) — the eighth storey of the feedback tree, each node")
A("keeping exactly two alive children (`unique_dead_child`). -/")
A("theorem dust_fire_row_nine (K : Nat)")
A("    (hK : " + " ∨ ".join(f"K % 19683 = {c}" for c in dead_sorted) + ") :")
A("    digit3 (4^K) 9 = 2 := by")
A("  rcases hK with " + " ".join(f"h{c}" for c in dead_sorted))
for c in dead_sorted:
    r, t = dead_by_class[c]
    A(f"  · exact fire_of_mod19683 K {r} {t} (by decide) (by decide) (by rw [show ({r}:Nat) = 1 + 3*{m0(r)} from by decide, wt_row_nine_read]; decide) (by omega)")
A("")
# no22_of_cascade_eight
A("/-- **THE CASCADE KILL, LEVEL EIGHT.**  The one hundred twenty-eight")
A("new classes die outright through the repo's own kill chain. -/")
A("theorem no22_of_cascade_eight (K : Nat)")
A("    (h : " + " ∨ ".join(f"K % 19683 = {c}" for c in dead_sorted) + ") :")
A("    noTernaryTwo (4^K) = false :=")
A("  no22_of_digit_two K 9 (dust_fire_row_nine K h)")
A("")
# cantarian_dust_mod_19683: the exclusion haves + final rcases
A("/-- **THE DUST PINNED AT LEVEL EIGHT — THE MAP DOUBLES AGAIN.**  A")
A("Cantorian dust exponent (`K ≡ 1 mod 3`) lives in one of TWO HUNDRED")
A("FIFTY-SIX surviving residues mod 19683.  The structural law, fifth")
A("stroke: `2, 4, 8, 16, 32, 64, 128, 256` — the alive set doubles")
A("level by level without exception, every node keeping exactly two")
A("children by the blade's one-of-three. -/")
A("theorem cantarian_dust_mod_19683 (K : Nat)")
A("    (hd : K % 3 = 1) (hc : CantorianPower K) :")
A("    K % 19683 = " + " ∨ K % 19683 = ".join(str(c) for c in survivors_sorted) + " := by")
A("  have h6561 := cantarian_dust_mod_6561 K hd hc")
A("  have hrow := hc 9 (by omega)")
for i, c in enumerate(dead_sorted):
    # the level-7 idiom: the exclusion uses the LAMBDA's own variable h,
    # nested into the disjunction position of this dead class
    term = "(Or.inl h)"
    for _ in range(i):
        term = f"(Or.inr {term})"
    A(f"  have hd{i} : K % 19683 ≠ {c} :=")
    A(f"    fun h => absurd (dust_fire_row_nine K {term}) hrow")
A("  rcases h6561 with " + " ".join(f"h{p}" for p in parents) + " <;> omega")
A("")
# the receipt
A("/-- **THE LEVEL-EIGHT RECEIPT.**  The worldtrace transformation, one")
A("more storey deeper: the six-term ladder, the quintic blade, the")
A("row-nine read, the quintic kill demo, the uniform engine at level")
A("eight, the one hundred twenty-eight fires, the kill chain, and the")
A("re-doubled survivor map (128 -> 256). -/")
A("theorem the_worldtrace_receipt_eight :")
A("    (∀ m : Nat, ∃ R : Nat, (1+63)^m")
A("      = 1 + m*63 + Nat.choose m 2 * 63 * 63 + Nat.choose m 3 * 63 * 63 * 63")
A("        + Nat.choose m 4 * 63 * 63 * 63 * 63")
A("        + Nat.choose m 5 * 63 * 63 * 63 * 63 * 63")
A("        + 63*63*63*63*63*63*R) ∧")
A("    (∀ m : Nat, 4^(1+3*m) ≡ 4 + 252*m + 15876*Nat.choose m 2")
A("      + 1000188*Nat.choose m 3 + 63011844*Nat.choose m 4")
A("      + 3969746172*Nat.choose m 5 [MOD 59049]) ∧")
A("    (∀ m : Nat, digit3 (4^(1+3*m)) 9")
A("      = digit3 (4 + 252*m + 15876*Nat.choose m 2 + 1000188*Nat.choose m 3")
A("          + 63011844*Nat.choose m 4 + 3969746172*Nat.choose m 5) 9) ∧")
A(f"    (digit3 (4^(1+3*{m0(DEMO_R)})) 9 = 2) ∧")
A("    (∀ K r t : Nat, r < 6561 → t < 3 →")
A("      (digit3 (4^r) 9 + t) % 3 = 2 → K % 19683 = r + 6561 * t →")
A("      digit3 (4^K) 9 = 2) ∧")
A("    (∀ K : Nat, K % 19683 = " + " ∨ K % 19683 = ".join(str(c) for c in dead_sorted) + " → digit3 (4^K) 9 = 2) ∧")
A("    (∀ K : Nat, K % 19683 = " + " ∨ K % 19683 = ".join(str(c) for c in dead_sorted) + " → noTernaryTwo (4^K) = false) ∧")
A("    (∀ K : Nat, K % 3 = 1 → CantorianPower K →")
A("      K % 19683 = " + " ∨ K % 19683 = ".join(str(c) for c in survivors_sorted) + ") :=")
A("  ⟨fun m => one_add_pow_six_term 63 m,")
A("    wt_quintic_mod59049, wt_row_nine_read, wt_quintic_fire_demo,")
A("    fire_of_mod19683, dust_fire_row_nine, no22_of_cascade_eight,")
A("    cantarian_dust_mod_19683⟩")
A("")
# axiom prints
for s in ["one_add_pow_six_term", "wt_quintic_mod59049", "wt_row_nine_read",
          "wt_quintic_fire_demo", "fire_of_mod19683", "dust_fire_row_nine",
          "no22_of_cascade_eight", "cantarian_dust_mod_19683",
          "the_worldtrace_receipt_eight"]:
    A(f"#print axioms {s}")
A("")

open("level8_section.lean", "w").write("\n".join(L))
print(f"parents checked (two-method): {CHECKS}")
print(f"dead classes: {len(dead_sorted)} (first: {dead_sorted[:6]})")
print(f"survivors: {len(survivors_sorted)} (first: {survivors_sorted[:8]})")
print("level8_section.lean written:", len("\n".join(L).splitlines()), "lines")
