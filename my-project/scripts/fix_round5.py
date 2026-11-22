# fix_round5.py — round 6 of the repair, from the full CI artifact of run
# 45071914059. Every fix is driven by an exact diagnostic:
#   - 582: rw [blockProjClosedAt_X_left] cannot see a as blockVarLeft M i
#     syntactically — establish the Fin.ext equality and subst first.
#   - 841/845/852: Finsupp.erase_add_single does not exist at v4.33.0-rc2;
#     as_sum's per-term goal has NO smul (monomial-only); the global
#     rw [hsplit] also mangles the RHS. Rebuilt: hsplit by per-index simp on
#     erase_same/erase_ne/single_eq_same/single_eq_of_ne; hmul as a ∀-coeff
#     lemma about the decomposed exponent (monomial_add_single + conv_lhs +
#     ring); the tail on rw [hsplit, hmul] + Ideal.mul_mem_left.
#   - 1031: Submodule.mem_bot takes R explicitly — (Submodule.mem_bot _).mp.
#   - 1100: Submodule.span_singleton_le_iff does not exist; the Ideal version
#     is span_singleton_le_iff_mem (RingTheory/Ideal/Span.lean:99) — used via
#     rw to dodge the explicit-argument projection disease.
#   - the descent (1113-1138): the dvd-destructure gives hgf : f = X * g
#     (not X * g = f), and MvPolynomial.totalDegree_mul at v4.33.0-rc2 is the
#     ≤-lemma (p q : polynomials), not the ≠-hypotheses equality. The descent
#     is rebuilt: the degree-shift helper (the support shifts through the
#     monomial factor — coeff_monomial_mul + le_totalDegree + the sup
#     attainment Finset.exists_mem_eq_sup) gives td g + 1 ≤ td (X * g), and
#     the induction runs on the ≤-bound.
#   - 1211: `by norm_num` is not a tactic — plain `norm_num`.
#   - 1274: IsMax at v4.33.0-rc2 consumes (η ≤ b) and returns (b ≤ η) —
#     le_antisymm hle (hmax hle) is the equation.
#   - 1312: the .1 projection on the CodimensionPoint subtype elaborates as
#     asHomogeneousIdeal in this position — destructure at the rintro and use
#     the plain witness variable.

path = '/home/z/hc-repo/GSTFiniteLinePointAlgebra.lean'
data = open(path, encoding='utf-8').read()
n0 = data

REPLACEMENTS = [
# R1 — 582: see a as blockVarLeft syntactically
("""  · have hb : b.val ≠ 2 * i.val := by
      intro hcon
      exact hab (by rw [ha, hcon])
    rw [blockProjClosedAt_X_left, blockProjClosedAt_X_ne M i hb, mul_zero]""",
"""  · have hb : b.val ≠ 2 * i.val := by
      intro hcon
      exact hab (by rw [ha, hcon])
    have haL : a = blockVarLeft M i := by
      apply Fin.ext
      show a.val = (blockVarLeft M i).val
      rw [blockVarLeft_val]
      exact ha
    subst haL
    rw [blockProjClosedAt_X_left, blockProjClosedAt_X_ne M i hb, mul_zero]"""),

# R2 — 841-853: the homogeneous_pos tail on the working route
("""  have hsplit : e = Finsupp.erase a e + Finsupp.single a (e a) :=
    (Finsupp.erase_add_single e a).symm
  have hmul : MvPolynomial.monomial e (MvPolynomial.coeff e t) =
      (X a ^ (e a - 1) *
        MvPolynomial.monomial (Finsupp.erase a e) (MvPolynomial.coeff e t)) *
        (X a : lineRing M) := by
    rw [hsplit, MvPolynomial.monomial_add_single]
    conv_lhs => rw [← Nat.sub_add_cancel ha, pow_succ]
    ring
  have hX : (X a : lineRing M) ∈
      Ideal.span (Set.range (X : Fin (2 * M) → lineRing M)) :=
    Submodule.subset_span (Set.mem_range_self a)
  rw [Algebra.smul_def, hmul, ← mul_assoc]
  exact Submodule.smul_mem _ _ hX""",
"""  have hsplit : e = Finsupp.erase a e + Finsupp.single a (e a) := by
    ext j
    by_cases hja : j = a
    · subst hja
      simp [Finsupp.add_apply, Finsupp.erase_same, Finsupp.single_eq_same]
    · simp [Finsupp.add_apply, Finsupp.erase_ne hja, Finsupp.single_eq_of_ne hja]
  have hmul : ∀ c : ℂ,
      MvPolynomial.monomial (Finsupp.erase a e + Finsupp.single a (e a)) c =
      (X a ^ (e a - 1) * MvPolynomial.monomial (Finsupp.erase a e) c) *
        (X a : lineRing M) := by
    intro c
    rw [MvPolynomial.monomial_add_single]
    conv_lhs => rw [← Nat.sub_add_cancel ha, pow_succ]
    ring
  have hX : (X a : lineRing M) ∈
      Ideal.span (Set.range (X : Fin (2 * M) → lineRing M)) :=
    Submodule.subset_span (Set.mem_range_self a)
  rw [hsplit, hmul]
  exact Ideal.mul_mem_left _ _ hX"""),

# R3 — 1031: Submodule.mem_bot takes R explicitly
("""    exact hf0 (Submodule.mem_bot.mp hfimg)""",
"""    exact hf0 ((Submodule.mem_bot _).mp hfimg)"""),

# R4 — 1100: the Ideal span_singleton_le_iff_mem via rw
("""  have hZnotin : ¬ ((X ⟨1, by omega⟩ : MvPolynomial (Fin 2) ℂ) ∈ ybar) := by
    intro hZ
    have hZle : Ideal.span {(X ⟨1, by omega⟩ : MvPolynomial (Fin 2) ℂ)} ≤ ybar :=
      Submodule.span_singleton_le_iff.mpr hZ
    exact hybarneZ (le_antisymm hybarle hZle)""",
"""  have hZnotin : ¬ ((X ⟨1, by omega⟩ : MvPolynomial (Fin 2) ℂ) ∈ ybar) := by
    intro hZ
    refine hybarneZ (le_antisymm hybarle ?_)
    rw [Ideal.span_singleton_le_iff_mem]
    exact hZ"""),

# R5 — the descent: the degree-shift helper + the ≤-induction
("""  -- THE ELEMENTARY DESCENT: every element of ȳ is zero
  have hkill : ∀ n : ℕ, ∀ f : MvPolynomial (Fin 2) ℂ,
      MvPolynomial.totalDegree f = n → f ∈ ybar → f = 0 := by
    intro n
    induction n with
    | zero =>
        intro f hfD hmem
        obtain ⟨g, hgf⟩ :=
          (Ideal.mem_span_singleton.mp (hybarle hmem) :
            (X ⟨1, by omega⟩ : MvPolynomial (Fin 2) ℂ) ∣ f)
        by_cases hg0 : g = 0
        · rw [← hgf, hg0, mul_zero]
        · rw [← hgf, MvPolynomial.totalDegree_mul
              (X_ne_zero (s := (⟨1, by omega⟩ : Fin 2))) hg0,
            MvPolynomial.totalDegree_X] at hfD
          omega
    | succ m ih =>
        intro f hfD hmem
        obtain ⟨g, hgf⟩ :=
          (Ideal.mem_span_singleton.mp (hybarle hmem) :
            (X ⟨1, by omega⟩ : MvPolynomial (Fin 2) ℂ) ∣ f)
        have hmem' : (X ⟨1, by omega⟩ : MvPolynomial (Fin 2) ℂ) * g ∈ ybar := by
          rw [hgf]; exact hmem
        rcases hybarprime.mem_or_mem hmem' with h1 | h2
        · exact absurd h1 hZnotin
        · by_cases hg0 : g = 0
          · rw [← hgf, hg0, mul_zero]
          · have hdeg : MvPolynomial.totalDegree g = m := by
              have hdd : MvPolynomial.totalDegree f =
                  MvPolynomial.totalDegree
                    ((X ⟨1, by omega⟩ : MvPolynomial (Fin 2) ℂ) * g) := by
                rw [hgf]
              rw [hdd, MvPolynomial.totalDegree_mul
                (X_ne_zero (s := (⟨1, by omega⟩ : Fin 2))) hg0,
                MvPolynomial.totalDegree_X] at hfD
              omega
            rw [← hgf, ih g hdeg h2, mul_zero]""",
"""  -- THE DEGREE-SHIFT RECEIPT: multiplying by the second variable raises the
  -- total degree by one (the support shifts through the monomial factor)
  have hge : ∀ g : MvPolynomial (Fin 2) ℂ, g ≠ 0 →
      MvPolynomial.totalDegree g + 1 ≤
        MvPolynomial.totalDegree ((X ⟨1, by omega⟩ : MvPolynomial (Fin 2) ℂ) * g) := by
    intro g hg
    obtain ⟨t, ht, htsup⟩ := Finset.exists_mem_eq_sup
      (MvPolynomial.support g) (MvPolynomial.support_nonempty_iff.mpr hg)
      (fun s => s.sum fun _ e => e)
    have hmem : (Finsupp.single (⟨1, by omega⟩ : Fin 2) 1 + t) ∈
        MvPolynomial.support ((X ⟨1, by omega⟩ : MvPolynomial (Fin 2) ℂ) * g) := by
      rw [MvPolynomial.mem_support_iff,
        show (X ⟨1, by omega⟩ : MvPolynomial (Fin 2) ℂ) =
          MvPolynomial.monomial (Finsupp.single (⟨1, by omega⟩ : Fin 2) 1) 1 from rfl,
        MvPolynomial.coeff_monomial_mul, one_mul]
      exact (MvPolynomial.mem_support_iff.mp ht)
    have hwt : (Finsupp.single (⟨1, by omega⟩ : Fin 2) 1 + t).sum (fun _ e => e) =
        1 + t.sum (fun _ e => e) := by
      rw [Finsupp.sum_add, Finsupp.sum_single_index]
      rfl
    rw [show MvPolynomial.totalDegree g = t.sum (fun _ e => e) from htsup]
    calc 1 + t.sum (fun _ e => e) =
          (Finsupp.single (⟨1, by omega⟩ : Fin 2) 1 + t).sum (fun _ e => e) := hwt.symm
      _ ≤ MvPolynomial.totalDegree
            ((X ⟨1, by omega⟩ : MvPolynomial (Fin 2) ℂ) * g) :=
            MvPolynomial.le_totalDegree hmem
  -- THE ELEMENTARY DESCENT: every element of ybar is zero
  have hkill : ∀ n : ℕ, ∀ f : MvPolynomial (Fin 2) ℂ,
      MvPolynomial.totalDegree f ≤ n → f ∈ ybar → f = 0 := by
    intro n
    induction n with
    | zero =>
        intro f hfD hmem
        obtain ⟨g, hgf⟩ :=
          (Ideal.mem_span_singleton.mp (hybarle hmem) :
            (X ⟨1, by omega⟩ : MvPolynomial (Fin 2) ℂ) ∣ f)
        by_cases hg0 : g = 0
        · rw [hgf, hg0, mul_zero]
        · exfalso
          have h1 := hge g hg0
          rw [← hgf] at h1
          omega
    | succ m ih =>
        intro f hfD hmem
        obtain ⟨g, hgf⟩ :=
          (Ideal.mem_span_singleton.mp (hybarle hmem) :
            (X ⟨1, by omega⟩ : MvPolynomial (Fin 2) ℂ) ∣ f)
        have hmem' : (X ⟨1, by omega⟩ : MvPolynomial (Fin 2) ℂ) * g ∈ ybar := by
          rw [← hgf]; exact hmem
        rcases hybarprime.mem_or_mem hmem' with h1 | h2
        · exact absurd h1 hZnotin
        · by_cases hg0 : g = 0
          · rw [hgf, hg0, mul_zero]
          · rw [hgf, ih g (by
              have h1 := hge g hg0
              rw [← hgf] at h1
              omega) h2, mul_zero]"""),

# R6 — 1211: by norm_num is not a tactic
("""      rw [hwgen, lineGenericPoint_coheight M i]
      by norm_num""",
"""      rw [hwgen, lineGenericPoint_coheight M i]
      norm_num"""),

# R7 — 1274: hmax hle is the reverse point-le; le_antisymm closes
("""  exact hmax ((le_iff_ideal M η
    (lineGenericPoint M ⟨a.val / 2, by have := a.isLt; omega⟩)).mpr hgen)""",
"""  have hle : η ≤ lineGenericPoint M ⟨a.val / 2, by have := a.isLt; omega⟩ :=
    (le_iff_ideal M η
      (lineGenericPoint M ⟨a.val / 2, by have := a.isLt; omega⟩)).mpr hgen
  exact le_antisymm hle (hmax hle)"""),

# R8 — 1312: destructure the second witness; no dotted projections
("""  rintro ⟨η', hη'⟩ hxη'
  obtain ⟨k, hk⟩ := exists_eq_lineGenericPoint M η hη
  obtain ⟨k', hk'⟩ := exists_eq_lineGenericPoint M (η'.1) η'.2""",
"""  rintro ⟨η'v, hη'⟩ hxη'
  obtain ⟨k, hk⟩ := exists_eq_lineGenericPoint M η hη
  obtain ⟨k', hk'⟩ := exists_eq_lineGenericPoint M η'v hη'"""),

# R8b — 1344: the Subtype.ext on the destructured form
("""  have hηeq : η = η' := by rw [hk, hk', hkk]
  exact Subtype.ext hηeq.symm""",
"""  have hηeq : η = η'v := by rw [hk, hk', hkk]
  exact Subtype.ext hηeq.symm"""),
]

total = 0
failed = []
for old, new in REPLACEMENTS:
    n = data.count(old)
    if n == 1:
        data = data.replace(old, new)
        total += 1
    elif n == 0:
        failed.append(old.strip().splitlines()[0][:80])
    else:
        print(f"AMBIGUOUS ({n}x): {old.strip().splitlines()[0][:80]}")
        data = data.replace(old, new)
        total += 1

open(path, 'w', encoding='utf-8').write(data)
print("changed:", data != n0, "| replacements applied:", total)
if failed:
    print("PATTERNS NOT FOUND:")
    for f in failed:
        print("  -", f)

probes = [
  ("blockVarLeft subst", "have haL : a = blockVarLeft M i := by", True),
  ("erase hsplit simp", "Finsupp.erase_ne hja", True),
  ("hmul forall", "have hmul : ∀ c : ℂ,", True),
  ("mul_mem_left tail", "exact Ideal.mul_mem_left _ _ hX", True),
  ("mem_bot applied", "(Submodule.mem_bot _).mp", True),
  ("span_singleton_le_iff_mem", "rw [Ideal.span_singleton_le_iff_mem]", True),
  ("hge helper", "Finset.exists_mem_eq_sup", True),
  ("le-induction", "MvPolynomial.totalDegree f ≤ n → f ∈ ybar → f = 0", True),
  ("no totalDegree_mul-eq uses", "MvPolynomial.totalDegree_mul", False),
  ("no X_ne_zero ascriptions", "X_ne_zero (s :=", False),
  ("norm_num plain", "lineGenericPoint_coheight M i]\n      norm_num", True),
  ("no by norm_num tactic", "by norm_num", False),
  ("hmax le_antisymm", "exact le_antisymm hle (hmax hle)", True),
  ("destructured witness", "exists_eq_lineGenericPoint M η'v hη'", True),
  ("no eta'.1 dots", "exists_eq_lineGenericPoint M (η'.1)", False),
  ("hetaeq primed", "have hetaeq", False),
]
ok = True
for desc, probe, want in probes:
    got = probe in data
    status = "OK " if got == want else "BAD"
    if got != want: ok = False
    print(f"{status} {desc}: found={got} expected={want}")
print("ALL OK" if ok and not failed else ("PATTERNS MISSED" if failed else "ISSUES REMAIN"))
