# fix_round4.py — round 4 of the GSTFiniteLinePointAlgebra.lean repair, from the
# full CI artifact of run 45069401431 (the round-3 push). Every fix below is
# driven by an exact compiler diagnostic:
#   - 341/577: `simp only [RingHom.mem_ker]` made no progress (the membership
#     pattern never matches syntactically); the following `show` carries the
#     defeq change alone — drop the simp line.
#   - 816: `exact key x y hc` applied an Iff as a function — `(key x y).mp hc`.
#   - 849-852 (homogeneous_pos_mem_span_X): the Finsupp subtraction-application
#     never splits on ℕ-valued Finsupps (Finsupp.coe_sub unused, the if-omega
#     goal unsplittable) and `Submodule.smul_mem` cannot eat the ℂ-Algebra-smul
#     of `as_sum`. Rebuilt on the subtraction-free decomposition
#     `Finsupp.erase_add_single` + the pin's `MvPolynomial.monomial_add_single`,
#     with `Algebra.smul_def` bridging the smul to the ring product.
#   - 1010: `Ideal.eq_top_iff_one` exists in v4.33.0-rc2 but takes I
#     explicitly — `(Ideal.eq_top_iff_one _).mpr`.
#   - 1028: U+0233 (ȳ) is not a Lean identifier character — all ȳ-identifiers
#     renamed to ybar-forms (hybarne/hybarle/hybarneZ).
#   - 1174: congrArg forced the ProjectiveSpectrum order onto le_antisymm while
#     hle lives at the carrier's Scheme-preorder — the equality is now derived
#     at the toIdeal level (le_antisymm on ideals, unambiguous) inside
#     le_iff_ideal's world.
#   - 1220: `rw [heq]` already closes by rfl — drop the surplus `exact le_rfl`.
#   - 1222: exact_mod_cast could not cast (0:ℕ)<1 to the ℕ∞ level — `by norm_num`.
#   - 1223: the strict hypotheses are Preorder-lt (`a ≤ b ∧ ¬ b ≤ a`), not
#     `a ≠ b` — the anonymous second components are now the ¬(b ≤ a) proofs.
#   - 1231/1311: the deprecated ENat.coe_le_coe / ENat.coe_lt_top replaced by
#     ENat.natCast_le_natCast / ENat.natCast_lt_top.
#   - 1286: `IsMax` is `∀ ⋏b, a ≤ b → a = b` — `hmax hle` IS the equation
#     η = lineGenericPoint …; the lt_or_eq_of_le dance is replaced by
#     `exact hmax hle`.
#   - 1297/1301: lineIndexOfGeneric_spec needs `.symm` (choose_spec gives
#     ↑η = lineGenericPoint …) and lineIndexOfGeneric_lineGenericPoint loses
#     its `.symm`.
#   - 1330: rewriting the subtype variable η' inside its own coercion is a
#     dependent rewrite (motive not type correct) — the second obtain is now
#     driven through the projections `(η'.1)` / `η'.2`.
#   - 1344: the goal is ⟨η', hη'⟩ = η₀, so Subtype.ext needs `hηeq.symm`.
#   - 1351: lineComponentOf's anonymous-constructor put the choose (already a
#     CodimensionPoint) in the value slot of a Subtype — the definition is now
#     just the choose; above/unique follow by defeq.
#   - 1373: `lineClosedPointAt_lt M` was missing its `i` argument.

path = '/home/z/hc-repo/GSTFiniteLinePointAlgebra.lean'
data = open(path, encoding='utf-8').read()
n0 = data

REPLACEMENTS = [
# 341 — the mem_ker simp line is dead weight; the show carries the change
("""  rintro _ ⟨a, b, hab, rfl⟩
  simp only [RingHom.mem_ker]
  show blockProjAt M i (X a * X b) = 0""",
"""  rintro _ ⟨a, b, hab, rfl⟩
  show blockProjAt M i (X a * X b) = 0"""),
# 577 — same
("""  rintro _ ⟨a, b, hab, rfl⟩
  simp only [RingHom.mem_ker]
  show blockProjClosedAt M i (X a * X b) = 0""",
"""  rintro _ ⟨a, b, hab, rfl⟩
  show blockProjClosedAt M i (X a * X b) = 0"""),
# 816 — an Iff is not a function
("""    exact key x y hc""",
"""    exact (key x y).mp hc"""),
# 849-852 — the homogeneous_pos tail on the erase/monomial_add_single route
("""  have hsplit : e = Finsupp.single a 1 + (e - Finsupp.single a 1) := by
    ext j
    simp only [Finsupp.add_apply, Finsupp.coe_sub, Pi.sub_apply,
      Finsupp.single_apply]
    by_cases hja : j = a
    · subst hja
      simp only [if_pos rfl]
      omega
    · simp only [if_neg hja]
      omega
  have hX : (X a : lineRing M) ∈
      Ideal.span (Set.range (X : Fin (2 * M) → lineRing M)) :=
    Submodule.subset_span (Set.mem_range_self a)
  have hmul : MvPolynomial.monomial e (MvPolynomial.coeff e t) =
      (X a : lineRing M) *
        MvPolynomial.monomial (e - Finsupp.single a 1) (MvPolynomial.coeff e t) := by
    rw [show (X a : lineRing M) =
      MvPolynomial.monomial (Finsupp.single a 1) 1 from rfl, MvPolynomial.monomial_mul,
      hsplit]
  rw [hmul, mul_comm]
  exact Submodule.smul_mem _ _ hX""",
"""  have hsplit : e = Finsupp.erase a e + Finsupp.single a (e a) :=
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
  exact Submodule.smul_mem _ _ hX"""),
# 1010 — Ideal.eq_top_iff_one takes I explicitly
("""      exact y.isPrime.ne_top (Ideal.eq_top_iff_one.mpr hgoal)""",
"""      exact y.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr hgoal)"""),
# 1174 — the equality at the ideal level (no cross-order le_antisymm)
("""    have hle : lineClosedPointAt M i ≤ lineGenericPoint M i :=
      (le_iff_ideal M (lineClosedPointAt M i) (lineGenericPoint M i)).mpr
        (by rw [lineClosedPointAt_asIdeal, lineGenericPoint_asIdeal];
            exact lineGenericIdeal_le_lineClosedIdealAt M i)
    have hII : (lineClosedPointAt M i).asHomogeneousIdeal =
        (lineGenericPoint M i).asHomogeneousIdeal :=
      congrArg ProjectiveSpectrum.asHomogeneousIdeal (le_antisymm hle heq)
    have h1' := congrArg HomogeneousIdeal.toIdeal hII
    rw [lineClosedPointAt_asIdeal, lineGenericPoint_asIdeal] at h1'
    rw [← h1']
    exact h1""",
"""    have hI : (lineClosedPointAt M i).asHomogeneousIdeal.toIdeal =
        (lineGenericPoint M i).asHomogeneousIdeal.toIdeal :=
      le_antisymm ((le_iff_ideal M (lineGenericPoint M i) (lineClosedPointAt M i)).mp heq)
        ((le_iff_ideal M (lineClosedPointAt M i) (lineGenericPoint M i)).mp
          ((le_iff_ideal M (lineClosedPointAt M i) (lineGenericPoint M i)).mpr
            (by rw [lineClosedPointAt_asIdeal, lineGenericPoint_asIdeal];
                exact lineGenericIdeal_le_lineClosedIdealAt M i)))
    rw [lineClosedPointAt_asIdeal, lineGenericPoint_asIdeal] at hI
    rw [← hI]
    exact h1"""),
# 1220 — rw [heq] closes by rfl
("""    · have hwgen : w = lineGenericPoint M i :=
        eq_lineGenericPoint_of_le M i w (by rw [heq]; exact le_rfl)
      rw [hwgen, lineGenericPoint_coheight M i]
      exact_mod_cast (by norm_num : (0 : ℕ) < (1 : ℕ))""",
"""    · have hwgen : w = lineGenericPoint M i :=
        eq_lineGenericPoint_of_le M i w (by rw [heq])
      rw [hwgen, lineGenericPoint_coheight M i]
      by norm_num"""),
# 1223 — Preorder-lt's second component is ¬ (b ≤ a)
("""    · exact absurd (no_intermediate_pointAt M i w ⟨hgen, hne.symm⟩ ⟨hwle, hwne⟩)
        False.elim""",
"""    · exact absurd
        (no_intermediate_pointAt M i w
          ⟨hgen, fun hle => hne (le_antisymm hle hgen)⟩
          ⟨hwle, fun hle => hwne (le_antisymm hwle hle)⟩) False.elim"""),
# 1231/1232 — the new ENat names
("""  have hn1 : n ≤ 1 := ENat.coe_le_coe.mp hupper
  have hn2 : 1 ≤ n := ENat.coe_le_coe.mp hlower""",
"""  have hn1 : n ≤ 1 := ENat.natCast_le_natCast.mp hupper
  have hn2 : 1 ≤ n := ENat.natCast_le_natCast.mp hlower"""),
# 1311 — the new ENat name in the coheight-zero receipt
("""    first
    | exact ENat.coe_lt_top 1
    | simp""",
"""    first
    | exact ENat.natCast_lt_top 1
    | simp"""),
# 1286 — IsMax is ∀ ⋏b, a ≤ b → a = b: hmax hle IS the equation
("""  have hle : η ≤ lineGenericPoint M ⟨a.val / 2, by have := a.isLt; omega⟩ :=
    (le_iff_ideal M η (lineGenericPoint M ⟨a.val / 2, by have := a.isLt; omega⟩)).mpr hgen
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact (hmax hlt).elim
  · exact heq""",
"""  exact hmax ((le_iff_ideal M η
    (lineGenericPoint M ⟨a.val / 2, by have := a.isLt; omega⟩)).mpr hgen)"""),
# 1297 — choose_spec points the other way
("""theorem lineIndexOfGeneric_spec (M : ℕ)
    (η : CodimensionPoint (finiteLineScheme M) 0) :
    lineGenericPoint M (lineIndexOfGeneric M η) = η.1 :=
  Classical.choose_spec (exists_eq_lineGenericPoint M η.1 η.2)""",
"""theorem lineIndexOfGeneric_spec (M : ℕ)
    (η : CodimensionPoint (finiteLineScheme M) 0) :
    lineGenericPoint M (lineIndexOfGeneric M η) = η.1 :=
  (Classical.choose_spec (exists_eq_lineGenericPoint M η.1 η.2)).symm"""),
# 1301 — and the injectivity consumes it un-symmed
("""  lineIndexOfGeneric M ⟨lineGenericPoint M i, lineGenericPoint_coheight M i⟩ = i :=
  lineGenericPoint_injective M (lineIndexOfGeneric_spec M _).symm""",
"""  lineIndexOfGeneric M ⟨lineGenericPoint M i, lineGenericPoint_coheight M i⟩ = i :=
  lineGenericPoint_injective M (lineIndexOfGeneric_spec M _)"""),
# 1330 — the subtype projection route for the second witness
("""  obtain ⟨k', hk'⟩ := exists_eq_lineGenericPoint M η' hη'""",
"""  obtain ⟨k', hk'⟩ := exists_eq_lineGenericPoint M (η'.1) η'.2"""),
# 1344 — the goal is ⟨η', hη'⟩ = η₀
("""  have hηeq : η = η' := by rw [hk, hk', hkk]
  exact Subtype.ext hηeq""",
"""  have hηeq : η = η' := by rw [hk, hk', hkk]
  exact Subtype.ext hηeq.symm"""),
# 1351 — the definition IS the choose
("""noncomputable def lineComponentOf (M : ℕ)
    (x : CodimensionPoint (finiteLineScheme M) 1) :
    CodimensionPoint (finiteLineScheme M) 0 :=
  ⟨Classical.choose (exists_unique_generic_above M x),
    by
      obtain ⟨η₀, hlt, huniq⟩ := exists_unique_generic_above M x
      have hch : Classical.choose (exists_unique_generic_above M x) = η₀ :=
        huniq _ (Classical.choose_spec (exists_unique_generic_above M x)).1
      rw [hch]
      exact η₀.2⟩""",
"""noncomputable def lineComponentOf (M : ℕ)
    (x : CodimensionPoint (finiteLineScheme M) 1) :
    CodimensionPoint (finiteLineScheme M) 0 :=
  Classical.choose (exists_unique_generic_above M x)"""),
# 1373 — the i-argument
("""  (lineComponentOf_unique M _ _ (lineClosedPointAt_lt M)).symm""",
"""  (lineComponentOf_unique M _ _ (lineClosedPointAt_lt M i)).symm"""),
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

# the U+0233 kill (not a Lean identifier character)
if '\u0233' in data:
    nb = data.count('\u0233')
    data = data.replace('\u0233', 'ybar')
    total += 1
    print(f"U+0233: replaced {nb} occurrences (hȳne -> hybarne, hȳle -> hybarle, ...)")
# guard: no other non-ASCII in identifier positions we touched
for ch, name in [('\u0303', 'COMBINING TILDE'), ('\u0304', 'COMBINING MACRON')]:
    if ch in data:
        print(f"WARNING: {name} still present x{data.count(ch)}")

open(path, 'w', encoding='utf-8').write(data)
print("changed:", data != n0, "| replacements applied:", total)
if failed:
    print("PATTERNS NOT FOUND:")
    for f in failed:
        print("  -", f)

# ---- self-check probes ------------------------------------------------------
probes = [
  ("no mem_ker simp", "simp only [RingHom.mem_ker]", False),
  ("iff applied via mp", "exact (key x y).mp hc", True),
  ("erase decomposition", "Finsupp.erase_add_single e a", True),
  ("monomial_add_single", "MvPolynomial.monomial_add_single", True),
  ("smul bridge", "rw [Algebra.smul_def, hmul, ← mul_assoc]", True),
  ("eq_top_iff_one applied", "(Ideal.eq_top_iff_one _).mpr hgoal", True),
  ("no bare eq_top", "Ideal.eq_top_iff_one.mpr", False),
  ("ideal-level antisymm", "le_antisymm ((le_iff_ideal M (lineGenericPoint M i) (lineClosedPointAt M i)).mp heq)", True),
  ("rw closes itself", "eq_lineGenericPoint_of_le M i w (by rw [heq])", True),
  ("norm_num cast", "by norm_num\n  have hne", False),
  ("preorder-lt components", "fun hle => hne (le_antisymm hle hgen)", True),
  ("preorder-lt hstrict", "fun hle => hwne (le_antisymm hwle hle)", True),
  ("new ENat le", "ENat.natCast_le_natCast.mp", True),
  ("new ENat lt", "ENat.natCast_lt_top 1", True),
  ("IsMax direct", "exact hmax ((le_iff_ideal M η", True),
  ("no lt_or_eq dance", "rcases lt_or_eq_of_le hle", False),
  ("spec symm", "(Classical.choose_spec (exists_eq_lineGenericPoint M η.1 η.2)).symm", True),
  ("injective unsymmed", "lineGenericPoint_injective M (lineIndexOfGeneric_spec M _)\n", True),
  ("projection obtain", "exists_eq_lineGenericPoint M (η'.1) η'.2", True),
  ("subtype ext symm", "exact Subtype.ext hηeq.symm", True),
  ("def is choose", "  Classical.choose (exists_unique_generic_above M x)\n\ntheorem lineComponentOf_above", True),
  ("no anon ctor def", "⟨Classical.choose (exists_unique_generic_above M x),", False),
  ("i-arg restored", "(lineClosedPointAt_lt M i)).symm", True),
  ("no U+0233", "\u0233", False),
  ("hybarne present", "hybarne", True),
  ("hybarle present", "hybarle", True),
]
ok = True
for desc, probe, want in probes:
    got = probe in data
    status = "OK " if got == want else "BAD"
    if got != want: ok = False
    print(f"{status} {desc}: found={got} expected={want}")
print("ALL OK" if ok and not failed else ("PATTERNS MISSED" if failed else "ISSUES REMAIN"))
