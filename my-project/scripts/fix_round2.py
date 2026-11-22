path = '/home/z/hc-repo/GSTFiniteLinePointAlgebra.lean'
data = open(path).read()
n0 = data

# 1. blockVarFamily values: full simp closes the if-True reduction
data = data.replace(
"""    blockVarFamily M i (blockVarLeft M i) = (X \u27e80, by omega\u27e9 : MvPolynomial (Fin 2) \u2102) := by
  simp only [blockVarFamily, blockVarLeft_val]""",
"""    blockVarFamily M i (blockVarLeft M i) = (X \u27e80, by omega\u27e9 : MvPolynomial (Fin 2) \u2102) := by
  simp [blockVarFamily, blockVarLeft_val]""")
data = data.replace(
"""    blockVarFamily M i (blockVarRight M i) = (X \u27e81, by omega\u27e9 : MvPolynomial (Fin 2) \u2102) := by
  simp only [blockVarFamily, blockVarRight_val]""",
"""    blockVarFamily M i (blockVarRight M i) = (X \u27e81, by omega\u27e9 : MvPolynomial (Fin 2) \u2102) := by
  simp [blockVarFamily, blockVarRight_val]""")

# 2. blockInclAt_X_zero/one: the congr-1 closes by defeq; drop the tail
data = data.replace(
"""  show (X (\u27e82 * i.val + 0, by have := i.isLt; omega\u27e9 : Fin (2 * M)) : lineRing M) =
    (X (blockVarLeft M i) : lineRing M)
  congr 1
  apply Fin.ext
  show (2 * i.val + 0 : \u2115) = (blockVarLeft M i).val
  rw [blockVarLeft_val]
  omega""",
"""  show (X (\u27e82 * i.val + 0, by have := i.isLt; omega\u27e9 : Fin (2 * M)) : lineRing M) =
    (X (blockVarLeft M i) : lineRing M)
  rfl""")
data = data.replace(
"""  show (X (\u27e82 * i.val + 1, by have := i.isLt; omega\u27e9 : Fin (2 * M)) : lineRing M) =
    (X (blockVarRight M i) : lineRing M)
  congr 1
  apply Fin.ext
  show (2 * i.val + 1 : \u2115) = (blockVarRight M i).val
  rw [blockVarRight_val]
  omega""",
"""  show (X (\u27e82 * i.val + 1, by have := i.isLt; omega\u27e9 : Fin (2 * M)) : lineRing M) =
    (X (blockVarRight M i) : lineRing M)
  rfl""")

# 3. crossIdeal-le-ker sites: simp-only mem_ker (coercion-friendly)
data = data.replace(
"""  rintro _ \u27e8a, b, hab, rfl\u27e9
  rw [RingHom.mem_ker]
  show blockProjAt M i (X a * X b) = 0""",
"""  rintro _ \u27e8a, b, hab, rfl\u27e9
  simp only [RingHom.mem_ker]
  show blockProjAt M i (X a * X b) = 0""")
data = data.replace(
"""  rintro _ \u27e8a, b, hab, rfl\u27e9
  rw [RingHom.mem_ker]
  show blockProjClosedAt M i (X a * X b) = 0""",
"""  rintro _ \u27e8a, b, hab, rfl\u27e9
  simp only [RingHom.mem_ker]
  show blockProjClosedAt M i (X a * X b) = 0""")

# 4. X_ne_zero anonymous-constructor sites: ascribe the Fin-literal
data = data.replace(
"""  rw [blockProjQuotAt_X_left M i] at hz
  exact X_ne_zero \u27e80, by omega\u27e9 hz""",
"""  rw [blockProjQuotAt_X_left M i] at hz
  exact X_ne_zero (s := (\u27e80, by omega\u27e9 : Fin 2)) hz""")
data = data.replace(
"""  rw [blockProjQuotAt_X_right M i] at hz
  exact X_ne_zero \u27e81, by omega\u27e9 hz""",
"""  rw [blockProjQuotAt_X_right M i] at hz
  exact X_ne_zero (s := (\u27e81, by omega\u27e9 : Fin 2)) hz""")
data = data.replace(
"""  rw [blockProjClosedQuotAt_mk, blockProjClosedAt_X_left] at hz
  exact X_ne_zero \u27e80, by omega\u27e9 hz""",
"""  rw [blockProjClosedQuotAt_mk, blockProjClosedAt_X_left] at hz
  exact X_ne_zero (s := (\u27e80, by omega\u27e9 : Fin 1)) hz""")
# the descent's X_ne_zero sites (post-parser-death, same disease)
data = data.replace(
"""        \u00b7 rw [hgf, MvPolynomial.totalDegree_mul (X_ne_zero \u27e81, by omega\u27e9) hg0,""",
"""        \u00b7 rw [hgf, MvPolynomial.totalDegree_mul
            (X_ne_zero (s := (\u27e81, by omega\u27e9 : Fin 2))) hg0,""")
data = data.replace(
"""              rw [hdd, MvPolynomial.totalDegree_mul (X_ne_zero \u27e81, by omega\u27e9) hg0,""",
"""              rw [hdd, MvPolynomial.totalDegree_mul
                (X_ne_zero (s := (\u27e81, by omega\u27e9 : Fin 2))) hg0,""")

# 5. le_iff_ideal's key: the ProjectiveSpectrum-typed statement
data = data.replace(
"""  have key : \u2200 a b : finiteLineScheme M,
      a \u2208 closure ({b} : Set (finiteLineScheme M)) \u2194
        b.asHomogeneousIdeal.toIdeal \u2264 a.asHomogeneousIdeal.toIdeal := by""",
"""  have key : \u2200 a b : ProjectiveSpectrum (lineGrading M),
      a \u2208 closure ({b} : Set (ProjectiveSpectrum (lineGrading M))) \u2194
        b.asHomogeneousIdeal.toIdeal \u2264 a.asHomogeneousIdeal.toIdeal := by""")

# 6a. homogeneous_pos: the forall-injection for hcon
data = data.replace(
"""    by_contra hcon
    have hcon' : \u2200 j : Fin (2 * M), \u00ac(0 < e j) := fun j => hcon j
    have he0 : e = 0 := Finsupp.ext fun j => by
      have := hcon' j
      simp only [Finsupp.zero_apply]
      omega""",
"""    by_contra hcon
    have hcon' : \u2200 j : Fin (2 * M), \u00ac(0 < e j) := fun j h' => hcon \u27e8j, h'\u27e9
    have he0 : e = 0 := Finsupp.ext fun j => by
      have := hcon' j
      simp only [Finsupp.zero_apply]
      omega""")

# 6b. hsplit: the reversed ite-condition + the coe_sub reduction
data = data.replace(
"""  have hsplit : e = Finsupp.single a 1 + (e - Finsupp.single a 1) := by
    ext j
    simp only [Finsupp.add_apply, Finsupp.sub_apply, Finsupp.single_apply]
    by_cases hja : j = a
    \u00b7 rw [hja]
      simp only [if_pos rfl]
      omega
    \u00b7 rw [if_neg hja, if_neg hja]
      omega""",
"""  have hsplit : e = Finsupp.single a 1 + (e - Finsupp.single a 1) := by
    ext j
    simp only [Finsupp.coe_sub, Pi.sub_apply, Finsupp.single_apply]
    by_cases hja : j = a
    \u00b7 subst hja
      simp only [if_pos rfl]
      omega
    \u00b7 simp only [if_neg (fun hcon => hja hcon.symm)]
      omega""")

# 6c. the span-mul ending
data = data.replace(
"""  rw [hmul, mul_comm]
  exact Submodule.smul_mem _ _ hX""",
"""  rw [hmul]
  exact Ideal.mul_mem_left _ _ hX""")

# 7. irrelevant_le's image destructure
data = data.replace(
"""    rw [Ideal.map_span, Ideal.span_le]
    rintro _ \u27e8a, rfl\u27e9
    exact h a""",
"""    rw [Ideal.map_span, Ideal.span_le]
    rintro _ \u27e8a, \u27e8b, rfl\u27e9, rfl\u27e9
    show (lineQuotientMap M) (X b) \u2208 I
    exact h b""")

# 8. exists_variable_not_mem: add not_not
data = data.replace(
"""  by_contra hcon
  simp only [not_exists] at hcon""",
"""  by_contra hcon
  simp only [not_exists, not_not] at hcon""")

# 9. coheight's le_iff argument order (IsMax gives LGP <= z)
data = data.replace(
"""  have hzle : z.asHomogeneousIdeal.toIdeal \u2264 lineGenericIdeal M i :=
    (le_iff_ideal M z (lineGenericPoint M i)).mp hle""",
"""  have hzle : z.asHomogeneousIdeal.toIdeal \u2264 lineGenericIdeal M i :=
    (le_iff_ideal M (lineGenericPoint M i) z).mp hle""")

# 10. sup_le -> sup_le_iff
data = data.replace(
"""  \u00b7 refine sup_le.mpr \u27e8lineGenericIdeal_le_lineClosedIdealAt M i, ?_\u27e9""",
"""  \u00b7 refine sup_le_iff.mpr \u27e8lineGenericIdeal_le_lineClosedIdealAt M i, ?_\u27e9""")
data = data.replace(
"""    rw [lineClosedIdealAt_eq_supAt M i, sup_le]""",
"""    rw [lineClosedIdealAt_eq_supAt M i, sup_le_iff]""")

# 11. the combining-tilde b-digits
data = data.replace('\u0062\u0303', 'bbar')

open(path, 'w').write(data)
print("changed:", data != n0)
for probe, want in [
  ("simp [blockVarFamily, blockVarLeft_val]", True),
  ("rfl\"\"\"", False), ("apply Fin.ext\n  show (2 * i.val + 0", False),
  ("simp only [RingHom.mem_ker]", True),
  ("X_ne_zero (s := (\u27e80, by omega\u27e9 : Fin 2)) hz", True),
  ("X_ne_zero (s := (\u27e80, by omega\u27e9 : Fin 1)) hz", True),
  (": ProjectiveSpectrum (lineGrading M),", True),
  ("fun j h' => hcon \u27e8j, h'\u27e9", True),
  ("Finsupp.coe_sub, Pi.sub_apply", True),
  ("Ideal.mul_mem_left _ _ hX", True),
  ("\u27e8a, \u27e8b, rfl\u27e9, rfl\u27e9", True),
  ("not_exists, not_not", True),
  ("(lineGenericPoint M i) z).mp hle", True),
  ("sup_le_iff.mpr", True),
  ("sup_le_iff]", True),
  ('\u0303', False),
]:
    got = probe in data
    print(("OK " if got == want else "BAD"), repr(probe[:60]), got)
