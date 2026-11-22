# fix_round3.py — the comprehensive round-3 repair of GSTFiniteLinePointAlgebra.lean
# at 9547ac1 (wave 4-A full repair + the surviving fix_round2 receipts, corrected).
#
# Fixes (each verified against the CI run 45057688805 and the Mathlib pins):
#   A. the namespace opens (CodimensionPoint / codimensionPointCycle from
#      GSTNativeCodimensionCyclePresentation, codimensionCycles from
#      GSTGeometricRealizationStage2D) — kills the whole autoImplicit family
#      at 1302-1418.
#   B. no_intermediate_pointAt's hgen made STRICT (the <= version is false at
#      the generic point); all internal hgen uses become hgen.le.
#   C. hround/hsurj rebuilt through lineQuotientMap (blockInclAt lands in
#      lineRing, blockProjQuotAt eats lineQuotient).
#   D. hgoal's w - (w - 1) (the w - 1 + 1 = 1 thinko), eq_top_iff_one.
#   E. hmapclosed: the map_zero hole-rw replaced by an explicit hout; the
#      second branch gets the lineClosedIdealAt/map_span unfolds so hmem
#      matches the goal.
#   F. hȳneZ's ending on le_antisymm + sup_le (constructor form).
#   G. the hkill descent block: rw directions corrected (hgf : X*g = f, so
#      every use is ← hgf except hmem' which is hgf), X_ne_zero ascriptions.
#   H. lineClosedPointAt_lt: congrArg needs an Eq — build it with
#      le_antisymm hle heq.
#   I. lineClosedPointAt_coheight rebuilt on the green ENat ladder receipt
#      (GSTClassicalHodgeSeparatorRelativeCoheightOne.lean:113-138) with the
#      explicit ((1 : ℕ) : ℕ∞) cast so coheight_le_coe_iff's rw matches.
#   J. eq_lineGenericPoint_of_le branch 2's phantom `b`.
#   K. hsplit on Finsupp.add_apply + coe_sub/Pi.sub_apply + if_neg hja.
#   L. lineGenericPoint_injective's rw direction; exists_eq_lineGenericPoint's
#      IsMax elimination (hmax hlt : False — IsMax = ∀ ⋃b, ¬ a < b).
#   M. exists_unique_generic_above: ← lineGenericPoint_asIdeal (x2), the
#      Fin.ext wrapper, lineClosedPointAt_component's .symm.
#   N. codimensionPointCycle_ne_zero on the green simp set.
#   Plus the surviving fix_round2 receipts (correct ones only):
#   blockVarFamily simp, blockInclAt_X rfl, mem_ker simp only, X_ne_zero
#   ascriptions (443/450/675), key ProjectiveSpectrum, hcon' injection,
#   irrelevant image destructure, not_not, coheight order, sup_le_iff,
#   b-combining-tilde -> bbar.

path = '/home/z/hc-repo/GSTFiniteLinePointAlgebra.lean'
data = open(path, encoding='utf-8').read()
n0 = data

REPLACEMENTS = [
# ---- A. the opens -----------------------------------------------------------
("""open AlgebraicGeometry CategoryTheory
open GSTProjectiveOverC GSTFiniteLineRing GSTFiniteLineWorldCarrier""",
"""open AlgebraicGeometry CategoryTheory
open GSTProjectiveOverC GSTFiniteLineRing GSTFiniteLineWorldCarrier
open GSTNativeCodimensionCyclePresentation GSTGeometricRealizationStage2D"""),

# ---- B. hgen strict ---------------------------------------------------------
("""theorem no_intermediate_pointAt (M : ℕ) (i : Fin M) (y : finiteLineScheme M)
    (hgen : lineGenericIdeal M i ≤ y.asHomogeneousIdeal.toIdeal)
    (hstrict : y.asHomogeneousIdeal.toIdeal < lineClosedIdealAt M i) :""",
"""theorem no_intermediate_pointAt (M : ℕ) (i : Fin M) (y : finiteLineScheme M)
    (hgen : lineGenericIdeal M i < y.asHomogeneousIdeal.toIdeal)
    (hstrict : y.asHomogeneousIdeal.toIdeal < lineClosedIdealAt M i) :"""),

# ---- C. hround/hsurj through the quotient map -------------------------------
("""  -- the block-i retraction roundtrip and surjectivity
  have hround : ∀ g : MvPolynomial (Fin 2) ℂ,
      blockProjQuotAt M i (blockInclAt M i g) = g := by
    intro g
    have hcomp : (blockProjQuotAt M i).comp (blockInclAt M i) =
        AlgHom.id ℂ (MvPolynomial (Fin 2) ℂ) := by
      refine MvPolynomial.algHom_ext fun a => ?_
      show blockProjQuotAt M i (blockInclAt M i (X a)) = X a
      rw [blockInclAt_X]
      show blockProjQuotAt M i (blockInclFamily M i a) = X a
      rcases a with ⟨av, hav⟩
      rcases av with _ | av1
      · show blockProjQuotAt M i
          (lineQuotientMap M (X (⟨2 * i.val + 0, _⟩ : Fin (2 * M)))) = (X (⟨0, _⟩ : Fin 2))
        rw [show ((⟨2 * i.val + 0, _⟩ : Fin (2 * M)) = blockVarLeft M i) from rfl,
          blockProjQuotAt_X_left]
      · rcases av1 with _ | av2
        · show blockProjQuotAt M i
            (lineQuotientMap M (X (⟨2 * i.val + 1, _⟩ : Fin (2 * M)))) = (X (⟨1, _⟩ : Fin 2))
          rw [show ((⟨2 * i.val + 1, _⟩ : Fin (2 * M)) = blockVarRight M i) from rfl,
            blockProjQuotAt_X_right]
        · omega
    have hgg := DFunLike.congr_fun hcomp g
    simpa using hgg
  have hsurj : Function.Surjective (blockProjQuotAt M i) := by
    intro g
    refine ⟨blockInclAt M i g, hround g⟩""",
"""  -- the block-i retraction roundtrip and surjectivity
  have hround : ∀ g : MvPolynomial (Fin 2) ℂ,
      blockProjQuotAt M i (lineQuotientMap M (blockInclAt M i g)) = g := by
    intro g
    rw [blockProjQuotAt_mk]
    simpa using DFunLike.congr_fun (blockProjAt_comp_blockInclAt M i) g
  have hsurj : Function.Surjective (blockProjQuotAt M i) := by
    intro g
    refine ⟨lineQuotientMap M (blockInclAt M i g), hround g⟩"""),

# ---- D. hgoal (w - (w - 1)) + eq_top_iff_one --------------------------------
("""      have hgoal : (1 : lineQuotient M) ∈ y.asHomogeneousIdeal.toIdeal := by
        have hsum : w - 1 + 1 = (1 : lineQuotient M) := by ring
        have hmem1 : w - 1 + 1 ∈ y.asHomogeneousIdeal.toIdeal :=
          Submodule.add_mem _ (hgen hwker) hw
        rw [hsum] at hmem1
        exact hmem1
      exact y.isPrime.ne_top (Ideal.eq_top_of_one_mem hgoal)""",
"""      have hgoal : (1 : lineQuotient M) ∈ y.asHomogeneousIdeal.toIdeal := by
        have hsub : w - (w - 1) ∈ y.asHomogeneousIdeal.toIdeal :=
          Submodule.sub_mem _ hw (hgen.le hwker)
        have hsum : w - (w - 1) = (1 : lineQuotient M) := by ring
        rw [hsum] at hsub
        exact hsub
      exact y.isPrime.ne_top (Ideal.eq_top_iff_one.mpr hgoal)"""),

# ---- B(2). hwmem's hgen.le ---------------------------------------------------
("""      have hwmem : w - (w - ã * b̃) ∈ y.asHomogeneousIdeal.toIdeal :=
        Submodule.sub_mem _ hw (hgen hd)""",
"""      have hwmem : w - (w - ã * b̃) ∈ y.asHomogeneousIdeal.toIdeal :=
        Submodule.sub_mem _ hw (hgen.le hd)"""),

# ---- E(1). hmapclosed first branch: explicit hout ---------------------------
("""      · rw [blockProjQuotAt_mk, blockProjAt_X_outside M i ?_, map_zero]
        · exact Submodule.zero_mem _
        · have hb2 := b.2
          omega""",
"""      · have hout : (b : Fin (2 * M)).val / 2 ≠ i.val := by
          have hb2 := b.2
          omega
        rw [blockProjQuotAt_mk, blockProjAt_X_outside M i hout]
        exact Submodule.zero_mem _"""),

# ---- E(2). hmapclosed second branch: unfold to the goal's span form ---------
("""      rw [blockProjQuotAt_mk, blockProjAt_X_right] at hmem
      exact hmem""",
"""      rw [blockProjQuotAt_mk, blockProjAt_X_right, lineClosedIdealAt,
        Ideal.map_span] at hmem
      exact hmem"""),

# ---- hȳne: drop the unused hgne, use the strict hgen ------------------------
("""  -- ȳ is nonzero: y strictly contains the generic ideal
  have hgne : lineGenericIdeal M i ≠ lineClosedIdealAt M i := by
    intro heq
    have hmem' := lineQuotientMap_X_right_mem_lineClosedIdealAt M i
    rw [← heq] at hmem'
    exact lineQuotientMap_X_pair_not_mem' M i hmem'
  have hȳne : ybar ≠ ⊥ := by
    intro hbot
    obtain ⟨f, hf, hfne⟩ : ∃ f ∈ y.asHomogeneousIdeal.toIdeal,
        f ∉ lineGenericIdeal M i := by
      by_contra hcon
      push_neg at hcon
      have hyg : y.asHomogeneousIdeal.toIdeal = lineGenericIdeal M i :=
        le_antisymm hcon hgen
      refine hstrict.ne ?_
      rw [hyg]
      exact hgne""",
"""  -- ȳ is nonzero: y strictly contains the generic ideal
  have hȳne : ybar ≠ ⊥ := by
    intro hbot
    obtain ⟨f, hf, hfne⟩ : ∃ f ∈ y.asHomogeneousIdeal.toIdeal,
        f ∉ lineGenericIdeal M i := by
      by_contra hcon
      push_neg at hcon
      exact absurd (le_antisymm hcon hgen.le).symm (ne_of_lt hgen)"""),

# ---- B(3). hker's hdiff: hgen.le ---------------------------------------------
("""      have hdiff : w - lineQuotientMap M (X (blockVarRight M i)) ∈
          y.asHomogeneousIdeal.toIdeal := hgen hker""",
"""      have hdiff : w - lineQuotientMap M (X (blockVarRight M i)) ∈
          y.asHomogeneousIdeal.toIdeal := hgen.le hker"""),

# ---- F. hȳneZ ending ----------------------------------------------------------
("""    refine hstrict.ne ?_
    rw [lineClosedIdealAt_eq_supAt M i, sup_le]
    exact ⟨hgen, by
      rw [Ideal.span_le]
      rintro _ rfl
      exact hqmem⟩""",
"""    refine (ne_of_lt hstrict) ?_
    exact le_antisymm hstrict.le (by
      rw [lineClosedIdealAt_eq_supAt M i]
      exact sup_le hgen.le (by
        rw [Ideal.span_le]
        rintro _ rfl
        exact hqmem))"""),

# ---- G. the hkill descent block ----------------------------------------------
("""        by_cases hg0 : g = 0
        · rw [hgf, hg0, mul_zero]
        · rw [hgf, MvPolynomial.totalDegree_mul (X_ne_zero ⟨1, by omega⟩) hg0,
            MvPolynomial.totalDegree_X] at hfD
          omega
    | succ m ih =>""",
"""        by_cases hg0 : g = 0
        · rw [← hgf, hg0, mul_zero]
        · rw [← hgf, MvPolynomial.totalDegree_mul
              (X_ne_zero (s := (⟨1, by omega⟩ : Fin 2))) hg0,
            MvPolynomial.totalDegree_X] at hfD
          omega
    | succ m ih =>"""),
("""        have hmem' : (X ⟨1, by omega⟩ : MvPolynomial (Fin 2) ℂ) * g ∈ ybar := by
          rw [← hgf]; exact hmem""",
"""        have hmem' : (X ⟨1, by omega⟩ : MvPolynomial (Fin 2) ℂ) * g ∈ ybar := by
          rw [hgf]; exact hmem"""),
("""          · rw [hgf, hg0, mul_zero]
          · have hdeg : MvPolynomial.totalDegree g = m := by
              have hdd : MvPolynomial.totalDegree f =
                  MvPolynomial.totalDegree
                    ((X ⟨1, by omega⟩ : MvPolynomial (Fin 2) ℂ) * g) := by
                rw [hgf]
              rw [hdd, MvPolynomial.totalDegree_mul (X_ne_zero ⟨1, by omega⟩) hg0,
                MvPolynomial.totalDegree_X] at hfD
              omega
            rw [hgf, ih g hdeg h2, mul_zero]""",
"""          · rw [← hgf, hg0, mul_zero]
          · have hdeg : MvPolynomial.totalDegree g = m := by
              have hdd : MvPolynomial.totalDegree f =
                  MvPolynomial.totalDegree
                    ((X ⟨1, by omega⟩ : MvPolynomial (Fin 2) ℂ) * g) := by
                rw [hgf]
              rw [hdd, MvPolynomial.totalDegree_mul
                (X_ne_zero (s := (⟨1, by omega⟩ : Fin 2))) hg0,
                MvPolynomial.totalDegree_X] at hfD
              omega
            rw [← hgf, ih g hdeg h2, mul_zero]"""),

# ---- H. lineClosedPointAt_lt: congrArg needs an Eq ---------------------------
("""    apply h2
    have hII : (lineClosedPointAt M i).asHomogeneousIdeal =
        (lineGenericPoint M i).asHomogeneousIdeal :=
      congrArg ProjectiveSpectrum.asHomogeneousIdeal heq""",
"""    apply h2
    have hle : lineClosedPointAt M i ≤ lineGenericPoint M i :=
      (le_iff_ideal M (lineClosedPointAt M i) (lineGenericPoint M i)).mpr
        (by rw [lineClosedPointAt_asIdeal, lineGenericPoint_asIdeal];
            exact lineGenericIdeal_le_lineClosedIdealAt M i)
    have hII : (lineClosedPointAt M i).asHomogeneousIdeal =
        (lineGenericPoint M i).asHomogeneousIdeal :=
      congrArg ProjectiveSpectrum.asHomogeneousIdeal (le_antisymm hle heq)"""),

# ---- I. lineClosedPointAt_coheight: the green ENat ladder --------------------
("""theorem lineClosedPointAt_coheight (M : ℕ) (i : Fin M) :
    Order.coheight (lineClosedPointAt M i) = 1 := by
  apply le_antisymm
  · rw [Order.coheight_le_coe_iff]
    intro w hw
    have hwle : w.asHomogeneousIdeal.toIdeal ≤ lineClosedIdealAt M i :=
      (le_iff_ideal M (lineClosedPointAt M i) w).mp hw.le
    have hwne : w.asHomogeneousIdeal.toIdeal ≠ lineClosedIdealAt M i := by
      intro heq
      have hwceq : w = lineClosedPointAt M i := by
        refine projectiveSpectrum_ext ?_
        refine HomogeneousIdeal.ext ?_
        rw [lineClosedPointAt_asIdeal]
        exact heq
      exact hw.ne hwceq.symm
    have hgen : lineGenericIdeal M i ≤ w.asHomogeneousIdeal.toIdeal := by
      rw [lineGenericIdeal, Ideal.span_le]
      rintro _ ⟨b, rfl⟩
      have hzero : lineQuotientMap M (X (blockVarLeft M i)) *
          lineQuotientMap M (X (b : Fin (2 * M))) = 0 :=
        crossMul_eq_zero M (fun hcon => b.2 (hcon.symm.trans
          (blockVarLeft_block M i)))
      have hX0 : lineQuotientMap M (X (blockVarLeft M i)) ∉
          w.asHomogeneousIdeal.toIdeal := fun hmem =>
        lineQuotientMap_X_left_not_mem_lineClosedIdealAt M i (hwle hmem)
      have hmem : lineQuotientMap M (X (blockVarLeft M i)) *
          lineQuotientMap M (X (b : Fin (2 * M))) ∈ w.asHomogeneousIdeal.toIdeal := by
        rw [hzero]; exact Submodule.zero_mem _
      rcases w.isPrime.mem_or_mem hmem with h1 | h2
      · exact absurd h1 hX0
      · exact h2
    rcases eq_or_ne w.asHomogeneousIdeal.toIdeal (lineGenericIdeal M i) with heq | hne
    · have hwgen : w = lineGenericPoint M i :=
        eq_lineGenericPoint_of_le M i w (by rw [heq]; exact le_rfl)
      rw [hwgen]
      exact lineGenericPoint_coheight M i
    · exact absurd (no_intermediate_pointAt M i w hgen ⟨hwle, hwne⟩) False.elim
  · have h := Order.coheight_add_one_le (lineClosedPointAt_lt M)
    rw [lineGenericPoint_coheight M i] at h
    have h1 : (0 : ℕ∞) + 1 = 1 := by norm_num
    rw [h1] at h
    exact h""",
"""theorem lineClosedPointAt_coheight (M : ℕ) (i : Fin M) :
    Order.coheight (lineClosedPointAt M i) = 1 := by
  have hlower : (1 : ℕ∞) ≤ Order.coheight (lineClosedPointAt M i) := by
    have h := Order.coheight_add_one_le (lineClosedPointAt_lt M i)
    rw [lineGenericPoint_coheight M i] at h
    simpa using h
  have hupper : Order.coheight (lineClosedPointAt M i) ≤ ((1 : ℕ) : ℕ∞) := by
    rw [Order.coheight_le_coe_iff]
    intro w hw
    have hwle : w.asHomogeneousIdeal.toIdeal ≤ lineClosedIdealAt M i :=
      (le_iff_ideal M (lineClosedPointAt M i) w).mp hw.le
    have hwne : w.asHomogeneousIdeal.toIdeal ≠ lineClosedIdealAt M i := by
      intro heq
      have hwceq : w = lineClosedPointAt M i := by
        refine projectiveSpectrum_ext ?_
        refine HomogeneousIdeal.ext ?_
        rw [lineClosedPointAt_asIdeal]
        exact heq
      exact (ne_of_lt hw) hwceq.symm
    have hgen : lineGenericIdeal M i ≤ w.asHomogeneousIdeal.toIdeal := by
      rw [lineGenericIdeal, Ideal.span_le]
      rintro _ ⟨b, rfl⟩
      have hzero : lineQuotientMap M (X (blockVarLeft M i)) *
          lineQuotientMap M (X (b : Fin (2 * M))) = 0 :=
        crossMul_eq_zero M (fun hcon => b.2 (hcon.symm.trans
          (blockVarLeft_block M i)))
      have hX0 : lineQuotientMap M (X (blockVarLeft M i)) ∉
          w.asHomogeneousIdeal.toIdeal := fun hmem =>
        lineQuotientMap_X_left_not_mem_lineClosedIdealAt M i (hwle hmem)
      have hmem : lineQuotientMap M (X (blockVarLeft M i)) *
          lineQuotientMap M (X (b : Fin (2 * M))) ∈ w.asHomogeneousIdeal.toIdeal := by
        rw [hzero]; exact Submodule.zero_mem _
      rcases w.isPrime.mem_or_mem hmem with h1 | h2
      · exact absurd h1 hX0
      · exact h2
    rcases eq_or_ne w.asHomogeneousIdeal.toIdeal (lineGenericIdeal M i) with heq | hne
    · have hwgen : w = lineGenericPoint M i :=
        eq_lineGenericPoint_of_le M i w (by rw [heq]; exact le_rfl)
      rw [hwgen, lineGenericPoint_coheight M i]
      exact_mod_cast (by norm_num : (0 : ℕ) < (1 : ℕ))
    · exact absurd (no_intermediate_pointAt M i w ⟨hgen, hne.symm⟩ ⟨hwle, hwne⟩)
        False.elim
  have hne : Order.coheight (lineClosedPointAt M i) ≠ ⊤ := by
    intro htop
    rw [htop] at hupper
    exact absurd hupper (by simp)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hne
  rw [← hn] at hupper hlower ⊢
  have hn1 : n ≤ 1 := ENat.coe_le_coe.mp hupper
  have hn2 : 1 ≤ n := ENat.coe_le_coe.mp hlower
  rw [← ENat.coe_one]
  exact congrArg ((↑) : ℕ → ℕ∞) (le_antisymm (α := ℕ) hn1 hn2)"""),

# ---- J. eq_lineGenericPoint_of_le branch 2's phantom b ----------------------
("""      have hzero : lineQuotientMap M (X a) *
          lineQuotientMap M (X (b : Fin (2 * M))) = 0 :=
        crossMul_eq_zero M (fun hcon => hblock (hcon.trans (blockVarLeft_block M i)))""",
"""      have hzero : lineQuotientMap M (X a) *
          lineQuotientMap M (X (blockVarLeft M i)) = 0 :=
        crossMul_eq_zero M (fun hcon => hblock (hcon.trans (blockVarLeft_block M i)))"""),

# ---- K. hsplit ----------------------------------------------------------------
("""  have hsplit : e = Finsupp.single a 1 + (e - Finsupp.single a 1) := by
    ext j
    simp only [Finsupp.add_apply, Finsupp.sub_apply, Finsupp.single_apply]
    by_cases hja : j = a
    · rw [hja]
      simp only [if_pos rfl]
      omega
    · rw [if_neg hja, if_neg hja]
      omega""",
"""  have hsplit : e = Finsupp.single a 1 + (e - Finsupp.single a 1) := by
    ext j
    simp only [Finsupp.add_apply, Finsupp.coe_sub, Pi.sub_apply,
      Finsupp.single_apply]
    by_cases hja : j = a
    · subst hja
      simp only [if_pos rfl]
      omega
    · simp only [if_neg hja]
      omega"""),

# ---- L(1). lineGenericPoint_injective's rw direction -------------------------
("""  have h1 := congrArg HomogeneousIdeal.toIdeal hII
  rw [lineGenericPoint_asIdeal, lineGenericPoint_asIdeal] at h1
  rw [← h1]
  exact hmem""",
"""  have h1 := congrArg HomogeneousIdeal.toIdeal hII
  rw [lineGenericPoint_asIdeal, lineGenericPoint_asIdeal] at h1
  rw [h1]
  exact hmem"""),

# ---- L(2). exists_eq_lineGenericPoint's IsMax elimination --------------------
("""  have hle : η ≤ lineGenericPoint M ⟨a.val / 2, by have := a.isLt; omega⟩ :=
    (le_iff_ideal M η (lineGenericPoint M ⟨a.val / 2, by have := a.isLt; omega⟩)).mpr hgen
  exact le_antisymm (hmax hle) hle""",
"""  have hle : η ≤ lineGenericPoint M ⟨a.val / 2, by have := a.isLt; omega⟩ :=
    (le_iff_ideal M η (lineGenericPoint M ⟨a.val / 2, by have := a.isLt; omega⟩)).mpr hgen
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact (hmax hlt).elim
  · exact heq"""),

# ---- M(1). exists_unique_generic_above: hkx/hkx' rw direction ----------------
("""  have hkx : lineGenericIdeal M k ≤ x.1.asHomogeneousIdeal.toIdeal := by
    rw [hk] at hxη
    rw [lineGenericPoint_asIdeal]
    exact (le_iff_ideal M x.1 (lineGenericPoint M k)).mp (le_of_lt hxη)
  have hkx' : lineGenericIdeal M k' ≤ x.1.asHomogeneousIdeal.toIdeal := by
    rw [hk'] at hxη'
    rw [lineGenericPoint_asIdeal]
    exact (le_iff_ideal M x.1 (lineGenericPoint M k')).mp (le_of_lt hxη')""",
"""  have hkx : lineGenericIdeal M k ≤ x.1.asHomogeneousIdeal.toIdeal := by
    rw [hk] at hxη
    rw [← lineGenericPoint_asIdeal]
    exact (le_iff_ideal M x.1 (lineGenericPoint M k)).mp (le_of_lt hxη)
  have hkx' : lineGenericIdeal M k' ≤ x.1.asHomogeneousIdeal.toIdeal := by
    rw [hk'] at hxη'
    rw [← lineGenericPoint_asIdeal]
    exact (le_iff_ideal M x.1 (lineGenericPoint M k')).mp (le_of_lt hxη')"""),

# ---- M(2). the Fin.ext wrapper -------------------------------------------------
("""      · exact hkx' (mem_lineGenericIdeal M k'
          (fun hcon => hne (hcon.symm.trans hblock).symm))""",
"""      · exact hkx' (mem_lineGenericIdeal M k'
          (fun hcon => hne (Fin.ext (hcon.symm.trans hblock).symm)))"""),

# ---- M(3). lineClosedPointAt_component's direction -----------------------------
("""    lineComponentOf M ⟨lineClosedPointAt M i, lineClosedPointAt_coheight M i⟩ =
      ⟨lineGenericPoint M i, lineGenericPoint_coheight M i⟩ :=
  lineComponentOf_unique M _ _ (lineClosedPointAt_lt M)""",
"""    lineComponentOf M ⟨lineClosedPointAt M i, lineClosedPointAt_coheight M i⟩ =
      ⟨lineGenericPoint M i, lineGenericPoint_coheight M i⟩ :=
  (lineComponentOf_unique M _ _ (lineClosedPointAt_lt M)).symm"""),

# ---- N. codimensionPointCycle_ne_zero's green simp set -------------------------
("""  have h2 : ((codimensionPointCycle X p x : AlgebraicCycle X ℚ) : X → ℚ) x.1 = 1 := by
    show Function.locallyFinsuppWithin.single x.1 (1 : ℚ) x.1 = 1
    simp""",
"""  have h2 : ((codimensionPointCycle X p x : AlgebraicCycle X ℚ) : X → ℚ) x.1 = 1 := by
    simp [codimensionPointCycle, Function.locallyFinsuppWithin.single_apply]"""),
]

# ---- the surviving fix_round2 receipts (verified correct) --------------------
FIX_ROUND2 = [
# blockVarFamily: full simp closes the if-True reduction
("""    blockVarFamily M i (blockVarLeft M i) = (X ⟨0, by omega⟩ : MvPolynomial (Fin 2) ℂ) := by
  simp only [blockVarFamily, blockVarLeft_val]""",
"""    blockVarFamily M i (blockVarLeft M i) = (X ⟨0, by omega⟩ : MvPolynomial (Fin 2) ℂ) := by
  simp [blockVarFamily, blockVarLeft_val]"""),
("""    blockVarFamily M i (blockVarRight M i) = (X ⟨1, by omega⟩ : MvPolynomial (Fin 2) ℂ) := by
  simp only [blockVarFamily, blockVarRight_val]""",
"""    blockVarFamily M i (blockVarRight M i) = (X ⟨1, by omega⟩ : MvPolynomial (Fin 2) ℂ) := by
  simp [blockVarFamily, blockVarRight_val]"""),
# blockInclAt_X_zero/one: the congr-1 closes by defeq
("""  show (X (⟨2 * i.val + 0, by have := i.isLt; omega⟩ : Fin (2 * M)) : lineRing M) =
    (X (blockVarLeft M i) : lineRing M)
  congr 1
  apply Fin.ext
  show (2 * i.val + 0 : ℕ) = (blockVarLeft M i).val
  rw [blockVarLeft_val]
  omega""",
"""  show (X (⟨2 * i.val + 0, by have := i.isLt; omega⟩ : Fin (2 * M)) : lineRing M) =
    (X (blockVarLeft M i) : lineRing M)
  rfl"""),
("""  show (X (⟨2 * i.val + 1, by have := i.isLt; omega⟩ : Fin (2 * M)) : lineRing M) =
    (X (blockVarRight M i) : lineRing M)
  congr 1
  apply Fin.ext
  show (2 * i.val + 1 : ℕ) = (blockVarRight M i).val
  rw [blockVarRight_val]
  omega""",
"""  show (X (⟨2 * i.val + 1, by have := i.isLt; omega⟩ : Fin (2 * M)) : lineRing M) =
    (X (blockVarRight M i) : lineRing M)
  rfl"""),
# crossIdeal-le-ker sites: simp-only mem_ker (coercion-friendly)
("""  rintro _ ⟨a, b, hab, rfl⟩
  rw [RingHom.mem_ker]
  show blockProjAt M i (X a * X b) = 0""",
"""  rintro _ ⟨a, b, hab, rfl⟩
  simp only [RingHom.mem_ker]
  show blockProjAt M i (X a * X b) = 0"""),
("""  rintro _ ⟨a, b, hab, rfl⟩
  rw [RingHom.mem_ker]
  show blockProjClosedAt M i (X a * X b) = 0""",
"""  rintro _ ⟨a, b, hab, rfl⟩
  simp only [RingHom.mem_ker]
  show blockProjClosedAt M i (X a * X b) = 0"""),
# X_ne_zero anonymous-constructor sites: ascribe the Fin-literal
("""  rw [blockProjQuotAt_X_left M i] at hz
  exact X_ne_zero ⟨0, by omega⟩ hz""",
"""  rw [blockProjQuotAt_X_left M i] at hz
  exact X_ne_zero (s := (⟨0, by omega⟩ : Fin 2)) hz"""),
("""  rw [blockProjQuotAt_X_right M i] at hz
  exact X_ne_zero ⟨1, by omega⟩ hz""",
"""  rw [blockProjQuotAt_X_right M i] at hz
  exact X_ne_zero (s := (⟨1, by omega⟩ : Fin 2)) hz"""),
("""  rw [blockProjClosedQuotAt_mk, blockProjClosedAt_X_left] at hz
  exact X_ne_zero ⟨0, by omega⟩ hz""",
"""  rw [blockProjClosedQuotAt_mk, blockProjClosedAt_X_left] at hz
  exact X_ne_zero (s := (⟨0, by omega⟩ : Fin 1)) hz"""),
# le_iff_ideal's key: the ProjectiveSpectrum-typed statement
("""  have key : ∀ a b : finiteLineScheme M,
      a ∈ closure ({b} : Set (finiteLineScheme M)) ↔
        b.asHomogeneousIdeal.toIdeal ≤ a.asHomogeneousIdeal.toIdeal := by""",
"""  have key : ∀ a b : ProjectiveSpectrum (lineGrading M),
      a ∈ closure ({b} : Set (ProjectiveSpectrum (lineGrading M))) ↔
        b.asHomogeneousIdeal.toIdeal ≤ a.asHomogeneousIdeal.toIdeal := by"""),
# homogeneous_pos: the forall-injection for hcon
("""    have hcon' : ∀ j : Fin (2 * M), ¬(0 < e j) := fun j => hcon j""",
"""    have hcon' : ∀ j : Fin (2 * M), ¬(0 < e j) := fun j h' => hcon ⟨j, h'⟩"""),
# irrelevant_le's image destructure
("""    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨a, rfl⟩
    exact h a""",
"""    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨a, ⟨b, rfl⟩, rfl⟩
    show (lineQuotientMap M) (X b) ∈ I
    exact h b"""),
# exists_variable_not_mem: add not_not
("""  by_contra hcon
  simp only [not_exists] at hcon""",
"""  by_contra hcon
  simp only [not_exists, not_not] at hcon"""),
# coheight's le_iff argument order (IsMax gives LGP <= z)
("""  have hzle : z.asHomogeneousIdeal.toIdeal ≤ lineGenericIdeal M i :=
    (le_iff_ideal M z (lineGenericPoint M i)).mp hle""",
"""  have hzle : z.asHomogeneousIdeal.toIdeal ≤ lineGenericIdeal M i :=
    (le_iff_ideal M (lineGenericPoint M i) z).mp hle"""),
# sup_le -> sup_le_iff (the Iff form)
("""  · refine sup_le.mpr ⟨lineGenericIdeal_le_lineClosedIdealAt M i, ?_⟩""",
"""  · refine sup_le_iff.mpr ⟨lineGenericIdeal_le_lineClosedIdealAt M i, ?_⟩"""),
]

total = 0
failed = []
for old, new in REPLACEMENTS + FIX_ROUND2:
    if old == new:
        continue
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

# the combining-tilde kill (b + U+0303 breaks the parser; no precomposed form)
if 'b\u0303' in data:
    nb = data.count('b\u0303')
    data = data.replace('b\u0303', 'bbar')
    total += 1
    print(f"combining-tilde: replaced {nb} occurrences (b~, hb~ -> bbar, hbbar)")

open(path, 'w', encoding='utf-8').write(data)
print("changed:", data != n0, "| replacements applied:", total)
if failed:
    print("PATTERNS NOT FOUND:")
    for f in failed:
        print("  -", f)

# ---- self-check probes -------------------------------------------------------
probes = [
  ("opens present", "open GSTNativeCodimensionCyclePresentation GSTGeometricRealizationStage2D", True),
  ("hgen strict", "(hgen : lineGenericIdeal M i < y.asHomogeneousIdeal.toIdeal)", True),
  ("hround quotient route", "blockProjQuotAt M i (lineQuotientMap M (blockInclAt M i g)) = g", True),
  ("hgoal sub", "w - (w - 1) ∈ y.asHomogeneousIdeal.toIdeal", True),
  ("eq_top_iff_one", "Ideal.eq_top_iff_one.mpr hgoal", True),
  ("hout explicit", "have hout : (b : Fin (2 * M)).val / 2 ≠ i.val", True),
  ("hȳneZ ending", "exact le_antisymm hstrict.le (by", True),
  ("hkill ← hgf", "rw [← hgf, hg0, mul_zero]", True),
  ("hkill ascription", "X_ne_zero (s := (⟨1, by omega⟩ : Fin 2))", True),
  ("lt branch built", "le_antisymm hle heq", True),
  ("coheight ladder", "ENat.ne_top_iff_exists.mp hne", True),
  ("coheight cast", "≤ ((1 : ℕ) : ℕ∞)", True),
  ("coheight_add_one_le i-arg", "Order.coheight_add_one_le (lineClosedPointAt_lt M i)", True),
  ("no_intermediate strict call", "no_intermediate_pointAt M i w ⟨hgen, hne.symm⟩ ⟨hwle, hwne⟩", True),
  ("phantom b killed", "lineQuotientMap M (X (blockVarLeft M i)) = 0 :=\n        crossMul_eq_zero M (fun hcon => hblock (hcon.trans (blockVarLeft_block M i)))", True),
  ("hsplit simp set", "Finsupp.add_apply, Finsupp.coe_sub, Pi.sub_apply", True),
  ("if_neg direct", "simp only [if_neg hja]", True),
  ("rw h1 direction", "rw [h1]\n  exact hmem", True),
  ("IsMax elim", "rcases lt_or_eq_of_le hle with hlt | heq", True),
  ("Fin.ext wrapper", "hne (Fin.ext (hcon.symm.trans hblock).symm)", True),
  ("component symm", "(lineComponentOf_unique M _ _ (lineClosedPointAt_lt M)).symm", True),
  ("cycle simp set", "simp [codimensionPointCycle, Function.locallyFinsuppWithin.single_apply]", True),
  ("blockVarFamily simp", "simp [blockVarFamily, blockVarLeft_val]", True),
  ("blockInclAt rfl", "(X (blockVarRight M i) : lineRing M)\n  rfl", True),
  ("mem_ker simp only", "simp only [RingHom.mem_ker]", True),
  ("X_ne_zero Fin 2 ascription", "X_ne_zero (s := (⟨0, by omega⟩ : Fin 2)) hz", True),
  ("X_ne_zero Fin 1 ascription", "X_ne_zero (s := (⟨0, by omega⟩ : Fin 1)) hz", True),
  ("key ProjectiveSpectrum", "have key : ∀ a b : ProjectiveSpectrum (lineGrading M),", True),
  ("hcon injection", "fun j h' => hcon ⟨j, h'⟩", True),
  ("image destructure", "rintro _ ⟨a, ⟨b, rfl⟩, rfl⟩", True),
  ("not_not added", "not_exists, not_not", True),
  ("coheight order fixed", "(le_iff_ideal M (lineGenericPoint M i) z).mp hle", True),
  ("sup_le_iff", "refine sup_le_iff.mpr", True),
  ("bbar present", "bbar", True),
  ("no combining tilde", "\u0303", False),
  ("old eq_top gone", "eq_top_of_one_mem", False),
  ("old hround gone", "blockProjQuotAt M i (blockInclAt M i g)", False),
  ("old sup_le.mpr gone", "sup_le.mpr", False),
  ("old congr-1 gone", "apply Fin.ext\n  show (2 * i.val + 0", False),
  ("old hmax misuse gone", "le_antisymm (hmax hle) hle", False),
  ("old rw gone", "rw [hgf, hg0, mul_zero]", False),
  ("old mem_ker rw gone at crossIdeal", "rw [RingHom.mem_ker]\n  show blockProjAt M i (X a * X b) = 0", False),
]
ok = True
for desc, probe, want in probes:
    got = probe in data
    status = "OK " if got == want else "BAD"
    if got != want: ok = False
    print(f"{status} {desc}: found={got} expected={want}")
print("ALL OK" if ok and not failed else "ISSUES REMAIN" if not ok else "OK (some patterns not found)")
