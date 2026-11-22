data = open('/home/z/hc-repo/GSTFiniteLinePointAlgebra.lean').read()
checks = [
  # (description, expected-substring, should-exist)
  ("hwker chain (fixed order)", "rw [mem_lineGenericIdeal_iff M i]\n        rw [map_sub, hw1, map_one, sub_self]", True),
  ("hwker old broken", "rw [mem_lineGenericIdeal_iff M i, blockProjQuotAt_mk]\n        rw [map_sub, map_one, hw1, sub_self]", False),
  ("hd chain fixed", "rw [mem_lineGenericIdeal_iff M i]\n        rw [map_sub, map_mul", True),
  ("hker order fixed", "rw [map_sub, blockProjQuotAt_mk, blockProjAt_X_right M i, hwZ, sub_self]", True),
  ("hZle Submodule form", "Submodule.span_singleton_le_iff.mpr hZ", True),
  ("hZle Ideal form (wrong)", "Ideal.span_singleton_le_iff.mpr hZ", False),
  ("ENat ladder", "exact ENat.coe_lt_top 1", True),
  ("uniqueness lambda fixed", "hne (hcon.symm.trans hblock).symm", True),
  ("uniqueness lambda old", "hne (hblock.trans hcon.symm)", False),
  ("eq_lineGenPt branch2 fixed", "hblock (hcon.trans (blockVarLeft_block M i))", True),
  ("exists_eq fixed", "b.2 hcon.symm", True),
  ("hyle calc form", "Ideal.map_mono hstrict.le\n      _ = Ideal.span", True),
  ("coheight branch fixed", "b.2 (hcon.symm.trans\n          (blockVarLeft_block M i))", True),
  ("blockVarFamily_left simp", "simp only [blockVarFamily, blockVarLeft_val]", True),
  ("import added", "import GSTNativeCodimensionCyclePresentation", True),
  ("projectiveSpectrum_ext graded", "{\U0001d49c : ℕ → σ} [GradedRing \U0001d49c]", True),
  ("descent kill present", "hkill : ∀ n : ℕ", True),
  ("le_iff_ideal inline", "specializes_iff_mem_closure", True),
  ("lineClosedPointAt present", "lineClosedPointAt_coheight", True),
  ("seeds present", "lineHonestSeedOne_ne", True),
]
ok = True
for desc, sub, should in checks:
    got = sub in data
    status = "OK " if got == should else "BAD"
    if got != should: ok = False
    print(f"{status} {desc}: found={got} expected={should}")
print("ALL OK" if ok else "FIXES NEEDED")
