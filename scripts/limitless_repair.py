from pathlib import Path


def replace(path: str, old: str, new: str) -> None:
    p = Path(path)
    s = p.read_text()
    if old not in s:
        raise SystemExit(f"target block not found: {path}")
    p.write_text(s.replace(old, new, 1))


replace(
    "GSTGradedWorldAlgebra.lean",
    '''theorem cosmicSector_idempotent (k : ℕ) (f : CompletedCosmos) :
    cosmicSector k (cosmicSector k f) = cosmicSector k f := by
  funext c
  simp only [cosmicSector]
  by_cases hk : cosmicDegree c = k
  · rw [if_pos hk, if_pos hk]
  · rw [if_neg hk]

theorem cosmicSector_orthogonal (k j : ℕ) (h : k ≠ j) (f : CompletedCosmos) :
    cosmicSector k (cosmicSector j f) = 0 := by
  funext c
  simp only [cosmicSector]
  by_cases hk : cosmicDegree c = k
  · have hj : cosmicDegree c ≠ j := by
      intro hcj
      apply h
      exact hk.symm.trans hcj
    rw [if_pos hk, if_neg hj]
  · rw [if_neg hk]
''',
    '''theorem cosmicSector_idempotent (k : ℕ) (f : CompletedCosmos) :
    cosmicSector k (cosmicSector k f) = cosmicSector k f := by
  funext c
  change (if cosmicDegree c = k then
      (if cosmicDegree c = k then f c else 0) else 0) =
    (if cosmicDegree c = k then f c else 0)
  by_cases hk : cosmicDegree c = k
  · simp only [if_pos hk]
  · simp only [if_neg hk]

theorem cosmicSector_orthogonal (k j : ℕ) (h : k ≠ j) (f : CompletedCosmos) :
    cosmicSector k (cosmicSector j f) = 0 := by
  funext c
  change (if cosmicDegree c = k then
      (if cosmicDegree c = j then f c else 0) else 0) = 0
  by_cases hk : cosmicDegree c = k
  · have hj : cosmicDegree c ≠ j := by
      intro hcj
      apply h
      exact hk.symm.trans hcj
    simp only [if_pos hk, if_neg hj]
  · simp only [if_neg hk]
''',
)

replace(
    "GSTGraphV2CanonicalPhaseSteering.lean",
    '''theorem rightSeedPhaseTransfer_injective_on_trits
    {a b : Nat} (ha : a < 3) (hb : b < 3)
    (h : rightSeedPhaseTransfer a = rightSeedPhaseTransfer b) :
    a = b := by
  have ha_cases : a = 0 ∨ a = 1 ∨ a = 2 := by omega
  have hb_cases : b = 0 ∨ b = 1 ∨ b = 2 := by omega
  rcases ha_cases with rfl | rfl | rfl <;>
    rcases hb_cases with rfl | rfl | rfl <;>
    norm_num [rightSeedPhaseTransfer] at h ⊢
''',
    '''theorem rightSeedPhaseTransfer_injective_on_trits
    {a b : Nat} (ha : a < 3) (hb : b < 3)
    (h : rightSeedPhaseTransfer a = rightSeedPhaseTransfer b) :
    a = b := by
  have ha_cases : a = 0 ∨ a = 1 ∨ a = 2 := by omega
  have hb_cases : b = 0 ∨ b = 1 ∨ b = 2 := by omega
  rcases ha_cases with rfl | rfl | rfl <;>
    rcases hb_cases with rfl | rfl | rfl
  all_goals norm_num [rightSeedPhaseTransfer] at h
  all_goals rfl
''',
)

replace(
    "GSTCoherentCosmology.lean",
    '''def cosmicD0Linear : CompletedCosmos →ₗ[ℤ] (CompletedCosmos × CompletedCosmos) where
  toFun := cosmicD0
  map_add' := by
    intro f g; apply Prod.ext <;> funext c <;>
      simp [cosmicD0, cosmicDeltaCarry, cosmicDeltaDigit] <;> ring
  map_smul' := by
    intro z f; apply Prod.ext <;> funext c <;>
      simp [cosmicD0, cosmicDeltaCarry, cosmicDeltaDigit, mul_sub]
''',
    '''def cosmicD0Linear : CompletedCosmos →ₗ[ℤ] (CompletedCosmos × CompletedCosmos) where
  toFun := cosmicD0
  map_add' := by
    intro f g
    apply Prod.ext <;> funext c <;>
      simp [cosmicD0, cosmicDeltaCarry, cosmicDeltaDigit]
  map_smul' := by
    intro z f; apply Prod.ext <;> funext c <;>
      simp [cosmicD0, cosmicDeltaCarry, cosmicDeltaDigit, mul_sub]
''',
)

replace(
    "GSTCoherentCosmology.lean",
    '''def windowD0 (A B : ℕ) : WorldCoef (A+2) (B+2) →ₗ[ℤ]
    (WorldCoef (A+1) (B+1) × WorldCoef (A+1) (B+1)) where
  toFun := fun f => (windowDeltaCarry (A+1) (B+1) f, windowDeltaDigit (A+1) (B+1) f)
  map_add' := by
    intro f g
    apply Prod.ext <;> funext c <;>
      simp [windowDeltaCarry, windowDeltaDigit, Pi.add_apply] <;> ring
  map_smul' := by
    intro z f
    apply Prod.ext <;> funext c <;>
      simp [windowDeltaCarry, windowDeltaDigit, Pi.smul_apply, smul_eq_mul, mul_sub]

def windowD1 (A B : ℕ) :
    (WorldCoef (A+1) (B+1) × WorldCoef (A+1) (B+1)) →ₗ[ℤ] WorldCoef A B where
  toFun := fun w => windowDeltaCarry A B w.2 - windowDeltaDigit A B w.1
  map_add' := by
    intro f g
    funext c
    simp [windowDeltaCarry, windowDeltaDigit, Pi.add_apply]
    ring
  map_smul' := by
    intro z f
    funext c
    simp [windowDeltaCarry, windowDeltaDigit, Pi.smul_apply, smul_eq_mul, mul_sub]
    ring

theorem windowD1_D0 (A B : ℕ) (f : WorldCoef (A+2) (B+2)) :
    windowD1 A B (windowD0 A B f)=0 := by
  funext c
  simp only [windowD1, windowD0, windowDeltaCarry, windowDeltaDigit]
  ring
''',
    '''theorem windowDeltaCarry_add_exact (A B : ℕ)
    (f g : WorldCoef (A+1) (B+1)) :
    windowDeltaCarry A B (f + g) =
      windowDeltaCarry A B f + windowDeltaCarry A B g := by
  funext c
  change (f _ + g _) - (f _ + g _) = (f _ - f _) + (g _ - g _)
  ring

theorem windowDeltaDigit_add_exact (A B : ℕ)
    (f g : WorldCoef (A+1) (B+1)) :
    windowDeltaDigit A B (f + g) =
      windowDeltaDigit A B f + windowDeltaDigit A B g := by
  funext c
  change (f _ + g _) - (f _ + g _) = (f _ - f _) + (g _ - g _)
  ring

theorem windowDeltaCarry_smul_exact (A B : ℕ) (z : ℤ)
    (f : WorldCoef (A+1) (B+1)) :
    windowDeltaCarry A B (z • f) = z • windowDeltaCarry A B f := by
  funext c
  change z * f _ - z * f _ = z * (f _ - f _)
  ring

theorem windowDeltaDigit_smul_exact (A B : ℕ) (z : ℤ)
    (f : WorldCoef (A+1) (B+1)) :
    windowDeltaDigit A B (z • f) = z • windowDeltaDigit A B f := by
  funext c
  change z * f _ - z * f _ = z * (f _ - f _)
  ring

theorem window_differentials_commute_exact (A B : ℕ)
    (f : WorldCoef (A+2) (B+2)) :
    windowDeltaCarry A B (windowDeltaDigit (A+1) (B+1) f) =
      windowDeltaDigit A B (windowDeltaCarry (A+1) (B+1) f) := by
  funext c
  change (f _ - f _) - (f _ - f _) = (f _ - f _) - (f _ - f _)
  ring

def windowD0 (A B : ℕ) : WorldCoef (A+2) (B+2) →ₗ[ℤ]
    (WorldCoef (A+1) (B+1) × WorldCoef (A+1) (B+1)) where
  toFun := fun f => (windowDeltaCarry (A+1) (B+1) f, windowDeltaDigit (A+1) (B+1) f)
  map_add' := by
    intro f g
    apply Prod.ext
    · exact windowDeltaCarry_add_exact (A+1) (B+1) f g
    · exact windowDeltaDigit_add_exact (A+1) (B+1) f g
  map_smul' := by
    intro z f
    apply Prod.ext
    · exact windowDeltaCarry_smul_exact (A+1) (B+1) z f
    · exact windowDeltaDigit_smul_exact (A+1) (B+1) z f

def windowD1 (A B : ℕ) :
    (WorldCoef (A+1) (B+1) × WorldCoef (A+1) (B+1)) →ₗ[ℤ] WorldCoef A B where
  toFun := fun w => windowDeltaCarry A B w.2 - windowDeltaDigit A B w.1
  map_add' := by
    intro f g
    change windowDeltaCarry A B (f.2 + g.2) - windowDeltaDigit A B (f.1 + g.1) =
      (windowDeltaCarry A B f.2 - windowDeltaDigit A B f.1) +
        (windowDeltaCarry A B g.2 - windowDeltaDigit A B g.1)
    rw [windowDeltaCarry_add_exact, windowDeltaDigit_add_exact]
    abel
  map_smul' := by
    intro z f
    change windowDeltaCarry A B (z • f.2) - windowDeltaDigit A B (z • f.1) =
      z • (windowDeltaCarry A B f.2 - windowDeltaDigit A B f.1)
    rw [windowDeltaCarry_smul_exact, windowDeltaDigit_smul_exact]
    exact (smul_sub z _ _).symm

theorem windowD1_D0 (A B : ℕ) (f : WorldCoef (A+2) (B+2)) :
    windowD1 A B (windowD0 A B f)=0 := by
  change windowDeltaCarry A B (windowDeltaDigit (A+1) (B+1) f) -
    windowDeltaDigit A B (windowDeltaCarry (A+1) (B+1) f) = 0
  rw [window_differentials_commute_exact, sub_self]
''',
)
