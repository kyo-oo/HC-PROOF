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
  funext c; simp [cosmicSector]

theorem cosmicSector_orthogonal (k j : ℕ) (h : k ≠ j) (f : CompletedCosmos) :
    cosmicSector k (cosmicSector j f) = 0 := by
  funext c
  by_cases hk : cosmicDegree c=k
  · have hj : cosmicDegree c ≠ j := by omega
    simp [cosmicSector, hk, hj]
  · simp [cosmicSector, hk]
''',
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
)

replace(
    "GSTGraphV2CanonicalPhaseSteering.lean",
    '''theorem rightSeedPhaseTransfer_injective_on_trits
    {a b : Nat} (ha : a < 3) (hb : b < 3)
    (h : rightSeedPhaseTransfer a = rightSeedPhaseTransfer b) :
    a = b := by
  interval_cases a <;> interval_cases b
  all_goals norm_num [rightSeedPhaseTransfer] at h ⊢
''',
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
)

replace(
    "GSTCoherentCosmology.lean",
    '''def windowD0 (A B : ℕ) : WorldCoef (A+2) (B+2) →ₗ[ℤ]
    (WorldCoef (A+1) (B+1) × WorldCoef (A+1) (B+1)) where
  toFun := fun f => (windowDeltaCarry (A+1) (B+1) f, windowDeltaDigit (A+1) (B+1) f)
  map_add' := by
    intro f g; apply Prod.ext <;> funext c <;>
      simp [windowDeltaCarry, windowDeltaDigit] <;> ring
  map_smul' := by
    intro z f; apply Prod.ext <;> funext c <;>
      simp [windowDeltaCarry, windowDeltaDigit, mul_sub]

def windowD1 (A B : ℕ) :
    (WorldCoef (A+1) (B+1) × WorldCoef (A+1) (B+1)) →ₗ[ℤ] WorldCoef A B where
  toFun := fun w => windowDeltaCarry A B w.2 - windowDeltaDigit A B w.1
  map_add' := by
    intro f g; funext c
    simp [windowDeltaCarry, windowDeltaDigit]; ring
  map_smul' := by
    intro z f; funext c
    simp [windowDeltaCarry, windowDeltaDigit, mul_sub]; ring

theorem windowD1_D0 (A B : ℕ) (f : WorldCoef (A+2) (B+2)) :
    windowD1 A B (windowD0 A B f)=0 := by
  funext c
  simp [windowD1, windowD0, windowDeltaCarry, windowDeltaDigit]
  ring
''',
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
)
