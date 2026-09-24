from pathlib import Path


def replace(path: str, old: str, new: str) -> None:
    p = Path(path)
    s = p.read_text()
    if old not in s:
        raise SystemExit(f"target block not found: {path}")
    p.write_text(s.replace(old, new, 1))


replace(
    "GSTCoherentCosmology.lean",
    '''def cosmicD0Linear : CompletedCosmos →ₗ[ℤ] (CompletedCosmos × CompletedCosmos) where
  toFun := cosmicD0
  map_add' := by
    intro f g
    apply Prod.ext <;> funext c <;>
      simp [cosmicD0, cosmicDeltaCarry, cosmicDeltaDigit]
  map_smul' := by
    intro z f; apply Prod.ext <;> funext c <;>
      simp [cosmicD0, cosmicDeltaCarry, cosmicDeltaDigit, mul_sub]

def cosmicD1Linear : (CompletedCosmos × CompletedCosmos) →ₗ[ℤ] CompletedCosmos where
  toFun := cosmicD1
  map_add' := by
    intro f g; funext c
    simp [cosmicD1, cosmicDeltaCarry, cosmicDeltaDigit]; ring
  map_smul' := by
    intro z f; funext c
    simp [cosmicD1, cosmicDeltaCarry, cosmicDeltaDigit, mul_sub]; ring
''',
    '''def cosmicD0Linear : CompletedCosmos →ₗ[ℤ] (CompletedCosmos × CompletedCosmos) where
  toFun := cosmicD0
  map_add' := by
    intro f g
    apply Prod.ext <;> funext c <;>
      simp [cosmicD0, cosmicDeltaCarry, cosmicDeltaDigit] <;> ring
  map_smul' := by
    intro z f; apply Prod.ext <;> funext c <;>
      simp [cosmicD0, cosmicDeltaCarry, cosmicDeltaDigit, mul_sub]

def cosmicD1Linear : (CompletedCosmos × CompletedCosmos) →ₗ[ℤ] CompletedCosmos where
  toFun := cosmicD1
  map_add' := by
    intro f g
    funext c
    simp [cosmicD1, cosmicDeltaCarry, cosmicDeltaDigit]
  map_smul' := by
    intro z f; funext c
    simp [cosmicD1, cosmicDeltaCarry, cosmicDeltaDigit, mul_sub]; ring
''',
)
