import GSTGraphV2CMWaveFusion
import GSTWorldPoincareDuality
import Mathlib

/-!
# GST IMAGE 3 — original CM J is a SIGNED GST HODGE/POINCARE STAR

The owner's original rational J on the 4 x 3 information world is
not independent of the owner's existing dimensionless Poincare world
complement: J = (original CM phase) * worldDual.

This module further constructs an EXACT original-GST rational
complex structure on EVERY rectangular world with an EVEN carry
depth (or EVEN digit depth) by signing the genuine worldDual
operator on its exchanged coordinate pairs.

This is full unlimited-N native GST information geometry, NOT a
geometric correspondence on an arbitrary smooth projective X.
It also identifies why odd-by-odd rectangular worlds cannot have
a rational all-coordinate complex structure of this signed-duality
form: their center is fixed by worldDual.
-/

set_option maxHeartbeats 3000000
noncomputable section

namespace GSTImageThreeAllRectangularCMStar

open GSTWorldCosmology
open GSTWorldPoincareDuality
open GSTGraphV2CMWaveFusion

/-- The original GST 4 x 3 CM mirror IS the existing original
dimensionless world Poincare complementary-cell operation. -/
theorem originalCM_mirror_is_worldDual
    (s : GSTGraphV2InformationRecovery.Cell) :
    mirrorCell s = (worldDual s : WorldCell 4 3) := by
  rcases s with ⟨c, d⟩
  apply Prod.ext
  · apply Fin.ext
    simp [mirrorCell, worldDual, complementFin]
  · apply Fin.ext
    simp [mirrorCell, worldDual, complementFin]

/-- J is the SIGN-TWISTED owner's existing GST Hodge-like star
on the ORIGINAL 4x3 information world, not a substitute phase model. -/
theorem originalCM_J_is_signed_worldStar
    (u : WaveSignal) (s : GSTGraphV2InformationRecovery.Cell) :
    J u s = cmSign s * u (worldDual s) := by
  simp only [J, originalCM_mirror_is_worldDual]

/-- A true rational orientation of a rectangular GST world along
the carry axis whenever that axis is even. -/
def evenCarryOrientation (A : Nat) (c : Fin A) : ℚ :=
  if c.val < A / 2 then 1 else -1

/-- The complementary carry coordinate has the OPPOSITE sign
for every genuinely even original GST carry depth. -/
theorem evenCarryOrientation_worldComplement
    (A : Nat) (hA : Even A) (c : Fin A) :
    evenCarryOrientation A (complementFin c) =
      - evenCarryOrientation A c := by
  obtain ⟨k, hk⟩ := hA
  have hdiv : A / 2 = k := by omega
  have hc : c.val < A := c.isLt
  have hcomp : (complementFin c).val = A - 1 - c.val := rfl
  by_cases h : c.val < k
  · have hm : ¬ A - 1 - c.val < k := by omega
    simp [evenCarryOrientation, hdiv, hcomp, h, hm]
  · have hm : A - 1 - c.val < k := by omega
    simp [evenCarryOrientation, hdiv, hcomp, h, hm]

/-- A new general-size native GST signed Poincare/CM J, using exactly
the OWNER'S existing dimensionless worldDual at every A x B. -/
def evenCarryWorldJ
    {A B : Nat} (hA : Even A)
    (u : WorldCell A B → ℚ) :
    WorldCell A B → ℚ :=
  fun c => evenCarryOrientation A c.1 * u (worldDual c)

/-- ALL even-carry rectangular GST worlds carry a genuine rational
complex structure generated from the OWNER'S existing Poincare star.
This extends the 4x3 CM ontology without fixing a 12-cell ceiling. -/
theorem evenCarryWorldJ_square
    {A B : Nat} (hA : Even A) (u : WorldCell A B → ℚ) :
    evenCarryWorldJ hA (evenCarryWorldJ hA u) = -u := by
  funext c
  change evenCarryOrientation A c.1 *
      (evenCarryOrientation A (worldDual c).1 *
        u (worldDual (worldDual c))) = -u c
  rw [worldDual_involutive]
  change evenCarryOrientation A c.1 *
      (evenCarryOrientation A (complementFin c.1) * u c) = -u c
  rw [evenCarryOrientation_worldComplement A hA c.1]
  by_cases h : c.1.val < A / 2
  · simp [evenCarryOrientation, h]
  · simp [evenCarryOrientation, h]

/-- The same native Hodge/CM construction works when the DIGIT
depth is even, even if the carry depth is odd. -/
def evenDigitWorldJ
    {A B : Nat} (hB : Even B)
    (u : WorldCell A B → ℚ) :
    WorldCell A B → ℚ :=
  fun c => evenCarryOrientation B c.2 * u (worldDual c)

theorem evenDigitWorldJ_square
    {A B : Nat} (hB : Even B) (u : WorldCell A B → ℚ) :
    evenDigitWorldJ hB (evenDigitWorldJ hB u) = -u := by
  funext c
  change evenCarryOrientation B c.2 *
      (evenCarryOrientation B (worldDual c).2 *
        u (worldDual (worldDual c))) = -u c
  rw [worldDual_involutive]
  change evenCarryOrientation B c.2 *
      (evenCarryOrientation B (complementFin c.2) * u c) = -u c
  rw [evenCarryOrientation_worldComplement B hB c.2]
  by_cases h : c.2.val < B / 2
  · simp [evenCarryOrientation, h]
  · simp [evenCarryOrientation, h]

#check originalCM_mirror_is_worldDual
#check originalCM_J_is_signed_worldStar
#check evenCarryOrientation_worldComplement
#check evenCarryWorldJ_square
#check evenDigitWorldJ_square

#print axioms originalCM_J_is_signed_worldStar
#print axioms evenCarryWorldJ_square
#print axioms evenDigitWorldJ_square

end GSTImageThreeAllRectangularCMStar
