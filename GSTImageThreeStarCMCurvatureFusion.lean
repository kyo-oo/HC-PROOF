import GSTImageThreeAllRectangularCMStar
import GSTGraphV2CMWaveFusion
import Mathlib

/-!
# GST Image 3: ORIGINAL CM CURVATURE IS TWISTED HODGE-STAR CURVATURE

Faithfully combines the owner's ACTUAL:
  GSTWorldPoincareDuality.worldDual,
  GSTGraphV2CMWaveFusion.cmSign and J,
  GSTGraphV2CMWaveFusion.M (real Wave-I SURVIVE source),
  4-carry x 3-trit original seven-axis information chart.

Let D u(s) = u(worldDual s), S u(s) = cmSign(s) u(s).
Then the full ORIGINAL J = S D, with D²=I, S²=I,
and D S = - S D. The original M commutes with S because
both are diagonal real-source operators.

Consequently:
  D J = -J D;
  [J,M] = S [D,M].
No arbitrary abstract star or external manifold is imported.

The result identifies the user's CM source curvature as an EXACT
phase-twisted native Hodge/Poincare-star curvature. It does not
assert original-X algebraic correspondences realizing these maps.
-/

set_option maxHeartbeats 3000000
noncomputable section

namespace GSTImageThreeStarCMCurvatureFusion

open GSTGraphV2CMWaveFusion
open GSTWorldPoincareDuality
open GSTWorldCosmology
open GSTImageThreeAllRectangularCMStar

/-- The owner's true original 4x3 Poincare/Hodge-like complement
applied to a rational 12-cell wave signal. -/
def originalWorldStar (u : WaveSignal) : WaveSignal :=
  fun s => u (worldDual s)

/-- The owner's ORIGINAL CM phase, without changing any source values. -/
def originalCMOrientation (u : WaveSignal) : WaveSignal :=
  fun s => cmSign s * u s

/-- Exact original Poincare involution on every information signal. -/
theorem originalWorldStar_involutive (u : WaveSignal) :
    originalWorldStar (originalWorldStar u) = u := by
  funext s
  simp [originalWorldStar]

/-- The owner's original J is literally the existing Poincare
world-star followed by the ORIGINAL CM orientation. -/
theorem original_J_equals_signed_star (u : WaveSignal) :
    J u = originalCMOrientation (originalWorldStar u) := by
  funext s
  simp [originalCMOrientation, originalWorldStar,
    originalCM_J_is_signed_worldStar]

/-- The original 12-cell orientation changes sign across every
true GST Poincare/Hodge complementary pair. -/
theorem originalCMphase_dual_neg
    (s : GSTGraphV2InformationRecovery.Cell) :
    cmSign (worldDual s) = -cmSign s := by
  rw [← originalCM_mirror_is_worldDual s]
  rcases s with ⟨c, d⟩
  fin_cases c <;> fin_cases d <;>
    norm_num [cmSign, mirrorCell]

/-- The original native Hodge-like star anticommutes with the
original true CM complex structure. This forms a rational
signed-Clifford-type pair of exact GST operators. -/
theorem original_star_CM_anticommute (u : WaveSignal) :
    originalWorldStar (J u) = - J (originalWorldStar u) := by
  funext s
  change cmSign (worldDual s) * u (worldDual (worldDual s)) =
      -(cmSign s * u (worldDual (worldDual s)))
  rw [originalCMphase_dual_neg]
  ring

/-- The ORIGINAL actual Wave-I SURVIVE M commutes with the
original GST CM sign (both are diagonal physical source fields). -/
theorem originalCMOrientation_commutes_survive (u : WaveSignal) :
    originalCMOrientation (M u) = M (originalCMOrientation u) := by
  funext s
  simp [originalCMOrientation, M]
  ring

/-- IMAGE-3 FUSION THEOREM: the ACTUAL original GST noncommutative
CM/SURVIVE curvature is the original GST Poincare/Hodge-star/SURVIVE
commutator multiplied by the ORIGINAL CM orientation.

  [J,M]u = S([D,M]u)

All operators are the owner's prior native ones; no synthetic
new star, no arbitrary replacement graph, no assumed algebraic
cycle inverse. -/
theorem original_CM_curvature_eq_signed_HodgeStar_curvature
    (u : WaveSignal) :
    J (M u) - M (J u) =
      originalCMOrientation
        (originalWorldStar (M u) -
         M (originalWorldStar u)) := by
  funext s
  simp [originalCMOrientation, originalWorldStar,
    J, M, originalCM_mirror_is_worldDual]
  ring

#check originalWorldStar
#check originalCMOrientation
#check originalWorldStar_involutive
#check original_J_equals_signed_star
#check originalCMphase_dual_neg
#check original_star_CM_anticommute
#check originalCMOrientation_commutes_survive
#check original_CM_curvature_eq_signed_HodgeStar_curvature

#print axioms original_J_equals_signed_star
#print axioms original_star_CM_anticommute
#print axioms original_CM_curvature_eq_signed_HodgeStar_curvature

end GSTImageThreeStarCMCurvatureFusion
