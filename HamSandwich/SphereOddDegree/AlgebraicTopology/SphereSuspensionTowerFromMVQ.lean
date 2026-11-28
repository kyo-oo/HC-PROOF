import HamSandwich.SphereOddDegree.AlgebraicTopology.SphereHomologyS1BaseMVQ
import HamSandwich.SphereOddDegree.AlgebraicTopology.SphereHomologyMVStepQ
import HamSandwich.SphereOddDegree.AlgebraicTopology.SphereHomologyQ

/-!
# The unconditional rational suspension tower and its stable export

The ℚ duplication of the assembly step (`SphereSuspensionTowerFromMV.lean` +
the stable-export layer of `SphereOrientationPosFromMV.lean`): the two
Mayer–Vietoris ingredients proved at ℚ are assembled into a single concrete,
unconditional term of type `SphereSuspensionTowerQ`:

* the base case `sphereTopHomologyIsoQ_one : SphereTopHomologyIsoQ 1`
  (i.e. `H₁(S¹; ℚ) ≅ ℚ`), from `SphereHomologyS1BaseMVQ.lean`, and
* the recursive step `sphereTopHomologyQ_step_MV : Hₙ₊₁(Sⁿ⁺¹; ℚ) ≅ Hₙ(Sⁿ; ℚ)`
  (`n ≥ 1`), from `SphereHomologyMVStepQ.lean`.

From the tower, `sphereTopHomologyIso_unconditional_Q` gives the rational
top-homology identification `Hₙ(Sⁿ; ℚ) ≅ ℚ` for **every** `n ≥ 1`.  (The ℤ
files' orientation/degree consumer layer is not needed at ℚ and is not
duplicated.)
-/

open CategoryTheory

noncomputable section

namespace SphereOddDegree

/-- **The unconditional rational sphere suspension tower**, assembled from the
Mayer–Vietoris base case `sphereTopHomologyIsoQ_one` and the Mayer–Vietoris
recursive step `sphereTopHomologyQ_step_MV`.  (Mirror of
`sphereSuspensionTower_from_MV`.) -/
def sphereSuspensionTowerQ_from_MV : SphereSuspensionTowerQ where
  base := sphereTopHomologyIsoQ_one
  step := fun n hn => sphereTopHomologyQ_step_MV n hn

/-- Compatibility alias: the unconditional rational suspension tower. -/
def sphereSuspensionTowerQ_unconditional : SphereSuspensionTowerQ :=
  sphereSuspensionTowerQ_from_MV

/-- **Stable projection.** The rational top-homology identification
`Hₙ(Sⁿ; ℚ) ≅ ℚ` for every dimension `n ≥ 1`, read off the unconditional
rational suspension tower.  (Mirror of `sphereTopHomologyIso_unconditional`.)
This is the ℚ endpoint's engine: at `n = 2` it is
`H₂(S²; ℚ) ≅ ModuleCat.of ℚ ℚ` over `TopCat.sphere 2`. -/
def sphereTopHomologyIso_unconditional_Q (n : ℕ) (hn : 1 ≤ n) :
    SphereTopHomologyIsoQ n :=
  sphereSuspensionTowerQ_from_MV.isoQ n hn

/-- Alias for `sphereTopHomologyIso_unconditional_Q`: the positive-dimensional
rational top-homology identification `Hₙ(Sⁿ; ℚ) ≅ ℚ` (`n ≥ 1`). -/
def sphereTopHomologyIso_of_pos_Q (n : ℕ) (hn : 1 ≤ n) :
    SphereTopHomologyIsoQ n :=
  sphereTopHomologyIso_unconditional_Q n hn

@[simp]
theorem sphereTopHomologyIso_unconditional_Q_eq (n : ℕ) (hn : 1 ≤ n) :
    sphereTopHomologyIso_unconditional_Q n hn =
      sphereSuspensionTowerQ_from_MV.isoQ n hn := rfl

@[simp]
theorem sphereTopHomologyIso_of_pos_Q_eq (n : ℕ) (hn : 1 ≤ n) :
    sphereTopHomologyIso_of_pos_Q n hn =
      sphereTopHomologyIso_unconditional_Q n hn := rfl

end SphereOddDegree

/-! ## Receipts -/

#check @SphereOddDegree.sphereSuspensionTowerQ_from_MV
#check @SphereOddDegree.sphereTopHomologyIso_unconditional_Q

#print axioms SphereOddDegree.sphereSuspensionTowerQ_from_MV
#print axioms SphereOddDegree.sphereTopHomologyIso_unconditional_Q

/-! ## PORT NOTES (the commander's CI-repair map)

Seams adapted in this file (ℚ duplication of the tower assembly):

1. `SphereSuspensionTower`/`sphereSuspensionTower_from_MV`/
   `sphereTopHomologyIso_unconditional` → the `Q` versions; the `base` and
   `step` fields consume `sphereTopHomologyIsoQ_one` and
   `sphereTopHomologyQ_step_MV` (both at ℚ).
2. The ℤ files' `SphereOrientationPos`/`SphereOrientation`/degree layer
   (`SphereTopHomologyReduction.lean`, `SphereOrientationPosFromMV.lean`) is
   intentionally NOT duplicated: the ℚ endpoint needs only the isomorphism
   family, not the degree theory.
-/
