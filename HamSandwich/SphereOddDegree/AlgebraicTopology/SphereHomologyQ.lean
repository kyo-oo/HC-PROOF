import HamSandwich.SphereOddDegree.TopCatBridge
import HamSandwich.SphereOddDegree.AlgebraicTopology.SingularHomologyQ
import Mathlib

/-!
# Rational top homology of spheres: abbreviations, model bridge, tower type

The ℚ duplication of the sphere-homology abbreviations and the suspension-tower
scaffolding of `SphereTopHomology.lean` and `SphereTopHomologyReduction.lean`
(which are ℤ-hardwired):

* **Top-homology abbreviations.** `sphereHomologyQ k n = Hₖ(Sⁿ; ℚ)` over the
  categorical sphere `TopCat.sphere n`, and `sphereTopHomologyQ n = Hₙ(Sⁿ; ℚ)`.
* **Model bridge.** `sphereModelHomologyIsoQ k n` transports `Hₖ(TopCat.sphere n;
  ℚ)` to rational homology of the raw subtype model `Sphere n`, by functoriality
  through the vendored bridge isomorphism `topCatSphereIso` (coefficient-free).
* **The isomorphism type.** `SphereTopHomologyIsoQ n` is the type of
  identifications `Hₙ(Sⁿ; ℚ) ≅ ℚ`.
* **The suspension tower structure.** `SphereSuspensionTowerQ` bundles the base
  `H₁(S¹; ℚ) ≅ ℚ` and the step `Hₙ₊₁(Sⁿ⁺¹; ℚ) ≅ Hₙ(Sⁿ; ℚ)` (`n ≥ 1`); from a
  tower, `SphereSuspensionTowerQ.isoQ` constructs the identification for all
  `n ≥ 1` by a one-line induction.

The degree/orientation consumer layer of the vendored ℤ files is *not*
duplicated (it is not needed for the ℚ endpoint).
-/

open CategoryTheory AlgebraicTopology

noncomputable section

namespace SphereOddDegree

/-! ## Top-homology abbreviations over `TopCat.sphere n` -/

/-- `Hₖ(Sⁿ; ℚ)`: the `k`-th rational singular homology of Mathlib's categorical
sphere object `TopCat.sphere n`.  (Mirror of `sphereHomologyℤ`.) -/
noncomputable abbrev sphereHomologyQ (k n : ℕ) : ModuleCat.{0} ℚ :=
  (singularHomologyQ k).obj (TopCat.sphere.{0} n)

/-- The **top** rational homology `Hₙ(Sⁿ; ℚ)` — the group that should be
`≅ ℚ`.  (Mirror of `sphereTopHomologyℤ`.) -/
noncomputable abbrev sphereTopHomologyQ (n : ℕ) : ModuleCat.{0} ℚ :=
  sphereHomologyQ n n

/-! ## Model bridge: `TopCat.sphere n` vs. the raw `Sphere n` model -/

/-- **Model bridge on rational homology.** The rational singular homology of the
categorical sphere `TopCat.sphere n` is isomorphic to that of the raw subtype
model `Sphere n`, by applying the homology functor to the coefficient-free
bridge isomorphism `topCatSphereIso`.  (Mirror of `sphereModelHomologyIso`.) -/
noncomputable def sphereModelHomologyIsoQ (k n : ℕ) :
    sphereHomologyQ k n ≅ (singularHomologyQ k).obj (TopCat.of (Sphere n)) :=
  (singularHomologyQ k).mapIso (topCatSphereIso n)

/-! ## The isomorphism type and the suspension tower -/

/-- The **type of rational top-homology identifications** `Hₙ(Sⁿ; ℚ) ≅ ℚ` (over
`TopCat.sphere n`).  (Mirror of `SphereTopHomologyIso`.) -/
abbrev SphereTopHomologyIsoQ (n : ℕ) : Type :=
  sphereTopHomologyQ n ≅ ModuleCat.of ℚ ℚ

/-- A **suspension tower for the rational top homology of spheres**: a base
identification `H₁(S¹; ℚ) ≅ ℚ` and, for every `n ≥ 1`, the top-degree
suspension isomorphism `Hₙ₊₁(Sⁿ⁺¹; ℚ) ≅ Hₙ(Sⁿ; ℚ)`.  (Mirror of
`SphereSuspensionTower`.) -/
structure SphereSuspensionTowerQ where
  /-- The base identification `H₁(S¹; ℚ) ≅ ℚ`. -/
  base : SphereTopHomologyIsoQ 1
  /-- The top-degree suspension isomorphism `Hₙ₊₁(Sⁿ⁺¹; ℚ) ≅ Hₙ(Sⁿ; ℚ)`,
  for every `n ≥ 1`. -/
  step : ∀ n : ℕ, 1 ≤ n → (sphereTopHomologyQ (n + 1) ≅ sphereTopHomologyQ n)

namespace SphereSuspensionTowerQ

variable (T : SphereSuspensionTowerQ)

/-- The shifted rational top-homology identification `Hₖ₊₁(Sᵏ⁺¹; ℚ) ≅ ℚ`, defined
by structural recursion on `k`.  (Mirror of `SphereSuspensionTower.isoSucc`;
`Nat.le_induction` only eliminates into `Prop`, so the data-valued family is
built on the shifted index.) -/
def isoSuccQ (k : ℕ) : SphereTopHomologyIsoQ (k + 1) :=
  Nat.rec T.base (fun j ih => (T.step (j + 1) (by omega)) ≪≫ ih) k

/-- From a rational suspension tower, the top-homology identification
`Hₙ(Sⁿ; ℚ) ≅ ℚ` for every `n ≥ 1`.  (Mirror of `SphereSuspensionTower.iso`.) -/
def isoQ : ∀ n : ℕ, 1 ≤ n → SphereTopHomologyIsoQ n
  | (k + 1), _ => T.isoSuccQ k

@[simp]
theorem isoSuccQ_zero : T.isoSuccQ 0 = T.base := rfl

end SphereSuspensionTowerQ

end SphereOddDegree

/-! ## PORT NOTES (the commander's CI-repair map)

Seams adapted in this file (ℚ duplication of the abbreviations/tower layer):

1. `sphereHomologyℤ`/`sphereTopHomologyℤ`/`sphereModelHomologyIso`/
   `SphereTopHomologyIso` → the `Q` versions at `ModuleCat.{0} ℚ`, coefficient
   object `ModuleCat.of ℚ ℚ`.
2. `topCatSphereIso` (TopCatBridge.lean) is coefficient-free and reused as-is.
3. `SphereSuspensionTowerQ` mirrors `SphereSuspensionTower`
   (SphereTopHomologyReduction.lean) verbatim; the ℤ file's
   `SphereOrientationPos`/degree consumer layer is intentionally NOT duplicated.
-/
