import HamSandwich.SphereOddDegree.AlgebraicTopology.SphereHomologyMVStep
import HamSandwich.SphereOddDegree.AlgebraicTopology.SphereHomologyQ
import HamSandwich.SphereOddDegree.AlgebraicTopology.SubChainSubspaceBridgeQ
import HamSandwich.SphereOddDegree.AlgebraicTopology.MayerVietoris
import Mathlib

/-!
# The Mayer–Vietoris recursive step for rational sphere homology

The ℚ duplication of the assembly section of `SphereHomologyMVStep.lean`
(the geometric band machinery of that file — punctured spheres, the equatorial
band, its contraction/homotopy equivalence to `Sⁿ`, and the open cover — is
coefficient-free and is *reused*):

* `bandHomologyIsoQ` — the rational homology of the equatorial band of `Sⁿ⁺¹` is
  `Hₙ(Sⁿ; ℚ)`, via the rational subspace bridge, rational homotopy invariance,
  and the rational model bridge;
* `sphereTopHomologyQ_step_MV` — **for `n ≥ 1`,
  `Hₙ₊₁(Sⁿ⁺¹; ℚ) ≅ Hₙ(Sⁿ; ℚ)`**, from the `[CommRing R]`-generic
  Mayer–Vietoris connecting isomorphism `mvHomologyIso_succ` instantiated at
  `ℚ`, with the four vanishing inputs supplied by
  `isZero_subChainComplex_homology_of_contractibleQ`.

This is the `step` field of `SphereSuspensionTowerQ`.
-/

set_option maxHeartbeats 4000000

open CategoryTheory AlgebraicTopology Limits Metric
open SphereOddDegree.AffineBarycentricSubdivision

noncomputable section
namespace SphereOddDegree

variable (n : ℕ)

/-- The rational homology of the band is isomorphic to `Hₙ(Sⁿ; ℚ)`, via the
rational subspace bridge, rational homotopy invariance, and the rational model
bridge.  (Mirror of `bandHomologyIso`.) -/
def bandHomologyIsoQ :
    (subChainComplex ℚ (sphereSpace n)
      ((upperOpens n : Set (sphereSpace n)) ∩ (lowerOpens n : Set (sphereSpace n)))).homology n ≅
      sphereTopHomologyQ n :=
  subspaceHomologyIsoQ (sphereSpace n)
      ((upperOpens n : Set (sphereSpace n)) ∩ (lowerOpens n : Set (sphereSpace n))) n
    ≪≫ singularHomologyQ_isoOfHomotopyEquivSpace n (sphereBandHomotopyEquiv n)
    ≪≫ (sphereModelHomologyIsoQ n n).symm

/-- **The Mayer–Vietoris recursive step at ℚ.** For `n ≥ 1`,
`Hₙ₊₁(Sⁿ⁺¹; ℚ) ≅ Hₙ(Sⁿ; ℚ)`.  (Mirror of `sphereTopHomology_step_MV`; the
Mayer–Vietoris machinery `mvHomologyIso_succ` is `[CommRing R]`-generic and is
instantiated at `ℚ`.) -/
def sphereTopHomologyQ_step_MV (hn : 1 ≤ n) :
    sphereTopHomologyQ (n + 1) ≅ sphereTopHomologyQ n :=
  sphereModelHomologyIsoQ (n + 1) (n + 1)
    ≪≫ mvHomologyIso_succ ℚ (upperOpens n) (lowerOpens n) (upperOpens_sup_lowerOpens n) n
        (isZero_subChainComplex_homology_of_contractibleQ _ _ (n + 1) (by omega))
        (isZero_subChainComplex_homology_of_contractibleQ _ _ (n + 1) (by omega))
        (isZero_subChainComplex_homology_of_contractibleQ _ _ n hn)
        (isZero_subChainComplex_homology_of_contractibleQ _ _ n hn)
    ≪≫ bandHomologyIsoQ n

end SphereOddDegree

/-! ## PORT NOTES (the commander's CI-repair map)

Seams adapted in this file (ℚ duplication of the MV step):

1. The entire geometric preamble of `SphereHomologyMVStep.lean`
   (`northPole`/`southPole`, `upperPunctured`/`lowerPunctured`, contractibility
   of the punctured spheres, the band ≃ `Sⁿ` homotopy equivalence
   `sphereBandHomotopyEquiv`, `sphereSpace`/`upperOpens`/`lowerOpens`/
   `upperOpens_sup_lowerOpens`, and the `ContractibleSpace` instances) is
   coefficient-free and **reused** from the vendored file — no duplication.
2. `subspaceHomologyIsoℤ` → `subspaceHomologyIsoQ`,
   `singularHomologyℤ_isoOfHomotopyEquivSpace` →
   `singularHomologyQ_isoOfHomotopyEquivSpace`, `sphereModelHomologyIso` →
   `sphereModelHomologyIsoQ`.
3. `mvHomologyIso_succ ℤ …` → `mvHomologyIso_succ ℚ …`: the MV machinery
   (`mvShortComplex`, `mvShortExact`, `smallChains_homologyIso`,
   `mvConnectingIso`, `mvHomologyIso_succ` in `MayerVietorisSES.lean` /
   `MayerVietoris.lean` / `SmallChainsQuasiIso.lean`) is `[CommRing R]`-generic
   throughout; only the four vanishing arguments change from the ℤ
   `isZero_subChainComplex_homology_of_contractible` to the ℚ
   `isZero_subChainComplex_homology_of_contractibleQ`.
-/
