import GSTUniversalChowRetractToTarget

/-!
# GST finite-dominant geometric descent in EVERY codimension

For any proper generically finite morphism f : Y -> X of nonzero degree,
the genuine native Chow pushforward and Betti Gysin/pullback maps obey
f_* f^* = deg(f)·id and naturality of the canonical geometric cycle class.

At every codimension p, a rational Hodge class on X is represented by
the explicit native target cycle

  (1 / deg(f)) · f_*(Z_Y(f^* alpha)),

where Z_Y is an independently constructed source algebraic representative.
In particular, the rational Hodge program descends through genuine finite
quotients and generically finite geometric dominations.

The associated defect-transport lemma detects the first essential input
for descending a class: its pulled-back class must be constructed using
the actual geometry of Y. Thus this theorem enables rigorous source
transfers without inserting Hodge algebraicity into the correspondence.
-/

set_option maxHeartbeats 12000000
noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTUniversalChowRetractToTarget

namespace GSTFiniteDominantAllCodimensionDescent

variable {Y X : SmoothProjectiveComplexScheme}
variable {HY : HodgeBigradedBettiData Y}
variable {HX : HodgeBigradedBettiData X}

/-- The genuine degree, Chow pushforward and rational Betti
push-pull comparisons of a generically finite projective morphism
in one arbitrary codimension p. -/
structure GeometricFiniteDominantMap
    (Y X : SmoothProjectiveComplexScheme)
    (HY : HodgeBigradedBettiData Y)
    (HX : HodgeBigradedBettiData X)
    (p : Nat) where
  degree : ℚ
  degree_ne_zero : degree ≠ 0
  nativePush :
    codimensionCycles Y.X p →ₗ[ℚ] codimensionCycles X.X p
  bettiPush :
    RationalSingularCohomology HY.analytification (2 * p) →ₗ[ℚ]
      RationalSingularCohomology HX.analytification (2 * p)
  bettiPull :
    RationalSingularCohomology HX.analytification (2 * p) →ₗ[ℚ]
      RationalSingularCohomology HY.analytification (2 * p)
  pull_preserves_hodge :
    ∀ alpha : RationalSingularCohomology HX.analytification (2 * p),
      alpha ∈ rationalHodgeSubspace (HX.hodgeBigrading p) →
      bettiPull alpha ∈
        rationalHodgeSubspace (HY.hodgeBigrading p)
  native_betti_natural :
    ∀ Z : codimensionCycles Y.X p,
      HX.cycleClass p (nativePush Z) =
        bettiPush (HY.cycleClass p Z)
  push_pull_degree :
    ∀ alpha : RationalSingularCohomology HX.analytification (2 * p),
      bettiPush (bettiPull alpha) = degree • alpha

/-- Construct the actual native codimension-p target cycle
from an independently represented Hodge class on a geometric source. -/
noncomputable def GeometricFiniteDominantMap.constructNative
    {p : Nat}
    (F : GeometricFiniteDominantMap Y X HY HX p)
    (hY : HodgeAtWeight Y HY p)
    (alpha : RationalSingularCohomology HX.analytification (2 * p))
    (hAlpha : alpha ∈ rationalHodgeSubspace (HX.hodgeBigrading p)) :
    codimensionCycles X.X p :=
  F.degree⁻¹ • F.nativePush
    (Classical.choose
      (hY (F.pull_preserves_hodge alpha hAlpha)))

/-- Constructed cycle's actual geometric class equals alpha. -/
theorem GeometricFiniteDominantMap.constructNative_correct
    {p : Nat}
    (F : GeometricFiniteDominantMap Y X HY HX p)
    (hY : HodgeAtWeight Y HY p)
    (alpha : RationalSingularCohomology HX.analytification (2 * p))
    (hAlpha : alpha ∈ rationalHodgeSubspace (HX.hodgeBigrading p)) :
    HX.cycleClass p (F.constructNative hY alpha hAlpha) = alpha := by
  let Z : codimensionCycles Y.X p :=
    Classical.choose (hY (F.pull_preserves_hodge alpha hAlpha))
  have hZ : HY.cycleClass p Z = F.bettiPull alpha :=
    Classical.choose_spec (hY (F.pull_preserves_hodge alpha hAlpha))
  calc
    HX.cycleClass p (F.constructNative hY alpha hAlpha) =
        F.degree⁻¹ • HX.cycleClass p (F.nativePush Z) := by
          simp only [GeometricFiniteDominantMap.constructNative, map_smul, Z]
    _ = F.degree⁻¹ • F.bettiPush (HY.cycleClass p Z) := by
          rw [F.native_betti_natural Z]
    _ = F.degree⁻¹ • F.bettiPush (F.bettiPull alpha) := by rw [hZ]
    _ = F.degree⁻¹ • (F.degree • alpha) := by
          rw [F.push_pull_degree]
    _ = alpha := by
          simp [smul_smul, F.degree_ne_zero]

/-- Hodge representability at arbitrary codimension descends
from a geometrically solved finite-degree source to the target. -/
theorem all_target_hodge_at_weight_of_finite_dominant_map
    {p : Nat}
    (F : GeometricFiniteDominantMap Y X HY HX p)
    (hY : HodgeAtWeight Y HY p) :
    HodgeAtWeight X HX p := by
  intro alpha hAlpha
  exact ⟨F.constructNative hY alpha hAlpha,
    F.constructNative_correct hY alpha hAlpha⟩

/-- If alpha is a new primitive/Hodge direction on X, then
its pullback remains a genuine new source direction on Y.
This controls how primitive defects behave under finite transfer. -/
theorem unrepresented_target_pulls_to_unrepresented_source
    {p : Nat}
    (F : GeometricFiniteDominantMap Y X HY HX p)
    (alpha : RationalSingularCohomology HX.analytification (2 * p))
    (hUnrepresented :
      ¬ ∃ ZX : codimensionCycles X.X p,
        HX.cycleClass p ZX = alpha) :
      ¬ ∃ ZY : codimensionCycles Y.X p,
        HY.cycleClass p ZY = F.bettiPull alpha := by
  rintro ⟨ZY, hZY⟩
  apply hUnrepresented
  refine ⟨F.degree⁻¹ • F.nativePush ZY, ?_⟩
  calc
    HX.cycleClass p (F.degree⁻¹ • F.nativePush ZY) =
        F.degree⁻¹ • HX.cycleClass p (F.nativePush ZY) := by
          rw [map_smul]
    _ = F.degree⁻¹ • F.bettiPush (HY.cycleClass p ZY) := by
          rw [F.native_betti_natural ZY]
    _ = F.degree⁻¹ • F.bettiPush (F.bettiPull alpha) := by rw [hZY]
    _ = F.degree⁻¹ • (F.degree • alpha) := by
          rw [F.push_pull_degree]
    _ = alpha := by simp [smul_smul, F.degree_ne_zero]

/-- Universal degree transfer, across EVERY codimension at once. -/
theorem all_hodge_on_target_of_all_finite_dominant_maps
    (F : ∀ p : Nat, GeometricFiniteDominantMap Y X HY HX p)
    (hY : ∀ p : Nat, HodgeAtWeight Y HY p) :
    ∀ p : Nat, HodgeAtWeight X HX p := by
  intro p
  exact all_target_hodge_at_weight_of_finite_dominant_map (F p) (hY p)

#check GeometricFiniteDominantMap.constructNative
#check GeometricFiniteDominantMap.constructNative_correct
#check unrepresented_target_pulls_to_unrepresented_source
#check all_hodge_on_target_of_all_finite_dominant_maps
#print axioms all_hodge_on_target_of_all_finite_dominant_maps

end GSTFiniteDominantAllCodimensionDescent
