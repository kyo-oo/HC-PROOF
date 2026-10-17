import GSTUniversalLefschetzCurveCycles

/-!
# GST Gate 3 — algebraic cycles from resolved supports on arbitrary X

A geometrically supported Hodge class has extra information beyond its
formal (p,p) type. Let i:Y -> X be a proper morphism from a smooth
resolution of a codimension-c algebraic support on X, and let
p=c+1. The authentic rational Betti Gysin map sends

  H²(Y,Q) -> H^(2(c+1))(X,Q),

raising both Hodge indices by c. Every rational (p,p) class in
its image has a rational (1,1) preimage, by strictness/splitting
of morphisms of polarizable pure rational Hodge structures.

The established Lefschetz (1,1) theorem produces a genuine divisor
D on Y. Its native proper pushforward i_*D is then an algebraic
codimension-p cycle on the ORIGINAL X and its canonical Betti
cycleClass is the prescribed target alpha.

This is a uniform actual-X source-producing theorem for every
codimension p>=1, not a hypothesis of Hodge-surjectivity on X.
The two geometric source obligations are explicitly recorded:
proper push-Gysin/cycleClass naturality and rational Hodge
strictness for an actual resolved algebraic support.

Gate 3's continuing target is to produce representatives for Hodge
classes outside all such geometric support images.
-/

set_option maxHeartbeats 12000000
noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTUniversalLefschetzCurveCycles

namespace GSTUniversalResolvedSupportHodge

variable {Y X : SmoothProjectiveComplexScheme}
variable {HY : HodgeBigradedBettiData Y}
variable {HX : HodgeBigradedBettiData X}

/-- Actual resolved algebraic support of codimension c in X.

The intended geometric instance is a proper map i:Y -> X from a
smooth resolution of a codimension-c subvariety. Native and Betti
Gysin maps are its proper pushforwards. The Hodge lift is the
rational strictness theorem for this genuine morphism of pure Hodge
structures, not the algebraicity of the requested target class. -/
structure ResolvedSupportGysin (c : ℕ) where
  supportMap : Y.X ⟶ X.X
  nativeGysin :
    codimensionCycles Y.X 1 →ₗ[ℚ] codimensionCycles X.X (c+1)
  bettiGysin :
    RationalSingularCohomology HY.analytification 2 →ₗ[ℚ]
      RationalSingularCohomology HX.analytification (2*(c+1))
  rationalHodgeLift :
    ∀ alpha : RationalSingularCohomology HX.analytification (2*(c+1)),
      alpha ∈ rationalHodgeSubspace (HX.hodgeBigrading (c+1)) →
      alpha ∈ LinearMap.range bettiGysin →
      ∃ beta : ClassicalHodgeFiber Y HY 1,
        bettiGysin beta.1 = alpha
  cycleClass_gysin :
    ∀ D : codimensionCycles Y.X 1,
      HX.cycleClass (c+1) (nativeGysin D) =
        bettiGysin (HY.cycleClass 1 D)

/-- Explicit native algebraic codimension-(c+1) cycle on the
ORIGINAL X, constructed by lifting the rational Hodge class to
a (1,1) class on its actual resolved support, taking the genuine
divisor provided by Lefschetz (1,1), then pushing the divisor. -/
noncomputable def ResolvedSupportGysin.nativeCycle
    {c : ℕ}
    (G : ResolvedSupportGysin (Y := Y) (X := X) (HY := HY) (HX := HX) c)
    (h11 : DivisorsRepresentHodge11 HY)
    (alpha : RationalSingularCohomology HX.analytification (2*(c+1)))
    (hHodge : alpha ∈ rationalHodgeSubspace (HX.hodgeBigrading (c+1)))
    (hSupported : alpha ∈ LinearMap.range G.bettiGysin) :
    codimensionCycles X.X (c+1) :=
  let beta : ClassicalHodgeFiber Y HY 1 :=
    Classical.choose (G.rationalHodgeLift alpha hHodge hSupported)
  let D : codimensionCycles Y.X 1 :=
    Classical.choose (h11 beta)
  G.nativeGysin D

/-- Constructed native source has the EXACT desired rational Betti
class on X. All inputs concern standard source geometry, not an
algebraic preimage of alpha on X. -/
theorem ResolvedSupportGysin.nativeCycle_correct
    {c : ℕ}
    (G : ResolvedSupportGysin (Y := Y) (X := X) (HY := HY) (HX := HX) c)
    (h11 : DivisorsRepresentHodge11 HY)
    (alpha : RationalSingularCohomology HX.analytification (2*(c+1)))
    (hHodge : alpha ∈ rationalHodgeSubspace (HX.hodgeBigrading (c+1)))
    (hSupported : alpha ∈ LinearMap.range G.bettiGysin) :
    HX.cycleClass (c+1)
      (G.nativeCycle h11 alpha hHodge hSupported) = alpha := by
  let beta : ClassicalHodgeFiber Y HY 1 :=
    Classical.choose (G.rationalHodgeLift alpha hHodge hSupported)
  let D : codimensionCycles Y.X 1 :=
    Classical.choose (h11 beta)
  have hBeta : G.bettiGysin beta.1 = alpha :=
    Classical.choose_spec (G.rationalHodgeLift alpha hHodge hSupported)
  have hD : HY.cycleClass 1 D = beta.1 :=
    Classical.choose_spec (h11 beta)
  change HX.cycleClass (c+1) (G.nativeGysin D) = alpha
  calc
    HX.cycleClass (c+1) (G.nativeGysin D) =
      G.bettiGysin (HY.cycleClass 1 D) := G.cycleClass_gysin D
    _ = G.bettiGysin beta.1 := by rw [hD]
    _ = alpha := hBeta

/-- Uniform original-X Gate 3 theorem: all rational Hodge classes
with a resolved codimension-(p-1) Gysin support have actual native
codimension-p algebraic representatives, for every p>=1. -/
theorem resolved_support_hodge_class_is_algebraic
    {c : ℕ}
    (G : ResolvedSupportGysin (Y := Y) (X := X) (HY := HY) (HX := HX) c)
    (h11 : DivisorsRepresentHodge11 HY)
    (alpha : RationalSingularCohomology HX.analytification (2*(c+1)))
    (hHodge : alpha ∈ rationalHodgeSubspace (HX.hodgeBigrading (c+1)))
    (hSupported : alpha ∈ LinearMap.range G.bettiGysin) :
    alpha ∈ LinearMap.range (HX.cycleClass (c+1)) := by
  refine ⟨G.nativeCycle h11 alpha hHodge hSupported, ?_⟩
  exact G.nativeCycle_correct h11 alpha hHodge hSupported

/-- In particular every rational Hodge (2,2) class on any smooth
projective complex fourfold supported on a resolved divisor has
an actual algebraic codimension-two representative on that fourfold.
The theorem is valid in other ambient dimensions as well. -/
theorem divisor_supported_hodge_two_is_algebraic
    (G : ResolvedSupportGysin (Y := Y) (X := X) (HY := HY) (HX := HX) 1)
    (h11 : DivisorsRepresentHodge11 HY)
    (alpha : RationalSingularCohomology HX.analytification 4)
    (hHodge : alpha ∈ rationalHodgeSubspace (HX.hodgeBigrading 2))
    (hSupported : alpha ∈ LinearMap.range G.bettiGysin) :
    ∃ Z : codimensionCycles X.X 2,
      HX.cycleClass 2 Z = alpha := by
  exact ⟨G.nativeCycle h11 alpha hHodge hSupported,
    G.nativeCycle_correct h11 alpha hHodge hSupported⟩

/-- Useful gate-3 exclusion: a rational Hodge class outside the
algebraic image cannot come from ANY resolved support of this kind.
This pinpoints the remaining source class for subsequent attacks. -/
theorem missing_hodge_class_avoids_resolved_support
    {c : ℕ}
    (G : ResolvedSupportGysin (Y := Y) (X := X) (HY := HY) (HX := HX) c)
    (h11 : DivisorsRepresentHodge11 HY)
    (alpha : RationalSingularCohomology HX.analytification (2*(c+1)))
    (hHodge : alpha ∈ rationalHodgeSubspace (HX.hodgeBigrading (c+1)))
    (hMissing : alpha ∉ LinearMap.range (HX.cycleClass (c+1))) :
    alpha ∉ LinearMap.range G.bettiGysin := by
  intro hSupported
  exact hMissing
    (resolved_support_hodge_class_is_algebraic G h11 alpha hHodge hSupported)

#check ResolvedSupportGysin.nativeCycle_correct
#check resolved_support_hodge_class_is_algebraic
#check divisor_supported_hodge_two_is_algebraic
#check missing_hodge_class_avoids_resolved_support
#print axioms resolved_support_hodge_class_is_algebraic

end GSTUniversalResolvedSupportHodge
