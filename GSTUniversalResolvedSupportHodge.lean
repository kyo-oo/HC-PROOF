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

This identifies exactly the resolved-support part of the universal
construction. The support condition is substantive geometric input:
any already algebraic cycle also admits resolved codimension-(p-1)
support by taking suitable algebraic containing cuts and resolutions.
Thus imposing this support condition on ALL Hodge classes would
restate the missing universal source-production task. The present
native formula constructs cycles only after an actual support has
been geometrically exhibited, and its Lean theorem audits that fact.
-/

set_option maxHeartbeats 12000000
noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeGeometricCycleClassSpine
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

/-! ## Gate 3: ORIGINAL-X reconstruction from affine algebraic data

Let i:Y -> X be a genuine smooth projective divisor, U=X\Y
its affine complement, and j:U -> X the open immersion.

For p=2, any rational (2,2) Hodge alpha on the original X
whose restriction to U has a genuine affine algebraic cycle
representative Z_U admits an explicit NATIVE algebraic cycle on X.

(1) Close Z_U in X to obtain a native codimension-two cycle C.
(2) The difference delta=alpha-cl_X(C) restricts to zero on U.
(3) Localization for the pair (X,U) gives
        delta in im(i_*:H²(Y,Q)->H⁴(X,Q)).
(4) Rational Hodge strictness + Lefschetz (1,1) produce a
    genuine algebraic divisor D_Y on Y with cl_X(i_*D_Y)=delta.
(5) Return C+i_*D_Y on the ORIGINAL X.

This is an exact affine-to-projective algebraization operation,
unlike the earlier supported-source theorem: the new cycle is
supplied only on the open AFFINE U, and the algebraic divisor
correcting the compactification is constructed by the proof.

Producing Z_U for EVERY rational Hodge target remains the new,
independent affine source-construction obligation.
-/

/-- Genuine smooth-affine-open localization and closure comparison
for codimension-two algebraic cycles. The cohomological exactness
input is the localization sequence for the actual open immersion,
not an assumption that the desired target class is algebraic. -/
structure AffineCodimensionTwoLocalization
    (U : Scheme) (HU : Type*)
    [AddCommGroup HU] [Module ℚ HU]
    (G : ResolvedSupportGysin (Y := Y) (X := X)
        (HY := HY) (HX := HX) 1) where
  openInclusion : U ⟶ X.X
  affineCycleClass :
    codimensionCycles U 2 →ₗ[ℚ] HU
  restrictBetti :
    RationalSingularCohomology HX.analytification 4 →ₗ[ℚ] HU
  nativeClosure :
    codimensionCycles U 2 →ₗ[ℚ] codimensionCycles X.X 2
  closure_restriction :
    ∀ Zu : codimensionCycles U 2,
      restrictBetti (HX.cycleClass 2 (nativeClosure Zu)) =
        affineCycleClass Zu
  localization_exact :
    ∀ delta : RationalSingularCohomology HX.analytification 4,
      restrictBetti delta = 0 →
        delta ∈ LinearMap.range G.bettiGysin

/-- ORIGINAL-X codimension-two Hodge reconstruction from a genuine
affine open cycle. The returned cycle is the closure of Zu PLUS
the algebraic divisor correction pushed forward from Y. -/
theorem affine_cycle_plus_divisor_boundary_represents_hodge_two
    {U : Scheme} {HU : Type*}
    [AddCommGroup HU] [Module ℚ HU]
    (SG : GeometricCycleClassSpine X HX)
    (G : ResolvedSupportGysin (Y := Y) (X := X)
        (HY := HY) (HX := HX) 1)
    (B : AffineCodimensionTwoLocalization
        (Y := Y) (X := X) (HY := HY) (HX := HX) U HU G)
    (h11 : DivisorsRepresentHodge11 HY)
    (alpha : RationalSingularCohomology HX.analytification 4)
    (hAlpha : alpha ∈ rationalHodgeSubspace (HX.hodgeBigrading 2))
    (Zu : codimensionCycles U 2)
    (hAffine :
      B.affineCycleClass Zu = B.restrictBetti alpha) :
    ∃ Zx : codimensionCycles X.X 2,
      HX.cycleClass 2 Zx = alpha := by
  let C : codimensionCycles X.X 2 := B.nativeClosure Zu
  let delta : RationalSingularCohomology HX.analytification 4 :=
    alpha - HX.cycleClass 2 C
  have hBoundary : B.restrictBetti delta = 0 := by
    calc
      B.restrictBetti delta =
          B.restrictBetti alpha - B.affineCycleClass Zu := by
            simp only [delta, map_sub, C, B.closure_restriction]
      _ = 0 := sub_eq_zero.mpr hAffine.symm
  have hSupported : delta ∈ LinearMap.range G.bettiGysin :=
    B.localization_exact delta hBoundary
  have hDeltaHodge :
      delta ∈ rationalHodgeSubspace (HX.hodgeBigrading 2) := by
    dsimp [delta]
    exact (rationalHodgeSubspace (HX.hodgeBigrading 2)).sub_mem
      hAlpha (SG.algebraic_is_hodge 2 C)
  let D : codimensionCycles X.X 2 :=
    G.nativeCycle h11 delta hDeltaHodge hSupported
  have hD : HX.cycleClass 2 D = delta :=
    G.nativeCycle_correct h11 delta hDeltaHodge hSupported
  refine ⟨C + D, ?_⟩
  calc
    HX.cycleClass 2 (C + D) =
        HX.cycleClass 2 C + HX.cycleClass 2 D := map_add _ _ _
    _ = HX.cycleClass 2 C + delta := by rw [hD]
    _ = alpha := by dsimp [delta]; abel

/-- The exact affine geometry criterion gives an all-X, codim-2
reduction: constructing the restricted (2,2) class on the affine
complement always suffices for an ACTUAL projective native cycle. -/
theorem all_hodge_two_of_affine_open_cycle_sources
    {U : Scheme} {HU : Type*}
    [AddCommGroup HU] [Module ℚ HU]
    (SG : GeometricCycleClassSpine X HX)
    (G : ResolvedSupportGysin (Y := Y) (X := X)
        (HY := HY) (HX := HX) 1)
    (B : AffineCodimensionTwoLocalization
        (Y := Y) (X := X) (HY := HY) (HX := HX) U HU G)
    (h11 : DivisorsRepresentHodge11 HY)
    (hAffineSources :
      ∀ alpha : RationalSingularCohomology HX.analytification 4,
        alpha ∈ rationalHodgeSubspace (HX.hodgeBigrading 2) →
        ∃ Zu : codimensionCycles U 2,
          B.affineCycleClass Zu = B.restrictBetti alpha) :
    ∀ alpha : RationalSingularCohomology HX.analytification 4,
      alpha ∈ rationalHodgeSubspace (HX.hodgeBigrading 2) →
      ∃ Zx : codimensionCycles X.X 2,
        HX.cycleClass 2 Zx = alpha := by
  intro alpha hAlpha
  obtain ⟨Zu, hZu⟩ := hAffineSources alpha hAlpha
  exact affine_cycle_plus_divisor_boundary_represents_hodge_two
    SG G B h11 alpha hAlpha Zu hZu

/-! ## Every positive codimension: affine Chow closure + lower Hodge

The codimension-two reconstruction above uses Lefschetz (1,1)
for a divisor on the boundary Y.

In the general successor p=q+1, exactly the SAME localization
mechanism needs a native codimension-q Hodge cycle on Y, i.e. a
strictly lower-codimension representative. This is a genuine
induction step on p for all original smooth projective X.

It is not a hidden full Hodge-surjectivity input: only weight q
on the boundary is supplied, never the target weight q+1 on X.
The new affine source is an algebraic codimension-(q+1) cycle
on U=X\Y with the prescribed RESTRICTED rational Betti class.
-/

/-- General affine-to-projective localization and canonical Betti
comparison at the successor codimension p=q+1. -/
structure AffineSuccessorHodgeLocalization
    (q : ℕ) (U : Scheme) (HU : Type*)
    [AddCommGroup HU] [Module ℚ HU] where
  openInclusion : U ⟶ X.X
  affineCycleClass :
    codimensionCycles U (q+1) →ₗ[ℚ] HU
  bettiRestriction :
    RationalSingularCohomology HX.analytification (2*(q+1)) →ₗ[ℚ] HU
  nativeClosure :
    codimensionCycles U (q+1) →ₗ[ℚ]
      codimensionCycles X.X (q+1)
  boundaryNativePush :
    codimensionCycles Y.X q →ₗ[ℚ]
      codimensionCycles X.X (q+1)
  boundaryBettiPush :
    RationalSingularCohomology HY.analytification (2*q) →ₗ[ℚ]
      RationalSingularCohomology HX.analytification (2*(q+1))
  closure_naturality :
    ∀ Zu : codimensionCycles U (q+1),
      bettiRestriction (HX.cycleClass (q+1) (nativeClosure Zu)) =
        affineCycleClass Zu
  boundary_cycleclass_naturality :
    ∀ D : codimensionCycles Y.X q,
      HX.cycleClass (q+1) (boundaryNativePush D) =
        boundaryBettiPush (HY.cycleClass q D)
  boundary_localization_exact :
    ∀ delta : RationalSingularCohomology HX.analytification (2*(q+1)),
      bettiRestriction delta = 0 →
        delta ∈ LinearMap.range boundaryBettiPush
  boundary_rational_hodge_lift :
    ∀ delta : RationalSingularCohomology HX.analytification (2*(q+1)),
      delta ∈ rationalHodgeSubspace (HX.hodgeBigrading (q+1)) →
      delta ∈ LinearMap.range boundaryBettiPush →
      ∃ beta : ClassicalHodgeFiber Y HY q,
        boundaryBettiPush beta.1 = delta

/-- The explicit all-X successor-induction construction.

For a rational (q+1,q+1)-Hodge class alpha on the original X,
construct a genuine affine codimension-(q+1) cycle Zu representing
its open restriction. The remaining boundary discrepancy is the
pushforward of a rational (q,q)-Hodge class on Y, represented by
a lower-codimension native cycle D via the given induction theorem.

The returned ORIGINAL-X cycle is closure(Zu)+i_*(D). -/
theorem affine_boundary_induction_constructs_original_hodge_cycle
    {q : ℕ} {U : Scheme} {HU : Type*}
    [AddCommGroup HU] [Module ℚ HU]
    (SG : GeometricCycleClassSpine X HX)
    (B : AffineSuccessorHodgeLocalization
       (Y := Y) (X := X) (HY := HY) (HX := HX) q U HU)
    (hLower :
      ∀ beta : ClassicalHodgeFiber Y HY q,
        ∃ D : codimensionCycles Y.X q,
          HY.cycleClass q D = beta.1)
    (alpha : RationalSingularCohomology HX.analytification (2*(q+1)))
    (hAlpha : alpha ∈ rationalHodgeSubspace (HX.hodgeBigrading (q+1)))
    (Zu : codimensionCycles U (q+1))
    (hAffine :
      B.affineCycleClass Zu = B.bettiRestriction alpha) :
    ∃ Zx : codimensionCycles X.X (q+1),
      HX.cycleClass (q+1) Zx = alpha := by
  let C : codimensionCycles X.X (q+1) := B.nativeClosure Zu
  let delta : RationalSingularCohomology HX.analytification (2*(q+1)) :=
    alpha - HX.cycleClass (q+1) C
  have hBoundaryZero : B.bettiRestriction delta = 0 := by
    calc
      B.bettiRestriction delta =
          B.bettiRestriction alpha - B.affineCycleClass Zu := by
            simp only [delta, map_sub, C, B.closure_naturality]
      _ = 0 := sub_eq_zero.mpr hAffine.symm
  have hDeltaSupported : delta ∈ LinearMap.range B.boundaryBettiPush :=
    B.boundary_localization_exact delta hBoundaryZero
  have hDeltaHodge :
      delta ∈ rationalHodgeSubspace (HX.hodgeBigrading (q+1)) := by
    dsimp [delta]
    exact (rationalHodgeSubspace (HX.hodgeBigrading (q+1))).sub_mem
      hAlpha (SG.algebraic_is_hodge (q+1) C)
  let beta : ClassicalHodgeFiber Y HY q :=
    Classical.choose (B.boundary_rational_hodge_lift
      delta hDeltaHodge hDeltaSupported)
  have hBeta : B.boundaryBettiPush beta.1 = delta :=
    Classical.choose_spec (B.boundary_rational_hodge_lift
      delta hDeltaHodge hDeltaSupported)
  let D : codimensionCycles Y.X q := Classical.choose (hLower beta)
  have hD : HY.cycleClass q D = beta.1 :=
    Classical.choose_spec (hLower beta)
  refine ⟨C + B.boundaryNativePush D, ?_⟩
  calc
    HX.cycleClass (q+1) (C + B.boundaryNativePush D) =
        HX.cycleClass (q+1) C +
          HX.cycleClass (q+1) (B.boundaryNativePush D) := by
            rw [map_add]
    _ = HX.cycleClass (q+1) C +
          B.boundaryBettiPush (HY.cycleClass q D) := by
            rw [B.boundary_cycleclass_naturality]
    _ = HX.cycleClass (q+1) C +
          B.boundaryBettiPush beta.1 := by rw [hD]
    _ = HX.cycleClass (q+1) C + delta := by rw [hBeta]
    _ = alpha := by dsimp [delta]; abel

/-- ALL-X successor Hodge construction when the affine source
algorithm supplies the genuinely restricted class, and the
lower-codimension boundary Hodge problem has been solved. -/
theorem affine_boundary_hodge_weight_successor
    {q : ℕ} {U : Scheme} {HU : Type*}
    [AddCommGroup HU] [Module ℚ HU]
    (SG : GeometricCycleClassSpine X HX)
    (B : AffineSuccessorHodgeLocalization
       (Y := Y) (X := X) (HY := HY) (HX := HX) q U HU)
    (hLower :
      ∀ beta : ClassicalHodgeFiber Y HY q,
        ∃ D : codimensionCycles Y.X q,
          HY.cycleClass q D = beta.1)
    (hAffineSources :
      ∀ alpha : RationalSingularCohomology HX.analytification (2*(q+1)),
        alpha ∈ rationalHodgeSubspace (HX.hodgeBigrading (q+1)) →
        ∃ Zu : codimensionCycles U (q+1),
          B.affineCycleClass Zu = B.bettiRestriction alpha) :
    ∀ alpha : RationalSingularCohomology HX.analytification (2*(q+1)),
      alpha ∈ rationalHodgeSubspace (HX.hodgeBigrading (q+1)) →
      ∃ Zx : codimensionCycles X.X (q+1),
        HX.cycleClass (q+1) Zx = alpha := by
  intro alpha hAlpha
  obtain ⟨Zu, hZu⟩ := hAffineSources alpha hAlpha
  exact affine_boundary_induction_constructs_original_hodge_cycle
    SG B hLower alpha hAlpha Zu hZu

#check affine_boundary_induction_constructs_original_hodge_cycle
#check affine_boundary_hodge_weight_successor
#print axioms affine_boundary_induction_constructs_original_hodge_cycle

/-! ## The first EXPLICIT affine algebraic K-theory source

The smooth affine quadric

  Q₂ = Spec R,    xy = z(1-z)

admits the concrete algebraic 2×2 idempotent

       ( z      x   )
   E = ( y     1-z ).

Unlike a holomorphic bundle arising from Oka–Grauert, the image
of E over the algebraic coordinate ring is a finitely generated
PROJECTIVE MODULE BY CONSTRUCTION. No algebraic K₀ representative
has been chosen or assumed in this theorem.

The recursive Clifford matrix factorization documented in the
Mathbox route record generalizes this source to split affine
quadrics of every even dimension 2p. The immediate Lean theorem
below is its nontrivial rank-one algebraic base case, over EVERY
commutative coefficient ring, with no geometry-specific axioms.
-/

namespace GSTAffineCliffordAlgebraization

/-- Explicit polynomial idempotent representing an actual
algebraic line bundle over the affine split quadric xy=z(1-z). -/
def quadricBottProjector
    {R : Type*} [CommRing R]
    (x y z : R) : Matrix (Fin 2) (Fin 2) R :=
  ![![z, x], ![y, 1-z]]

/-- Polynomial identity in *every commutative ring* satisfying
the quadric equation. It constructs a genuine algebraic projective
module by the image-of-idempotent construction, not a selected
topological or holomorphic K₀ class. -/
theorem quadricBottProjector_idempotent
    {R : Type*} [CommRing R]
    (x y z : R) (hQuadric : x*y = z*(1-z)) :
    quadricBottProjector x y z * quadricBottProjector x y z =
      quadricBottProjector x y z := by
  let E := quadricBottProjector x y z
  obtain ⟨h00, h01, h10, h11⟩ := Matrix.two_mul_expl E E
  change E * E = E
  ext i j
  fin_cases i <;> fin_cases j
  · rw [h00]
    simp [E, quadricBottProjector, hQuadric]
    ring
  · rw [h01]
    simp [E, quadricBottProjector]
    ring
  · rw [h10]
    simp [E, quadricBottProjector]
    ring
  · rw [h11]
    simp [E, quadricBottProjector, hQuadric]
    ring

/-! ## UNIVERSAL AFFINE REPLACEMENT projector for arbitrary X

For EVERY projective embedding X⊂P^N, the explicit affine
Jouanolou incidence complement J(X) has coordinate functions
e_ij=x_i λ_j/(Σ x_k λ_k). These are regular on the complement
and satisfy the rank-one equations

  e_ik * e_kj = e_ij * e_kk,    Σ_k e_kk = 1.

The following formal theorem proves the resulting square matrix
is an algebraic idempotent in EVERY size and EVERY coefficient
commutative ring. Thus its image is a genuine algebraic
projective module over the affine incidence coordinate ring.

This is an actual all-X source: no K₀ preimage or Hodge class
was supplied to the construction. This first rank-one source
recovers the algebraic tautological bundle; independent
higher-rank projectors are needed for arbitrary primitive α.
-/

/-- Universal rank-one incidence relation plus trace-one gives
an explicit algebraic projector over ANY commutative ring.
The intended geometric inputs are actual regular functions
on the affine Jouanolou model of any projective variety X. -/
theorem incidenceRankOneMatrix_idempotent
    {R : Type*} [CommRing R]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Matrix ι ι R)
    (hMinor : ∀ i j k : ι,
       E i k * E k j = E i j * E k k)
    (hTrace : (∑ k : ι, E k k) = 1) :
    E * E = E := by
  ext i j
  calc
    (E * E) i j = ∑ k : ι, E i k * E k j := Matrix.mul_apply
    _ = ∑ k : ι, E i j * E k k := by
      apply Finset.sum_congr rfl
      intro k _
      exact hMinor i j k
    _ = E i j * (∑ k : ι, E k k) := by
      rw [Finset.mul_sum]
    _ = E i j := by rw [hTrace, mul_one]

/-! ## Higher-rank affine source from the ACTUAL Jacobian

For a smooth affine complete intersection U⊂A^m cut out by
c equations f₁,...,f_c, its actual coordinate Jacobian
J:A^m→A^c is split surjective: the maximal minors generate
the unit ideal by the Jacobian smoothness criterion, and
Bezout combinations of the minors construct an algebraic
right inverse B with J∘B=id.

The explicit map P=id-B∘J is an IDEMPOTENT with image
ker(J), the algebraic tangent module T_U. This is an
independent higher-rank algebraic K₀ source computable
directly from the equations of U. No desired rational Hodge
class is a premise. On general smooth affine U an algebraic
projective cotangent presentation supplies the analogous
idempotent after a projective-module splitting.

The next geometric task is to calculate which primitive Hodge
directions the Chern classes of such genuinely manufactured
higher-rank projectors actually span on J(X).
-/

/-- The exact algebraic tangent-module projector produced by
a Jacobian J with a polynomial/algebraic right inverse B. -/
def algebraicJacobianKernelProjector
    {R : Type*} [CommRing R]
    {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (J : M →ₗ[R] N) (B : N →ₗ[R] M) : M →ₗ[R] M :=
  LinearMap.id - B.comp J

/-- Every output of the polynomial Jacobian projector lies in
the genuine tangent kernel of the defining affine equations. -/
theorem algebraicJacobianKernelProjector_in_kernel
    {R : Type*} [CommRing R]
    {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (J : M →ₗ[R] N) (B : N →ₗ[R] M)
    (hJB : J.comp B = LinearMap.id) (v : M) :
    J (algebraicJacobianKernelProjector J B v) = 0 := by
  have hSplit (w : N) : J (B w) = w := by
    have hw := congrArg (fun f : N →ₗ[R] N => f w) hJB
    simpa only [LinearMap.comp_apply, LinearMap.id_apply] using hw
  change J (v - B (J v)) = 0
  rw [map_sub, hSplit]
  exact sub_self (J v)

/-- A tangent vector in ker J is fixed by the explicit
algebraic Jacobian idempotent. -/
theorem algebraicJacobianKernelProjector_fixes_kernel
    {R : Type*} [CommRing R]
    {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (J : M →ₗ[R] N) (B : N →ₗ[R] M)
    (v : M) (hv : J v = 0) :
    algebraicJacobianKernelProjector J B v = v := by
  change v - B (J v) = v
  rw [hv, map_zero, sub_zero]

/-- The concrete polynomial id-BJ construction is a
higher-rank ALGEBRAIC idempotent for any split Jacobian. -/
theorem algebraicJacobianKernelProjector_idempotent
    {R : Type*} [CommRing R]
    {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (J : M →ₗ[R] N) (B : N →ₗ[R] M)
    (hJB : J.comp B = LinearMap.id) :
    (algebraicJacobianKernelProjector J B).comp
      (algebraicJacobianKernelProjector J B) =
        algebraicJacobianKernelProjector J B := by
  ext v
  change algebraicJacobianKernelProjector J B
      (algebraicJacobianKernelProjector J B v) =
        algebraicJacobianKernelProjector J B v
  exact algebraicJacobianKernelProjector_fixes_kernel
    J B (algebraicJacobianKernelProjector J B v)
    (algebraicJacobianKernelProjector_in_kernel J B hJB v)

#check algebraicJacobianKernelProjector_idempotent
#print axioms algebraicJacobianKernelProjector_idempotent

#check incidenceRankOneMatrix_idempotent
#print axioms incidenceRankOneMatrix_idempotent

#check quadricBottProjector
#check quadricBottProjector_idempotent
#print axioms quadricBottProjector_idempotent

end GSTAffineCliffordAlgebraization

#check affine_cycle_plus_divisor_boundary_represents_hodge_two
#check all_hodge_two_of_affine_open_cycle_sources
#print axioms affine_cycle_plus_divisor_boundary_represents_hodge_two

#check ResolvedSupportGysin.nativeCycle_correct
#check resolved_support_hodge_class_is_algebraic
#check divisor_supported_hodge_two_is_algebraic
#check missing_hodge_class_avoids_resolved_support
#print axioms resolved_support_hodge_class_is_algebraic

end GSTUniversalResolvedSupportHodge
