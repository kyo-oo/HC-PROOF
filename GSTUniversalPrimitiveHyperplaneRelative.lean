import GSTGeometricRealizationStage2G

/-!
# GST original-X primitive middle classes and hyperplane-relative geometry

This file attacks the exact geometric mechanism of Gate 3:
  how does an arbitrary rational primitive middle-Hodge class on X
  behave under a genuine smooth hyperplane section i:Y -> X?

For every smooth projective X of even complex dimension 2p and
every smooth ample hyperplane section Y, the ordinary geometric maps
in rational singular Betti cohomology satisfy

  i_* i^* = L      (self-intersection formula),
  i_* injective    (Gysin form of weak Lefschetz),
  im(H^(2p)(X,Y) -> H^(2p)(X)) = ker(i^*).

It follows, for EVERY primitive middle class alpha, that:
  i^* alpha = 0,
  alpha has a relative Betti lift in H^(2p)(X,Y).

Hence an arbitrary nonzero primitive class CANNOT be recovered
from its restriction to one hyperplane: the restriction is zero.
The relative source is a genuine universal cohomological carrier,
but a relative Betti lift is NOT an algebraic codimension-p cycle.
The remaining mathematical task is to produce such an algebraic
cycle without assuming that primitive algebraicity in its input.

The structure below tracks standard topological hyperplane/relative
comparison theorems as independent geometry inputs. It supplies
no target-surjectivity field and chooses no Chow cycle for alpha.
-/

set_option maxHeartbeats 12000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G

namespace GSTUniversalPrimitiveHyperplaneRelative

variable {X Y : SmoothProjectiveComplexScheme}
variable {HX : HodgeBigradedBettiData X}
variable {HY : HodgeBigradedBettiData Y}
variable {W : Type*} [AddCommGroup W] [Module ℚ W]

/-- Rational singular-Betti data for a *genuine smooth hyperplane*
Y⊂X with dim_C X=2p. The relative space W is intended to be
H^(2p)(X_an,Y_an;Q), or H_c^(2p)(X_an\Y_an;Q).

All fields are standard topological identities about an actual
hyperplane, not the Hodge conjecture or its desired cycle witness. -/
structure SmoothMiddleHyperplaneBetti
    (p : ℕ)
    (X Y : SmoothProjectiveComplexScheme)
    (HX : HodgeBigradedBettiData X)
    (HY : HodgeBigradedBettiData Y)
    (W : Type*) [AddCommGroup W] [Module ℚ W] where
  middleRestriction :
    RationalSingularCohomology HX.analytification (2*p) →ₗ[ℚ]
      RationalSingularCohomology HY.analytification (2*p)
  middleGysin :
    RationalSingularCohomology HY.analytification (2*p) →ₗ[ℚ]
      RationalSingularCohomology HX.analytification (2*p+2)
  ampleCup :
    RationalSingularCohomology HX.analytification (2*p) →ₗ[ℚ]
      RationalSingularCohomology HX.analytification (2*p+2)
  gysin_injective : Function.Injective middleGysin
  self_intersection :
    ∀ a : RationalSingularCohomology HX.analytification (2*p),
      middleGysin (middleRestriction a) = ampleCup a
  relativeToX :
    W →ₗ[ℚ]
      RationalSingularCohomology HX.analytification (2*p)
  relative_exact :
    ∀ a : RationalSingularCohomology HX.analytification (2*p),
      middleRestriction a = 0 ↔ a ∈ LinearMap.range relativeToX

/-- For every even-dimensional original X, the geometric middle
primitive condition is EXACTLY vanishing on a smooth hyperplane. -/
theorem SmoothMiddleHyperplaneBetti.primitive_iff_restriction_zero
    {p : ℕ}
    (G : SmoothMiddleHyperplaneBetti p X Y HX HY W)
    (alpha : RationalSingularCohomology HX.analytification (2*p)) :
    G.ampleCup alpha = 0 ↔ G.middleRestriction alpha = 0 := by
  constructor
  · intro hPrimitive
    apply G.gysin_injective
    calc
      G.middleGysin (G.middleRestriction alpha) =
        G.ampleCup alpha := G.self_intersection alpha
      _ = 0 := hPrimitive
      _ = G.middleGysin 0 := (map_zero G.middleGysin).symm
  · intro hRestricted
    calc
      G.ampleCup alpha =
        G.middleGysin (G.middleRestriction alpha) :=
        (G.self_intersection alpha).symm
      _ = G.middleGysin 0 := by rw [hRestricted]
      _ = 0 := map_zero G.middleGysin

/-- Every rational primitive middle class on every original even
dimensional X is the image of an actual relative BETTI class for
the pair (X,Y). No algebraic source has been selected here. -/
theorem SmoothMiddleHyperplaneBetti.primitive_has_relative_betti_lift
    {p : ℕ}
    (G : SmoothMiddleHyperplaneBetti p X Y HX HY W)
    (alpha : RationalSingularCohomology HX.analytification (2*p))
    (hPrimitive : G.ampleCup alpha = 0) :
    ∃ w : W, G.relativeToX w = alpha := by
  have hr : G.middleRestriction alpha = 0 :=
    (G.primitive_iff_restriction_zero alpha).mp hPrimitive
  exact (G.relative_exact alpha).mp hr

/-- The Hodge-rational subspace is preserved as a PROPERTY of alpha.
The relative lift is topological and its Hodge/algebraic realization
is precisely the next genuinely geometric part of Gate 3. -/
theorem SmoothMiddleHyperplaneBetti.primitive_hodge_relative_lift
    {p : ℕ}
    (G : SmoothMiddleHyperplaneBetti p X Y HX HY W)
    (alpha : RationalSingularCohomology HX.analytification (2*p))
    (hHodge : alpha ∈ rationalHodgeSubspace (HX.hodgeBigrading p))
    (hPrimitive : G.ampleCup alpha = 0) :
    (∃ w : W, G.relativeToX w = alpha) ∧
      alpha ∈ rationalHodgeSubspace (HX.hodgeBigrading p) := by
  exact ⟨G.primitive_has_relative_betti_lift alpha hPrimitive, hHodge⟩

/-- CRITICAL source-filtering theorem: restriction to a single
smooth hyperplane loses EVERY middle-primitive direction.
Any linear procedure using only that restricted class returns
zero, so it cannot reconstruct a nonzero primitive Hodge class. -/
theorem SmoothMiddleHyperplaneBetti.no_recovery_from_restriction
    {p : ℕ}
    (G : SmoothMiddleHyperplaneBetti p X Y HX HY W)
    (alpha : RationalSingularCohomology HX.analytification (2*p))
    (hPrimitive : G.ampleCup alpha = 0)
    (hNonzero : alpha ≠ 0)
    (recover :
      RationalSingularCohomology HY.analytification (2*p) →ₗ[ℚ]
        RationalSingularCohomology HX.analytification (2*p)) :
    recover (G.middleRestriction alpha) ≠ alpha := by
  have hr : G.middleRestriction alpha = 0 :=
    (G.primitive_iff_restriction_zero alpha).mp hPrimitive
  intro hReconstruct
  have hz : (0 :
      RationalSingularCohomology HX.analytification (2*p)) = alpha := by
    calc
      0 = recover 0 := (map_zero recover).symm
      _ = recover (G.middleRestriction alpha) := by rw [hr]
      _ = alpha := hReconstruct
  exact hNonzero hz.symm

#check SmoothMiddleHyperplaneBetti.primitive_iff_restriction_zero
#check SmoothMiddleHyperplaneBetti.primitive_has_relative_betti_lift
#check SmoothMiddleHyperplaneBetti.primitive_hodge_relative_lift
#check SmoothMiddleHyperplaneBetti.no_recovery_from_restriction
#print axioms SmoothMiddleHyperplaneBetti.no_recovery_from_restriction

end GSTUniversalPrimitiveHyperplaneRelative
