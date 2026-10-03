import GSTClassicalHodgeSchemeFiniteCorrespondenceFirewall
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.Topology.LocallyConstant.Basic

/-!
# GST CLASSICAL HODGE — STRICT FINITE-FLAT CORRESPONDENCE DEGREE

The Betti trace lane should not carry an arbitrary degree scalar when the
scheme geometry already knows the finite degree.  Mathlib constructs the rank
`f.finrank : Y -> Nat` of a finite flat morphism, proves it is locally
constant (under local finite presentation), and proves positive rank
everywhere is equivalent to surjectivity.

This file lifts those facts to strict scheme correspondences.  It separates
three levels cleanly:

* scheme-bi-finite: both projections are finite morphisms;
* scheme-bi-finite-flat: both projections additionally have locally constant
  finite rank;
* surjective finite-flat: every local rank is positive and hence gives a
  canonical nonzero rational degree.

No Hodge or Betti transfer is assumed here.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicGeometry

namespace GSTClassicalHodgeStrictCorrespondenceFiniteFlatDegree

open GSTProjectiveOverC
open GSTClassicalHodgeSchemeFiniteCorrespondenceFirewall

variable {V : SmoothProjectiveComplexScheme}

/-- Strict bi-finite correspondence whose two projections are finite flat and
locally of finite presentation, so Mathlib's scheme-theoretic rank is locally
constant on `X`. -/
structure SchemeBiFiniteFlatCorrespondence
    (V : SmoothProjectiveComplexScheme)
    extends SchemeBiFiniteClosedCorrespondence V where
  left_flat : Flat toSchemeFiniteClosedCorrespondence.left
  right_flat : Flat right
  left_lfp : LocallyOfFinitePresentation toSchemeFiniteClosedCorrespondence.left
  right_lfp : LocallyOfFinitePresentation right

namespace SchemeBiFiniteFlatCorrespondence

/-- Canonical local degree/rank of the left finite-flat projection. -/
noncomputable def leftRank
    (K : SchemeBiFiniteFlatCorrespondence V) : V.X → ℕ := by
  letI : Flat K.toSchemeFiniteClosedCorrespondence.left := K.left_flat
  letI : IsFinite K.toSchemeFiniteClosedCorrespondence.left :=
    K.toSchemeFiniteClosedCorrespondence.left_isFinite
  exact K.toSchemeFiniteClosedCorrespondence.left.finrank

/-- Canonical local degree/rank of the right finite-flat projection. -/
noncomputable def rightRank
    (K : SchemeBiFiniteFlatCorrespondence V) : V.X → ℕ := by
  letI : Flat K.right := K.right_flat
  letI : IsFinite K.right := K.right_isFinite
  exact K.right.finrank

/-- The left rank is locally constant on the actual scheme topology. -/
theorem leftRank_isLocallyConstant
    (K : SchemeBiFiniteFlatCorrespondence V) :
    IsLocallyConstant K.leftRank := by
  letI : Flat K.toSchemeFiniteClosedCorrespondence.left := K.left_flat
  letI : IsFinite K.toSchemeFiniteClosedCorrespondence.left :=
    K.toSchemeFiniteClosedCorrespondence.left_isFinite
  letI : LocallyOfFinitePresentation K.toSchemeFiniteClosedCorrespondence.left :=
    K.left_lfp
  simpa [leftRank] using
    Scheme.Hom.isLocallyConstant_finrank K.toSchemeFiniteClosedCorrespondence.left

/-- The right rank is locally constant. -/
theorem rightRank_isLocallyConstant
    (K : SchemeBiFiniteFlatCorrespondence V) :
    IsLocallyConstant K.rightRank := by
  letI : Flat K.right := K.right_flat
  letI : IsFinite K.right := K.right_isFinite
  letI : LocallyOfFinitePresentation K.right := K.right_lfp
  simpa [rightRank] using Scheme.Hom.isLocallyConstant_finrank K.right

/-- Surjectivity of the left projection is equivalent to positive local rank
at every target point. -/
theorem one_le_leftRank_iff_surjective
    (K : SchemeBiFiniteFlatCorrespondence V) :
    1 ≤ K.leftRank ↔ Surjective K.toSchemeFiniteClosedCorrespondence.left := by
  letI : Flat K.toSchemeFiniteClosedCorrespondence.left := K.left_flat
  letI : IsFinite K.toSchemeFiniteClosedCorrespondence.left :=
    K.toSchemeFiniteClosedCorrespondence.left_isFinite
  simpa [leftRank] using
    Scheme.Hom.one_le_finrank_iff_surjective
      K.toSchemeFiniteClosedCorrespondence.left

/-- Surjectivity of the right projection is equivalent to positive local rank
at every target point. -/
theorem one_le_rightRank_iff_surjective
    (K : SchemeBiFiniteFlatCorrespondence V) :
    1 ≤ K.rightRank ↔ Surjective K.right := by
  letI : Flat K.right := K.right_flat
  letI : IsFinite K.right := K.right_isFinite
  simpa [rightRank] using Scheme.Hom.one_le_finrank_iff_surjective K.right

/-- On a preconnected target, left finite-flat degree is globally constant. -/
theorem leftRank_eq
    [PreconnectedSpace V.X]
    (K : SchemeBiFiniteFlatCorrespondence V)
    (x y : V.X) :
    K.leftRank x = K.leftRank y :=
  K.leftRank_isLocallyConstant.apply_eq_of_preconnectedSpace x y

/-- On a preconnected target, right finite-flat degree is globally constant. -/
theorem rightRank_eq
    [PreconnectedSpace V.X]
    (K : SchemeBiFiniteFlatCorrespondence V)
    (x y : V.X) :
    K.rightRank x = K.rightRank y :=
  K.rightRank_isLocallyConstant.apply_eq_of_preconnectedSpace x y

/-- Rational form of the canonical right degree at a chosen target point. -/
noncomputable def rightDegreeQAt
    (K : SchemeBiFiniteFlatCorrespondence V)
    (x : V.X) : ℚ :=
  K.rightRank x

/-- A surjective finite-flat right projection has nonzero canonical rational
degree at every point. -/
theorem rightDegreeQAt_ne_zero_of_surjective
    (K : SchemeBiFiniteFlatCorrespondence V)
    (hsurj : Surjective K.right)
    (x : V.X) :
    K.rightDegreeQAt x ≠ 0 := by
  have hpos : 1 ≤ K.rightRank x :=
    (K.one_le_rightRank_iff_surjective.mpr hsurj) x
  exact_mod_cast (Nat.ne_zero_of_lt hpos)

/-- On a preconnected target the canonical rational degree is independent of
which target point is used to read it. -/
theorem rightDegreeQAt_eq
    [PreconnectedSpace V.X]
    (K : SchemeBiFiniteFlatCorrespondence V)
    (x y : V.X) :
    K.rightDegreeQAt x = K.rightDegreeQAt y := by
  exact_mod_cast K.rightRank_eq x y

end SchemeBiFiniteFlatCorrespondence

/-- Full-degree finite-flat carrier: both strict projections are surjective.
This is the natural scheme-theoretic source of a nonzero finite degree in both
orientations. -/
structure SurjectiveBiFiniteFlatCorrespondence
    (V : SmoothProjectiveComplexScheme)
    extends SchemeBiFiniteFlatCorrespondence V where
  left_surjective : Surjective toSchemeBiFiniteFlatCorrespondence.toSchemeFiniteClosedCorrespondence.left
  right_surjective : Surjective toSchemeBiFiniteFlatCorrespondence.right

namespace SurjectiveBiFiniteFlatCorrespondence

/-- Both local rank functions are everywhere positive. -/
theorem positive_ranks
    (K : SurjectiveBiFiniteFlatCorrespondence V) :
    (1 ≤ K.toSchemeBiFiniteFlatCorrespondence.leftRank) ∧
    (1 ≤ K.toSchemeBiFiniteFlatCorrespondence.rightRank) :=
  ⟨K.toSchemeBiFiniteFlatCorrespondence.one_le_leftRank_iff_surjective.mpr
      K.left_surjective,
    K.toSchemeBiFiniteFlatCorrespondence.one_le_rightRank_iff_surjective.mpr
      K.right_surjective⟩

end SurjectiveBiFiniteFlatCorrespondence

#check SchemeBiFiniteFlatCorrespondence
#check SchemeBiFiniteFlatCorrespondence.leftRank
#check SchemeBiFiniteFlatCorrespondence.rightRank
#check SchemeBiFiniteFlatCorrespondence.leftRank_isLocallyConstant
#check SchemeBiFiniteFlatCorrespondence.rightRank_isLocallyConstant
#check SchemeBiFiniteFlatCorrespondence.one_le_rightRank_iff_surjective
#check SchemeBiFiniteFlatCorrespondence.rightDegreeQAt
#check SurjectiveBiFiniteFlatCorrespondence
#check SurjectiveBiFiniteFlatCorrespondence.positive_ranks

end GSTClassicalHodgeStrictCorrespondenceFiniteFlatDegree
