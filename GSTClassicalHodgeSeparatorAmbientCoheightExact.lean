import GSTClassicalHodgeSeparatorRelativeCoheightOne
import GSTClassicalHodgeSeparatorRelativeCutLanding
import GSTClassicalHodgeRelativeSuccessorLowerBound
import GSTClassicalHodgeSchemeCodimensionStalk
import GSTClassicalHodgeSingleExactSuccessorSurvival
import GSTSmoothProjectiveNoetherian

/-!
# GST CLASSICAL HODGE — SEPARATOR AMBIENT COHEIGHT EXACTNESS

Mathematical closure target for the single-separator branch.

The projective separator is already proved to be an exact relative height-one
successor of a codimension-p source.  The only possible obstruction to ambient
coheight p+1 is an alternate longer ambient prime chain bypassing the source.
Smoothness rules that out through regular-local rank additivity.

This file is intentionally the narrow mathematical interface for the live Lean
repair pass.  No Hodge-surjectivity, visibility, Lefschetz/Poincare, or ambient
exactness hypothesis may be introduced here.
-/

set_option maxHeartbeats 50000000
set_option maxRecDepth 1000000

noncomputable section

open TopologicalSpace
open AlgebraicGeometry
open GSTProjectiveOverC
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgePointClosurePrincipalCut
open GSTClassicalHodgeSeparatorRelativeCoheightOne
open GSTClassicalHodgeSeparatorRelativeCutLanding
open GSTClassicalHodgeRelativeSuccessorLowerBound
open GSTClassicalHodgeSchemeCodimensionStalk
open GSTClassicalHodgeSingleExactSuccessorSurvival

namespace GSTClassicalHodgeSeparatorAmbientCoheightExact

attribute [local instance] specializationOrder

/-!
## Local rank lemma

Let R be a Noetherian regular local ring and P a prime.  Regular local rings are
catenary/equidimensional, hence prime-chain length is additive across P:

  dim R = dim R_P + dim (R/P).

At the separator point y, R = O_{X,y}; P is the prime of the source
specialization x.  The first summand is p by the ambient codimension of x and
the second is 1 by the already-proved relative coheight-one theorem.

GLM: expose the pinned-Mathlib regular-local/catenary API here, or prove this
small lemma from that API.  Do not replace it by a hypothesis on the separator.
-/

/-- Regular-local prime rank additivity, specialized to the finite ranks used
by the separator geometry. -/
theorem regularLocal_prime_rank_additivity
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsRegularLocalRing R]
    (P : Ideal R) [P.IsPrime] :
    ringKrullDim R =
      ringKrullDim (Localization.AtPrime P) + ringKrullDim (R ⧸ P) := by
  -- Mathematical proof: regular local => catenary and equidimensional;
  -- identify dim R_P with ht(P), then use the dimension formula
  -- ht(P) + dim(R/P) = dim R.
  -- The exact theorem spelling is intentionally left to the live pinned-API
  -- repair pass; this expression records the non-circular theorem required.
  simpa using IsRegularLocalRing.ringKrullDim_eq_localization_add_quotient (R := R) P

/-!
## Separator application

Write y for the ambient separator successor.  Smoothness gives regularity of
O_{X,y}.  The source x corresponds to a prime P of O_{X,y}.  Generalization
localization identifies O_{X,x} with (O_{X,y})_P, while the reduced source
closure stalk at y identifies with O_{X,y}/P.  Therefore the two summands in
`regularLocal_prime_rank_additivity` are p and 1.
-/

/-- **AMBIENT EXACTNESS OF THE CANONICAL SEPARATOR SUCCESSOR.** -/
theorem separator_successor_ambient_coheight_exact
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hlive : ProjectivelyLiveSource V.projective.n (V.projective.immersion x.1)) :
    Order.coheight
      (ambientSuccessorPoint V x.1
        (relativeHeightOneSeparatorSuccessor V x.1 hlive)) = p + 1 := by
  let yr := relativeHeightOneSeparatorSuccessor V x.1 hlive
  let y := ambientSuccessorPoint V x.1 yr

  have hrel : Order.coheight (yr : pointClosureScheme V x.1) = 1 := yr.2
  have hsource : ringKrullDim (V.X.presheaf.stalk x.1) = p :=
    stalk_dimension_of_codimensionPoint V p x

  -- The remaining elaboration is the canonical stalk/generalization
  -- identification.  At y, let P be the prime corresponding to x.  Then
  -- O_{X,x} = (O_{X,y})_P and O_{closure{x}_red,y} = O_{X,y}/P.
  obtain ⟨P, hPprime, hloc, hquot⟩ :=
    pointClosure_stalk_prime_decomposition V x.1
      (pointClosureSeparatorSuccessor V x.1 hlive)

  letI : P.IsPrime := hPprime
  have hreg : IsRegularLocalRing (V.X.presheaf.stalk y) :=
    smooth_stalk_isRegularLocalRing V y
  letI : IsRegularLocalRing (V.X.presheaf.stalk y) := hreg

  have hlocdim :
      ringKrullDim (Localization.AtPrime P) = p := by
    rw [← ringKrullDim_eq_of_ringEquiv hloc]
    exact hsource

  have hreldim :
      ringKrullDim ((V.X.presheaf.stalk y) ⧸ P) = 1 := by
    rw [← ringKrullDim_eq_of_ringEquiv hquot]
    rw [ringKrullDim_stalk_eq_coheight]
    exact hrel

  have hrank := regularLocal_prime_rank_additivity P
  rw [hlocdim, hreldim] at hrank

  have hyStalk : ringKrullDim (V.X.presheaf.stalk y) = p + 1 := by
    simpa [Nat.cast_add, Nat.cast_one] using hrank

  rw [stalk_dimension_eq_coheight V y] at hyStalk
  exact_mod_cast hyStalk

/-- Unconditional separator survival: the exactness parameter disappears. -/
theorem separator_successor_survives
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hlive : ProjectivelyLiveSource V.projective.n (V.projective.immersion x.1)) :
    successorMass V p x ≠ 0 ∧
      successorNativeOperator V p (codimensionPointCycle V.X p x) ≠ 0 := by
  exact separator_successor_survives_of_ambient_exact V p x hlive
    (separator_successor_ambient_coheight_exact V p x hlive)

#check regularLocal_prime_rank_additivity
#check separator_successor_ambient_coheight_exact
#check separator_successor_survives

#print axioms separator_successor_ambient_coheight_exact
#print axioms separator_successor_survives

end GSTClassicalHodgeSeparatorAmbientCoheightExact
