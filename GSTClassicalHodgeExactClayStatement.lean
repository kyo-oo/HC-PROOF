import GSTClassicalHodgePointNormalForm
import GSTCompactNativeCyclePresentation

/-!
# GST CLASSICAL HODGE — EXACT CLAY-STYLE TARGET

This file pins the actual rational Hodge conjecture as the acceptance target.
Nothing weaker is allowed to masquerade as the final statement.

For a smooth projective complex variety X and codimension p, a rational Hodge
class is a class in H^(2p)(X,Q) whose complexification belongs to H^(p,p).
The conjecture says that every such class is the class of a rational algebraic
codimension-p cycle.

Because `codimensionCycles X p` is already the Q-vector space of native
Mathlib algebraic cycles supported in codimension p, the phrase

  "a rational linear combination of algebraic cycles"

is represented literally by an element of `codimensionCycles X p`.

The last theorem expands the same statement further into a finite rational sum
of genuine codimension-p irreducible point cycles, using projective compactness.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeExactClayStatement

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTCompactNativeCyclePresentation
open GSTClassicalHodgePointNormalForm

variable {V : SmoothProjectiveComplexScheme}
variable (H : HodgeBigradedBettiData V)

/-- Literal elementwise rational Hodge conjecture.
Every rational `(p,p)` class is the cycle class of one rational algebraic
codimension-p cycle. -/
def EveryHodgeClassIsRationalAlgebraic : Prop :=
  ∀ p : Nat,
  ∀ alpha : RationalSingularCohomology H.analytification (2 * p),
    alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p) →
      ∃ Z : codimensionCycles V.X p,
        H.cycleClass p Z = alpha

/-- Fully expanded wording: every rational Hodge class is a FINITE rational
linear combination of classes of genuine codimension-p irreducible algebraic
subvarieties (represented by their generic points). -/
def EveryHodgeClassIsFiniteRationalCombination : Prop :=
  ∀ p : Nat,
  ∀ alpha : RationalSingularCohomology H.analytification (2 * p),
    alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p) →
      ∃ phi : FiniteCodimensionPresentation V.X p,
        phi.sum (fun x q =>
          q • H.cycleClass p (codimensionPointCycle V.X p x)) = alpha

/-- The repo's Stage-2G target is EXACTLY the ordinary elementwise rational
Hodge conjecture. -/
theorem everyHodgeClassIsRationalAlgebraic_iff_stage2G :
    EveryHodgeClassIsRationalAlgebraic H ↔
      BigradedBettiHodgeStatement V H := by
  constructor
  · intro h p alpha halpha
    exact h p alpha halpha
  · intro h p alpha halpha
    exact h p halpha

/-- On a projective carrier, the one-cycle wording and the literal finite
rational-combination wording are equivalent. -/
theorem rationalAlgebraic_iff_finiteRationalCombination :
    EveryHodgeClassIsRationalAlgebraic H ↔
      EveryHodgeClassIsFiniteRationalCombination H := by
  constructor
  · intro h p alpha halpha
    rcases h p alpha halpha with ⟨Z, hZ⟩
    letI : CompactSpace V.X := smoothProjectiveCompactSpace V
    let phi := presentationOfNativeCycle V.X p Z
    refine ⟨phi, ?_⟩
    have hmap :=
      linearMap_realizeFiniteCodimensionPresentation
        V.X p (H.cycleClass p) phi
    have hreal : realizeFiniteCodimensionPresentation V.X p phi = Z := by
      exact realize_presentationOfNativeCycle V.X p Z
    rw [hreal] at hmap
    exact hmap.symm.trans hZ
  · intro h p alpha halpha
    rcases h p alpha halpha with ⟨phi, hphi⟩
    refine ⟨realizeFiniteCodimensionPresentation V.X p phi, ?_⟩
    calc
      H.cycleClass p (realizeFiniteCodimensionPresentation V.X p phi)
          = phi.sum (fun x q =>
              q • H.cycleClass p (codimensionPointCycle V.X p x)) :=
            linearMap_realizeFiniteCodimensionPresentation
              V.X p (H.cycleClass p) phi
      _ = alpha := hphi

/-- **EXACT CLAY-STYLE NORMAL FORM.**
All three formulations coincide:
1. the Stage-2G range inclusion;
2. every rational Hodge class has an algebraic-cycle representative;
3. every rational Hodge class is a finite rational linear combination of
   irreducible codimension-p algebraic cycle classes. -/
theorem exact_rational_hodge_conjecture_normal_form :
    BigradedBettiHodgeStatement V H ↔
      EveryHodgeClassIsRationalAlgebraic H := by
  exact everyHodgeClassIsRationalAlgebraic_iff_stage2G H |>.symm

/-- Same target in the most literal finite-sum wording. -/
theorem exact_rational_hodge_conjecture_finite_sum :
    BigradedBettiHodgeStatement V H ↔
      EveryHodgeClassIsFiniteRationalCombination H := by
  exact
    (exact_rational_hodge_conjecture_normal_form H).trans
      (rationalAlgebraic_iff_finiteRationalCombination H)

#check EveryHodgeClassIsRationalAlgebraic
#check EveryHodgeClassIsFiniteRationalCombination
#check everyHodgeClassIsRationalAlgebraic_iff_stage2G
#check rationalAlgebraic_iff_finiteRationalCombination
#check exact_rational_hodge_conjecture_normal_form
#check exact_rational_hodge_conjecture_finite_sum

#print axioms exact_rational_hodge_conjecture_normal_form
#print axioms exact_rational_hodge_conjecture_finite_sum

end GSTClassicalHodgeExactClayStatement
