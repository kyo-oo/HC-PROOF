import GSTCMQuadraticNativeRankForcing
import GSTClassicalHodgeCrossCarrierGeometricTransfer

/-!
# Universal Hodge: CM–NM obstruction and source–target geometry audit

This file is an adversarial check against a false unconditional completion.
It does NOT add any axiom, arbitrary cycle witness, or artificial Hodge action.

1. The imaginary-quadratic CM operator polynomial
     T² - 2aT + (a²+b²)I = 0, b != 0
   CANNOT hold on the rational one-dimensional vector space Q.
   Thus the earlier rank-two CM forcing cannot serve as a single
   UNIVERSAL operator law, notably for a rank-one Hodge fiber.
   This does not refute CM arithmetic on even-dimensional factors.
2. Any actual realized algebraic cross-carrier correspondence sends
   a class of an actual algebraic source cycle to the actual algebraic
   cycle-class range of its destination. If beta is NOT algebraic,
   it is impossible for beta to be obtained by any such transfer of
   an algebraic source cycle. More compositions of old transfers
   do not independently create algebraicity of arbitrary beta.

A path to an unconditional Hodge proof must supply a NEW actual
geometric construction for the arbitrary missing target class
(or establish a genuinely universal geometric mechanism beyond
transfer closure). Giving names to conditional CM/NM transfers
does not discharge this implication.
-/

set_option maxHeartbeats 20000000
noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTCMQuadraticNativeRankForcing
open GSTClassicalHodgeCrossCarrierGeometricTransfer

namespace GSTUniversalCMArithmeticObstruction

/-- A universal imaginary-quadratic CM law is already impossible on
the smallest nonzero rational Hodge carrier: a one-dimensional
Q-module. This uses the already verified CM rational-eigenline
contradiction, not an invented linear-algebra assumption. -/
theorem no_imaginary_quadratic_CM_on_rational_line
    (T : Module.End ℚ ℚ) (a b : ℚ) (hb : b ≠ 0)
    (hMin : ∀ z : ℚ,
      T (T z) - (2*a) • T z + (a^2+b^2) • z = 0) : False := by
  have hEigen : T (1:ℚ) = (T (1:ℚ)) • (1:ℚ) := by
    simp
  exact imaginary_quadratic_CM_no_rational_eigenline
    (W := ℚ) T a b hb hMin (1:ℚ) (by norm_num)
    (T (1:ℚ)) hEigen

variable {V W : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {J : HodgeBigradedBettiData W}
variable {p q : Nat}

/-- The geometric transfer law cannot output a nonalgebraic
cohomological target from an algebraic source. This has no
generic-surjectivity assumptions and applies to every genuine
cross-carrier transfer. -/
theorem no_algebraic_source_transfer_hits_non_algebraic_target
    (R : CrossCarrierTransfer V W H J p q)
    (target : RationalSingularCohomology J.analytification (2*q))
    (hnot : target ∉ LinearMap.range (J.cycleClass q)) :
    ¬ ∃ Z : codimensionCycles V.X p,
      R.betti (H.cycleClass p Z) = target := by
  rintro ⟨Z,hZ⟩
  apply hnot
  rw [← hZ]
  exact R.native_range_preserved Z

/-- The obstruction survives two consecutive genuine
cross-carrier transfers, even with different carriers/codimensions.
This prevents a formal CM -> auxiliary -> arbitrary-target
program from being mislabeled as a universal Hodge proof
without an independently proved source-to-target spanning law. -/
theorem no_composed_algebraic_transfer_hits_non_algebraic_target
    {U : SmoothProjectiveComplexScheme}
    {K : HodgeBigradedBettiData U}
    {r : Nat}
    (R : CrossCarrierTransfer V W H J p q)
    (S : CrossCarrierTransfer W U J K q r)
    (target : RationalSingularCohomology K.analytification (2*r))
    (hnot : target ∉ LinearMap.range (K.cycleClass r)) :
    ¬ ∃ Z : codimensionCycles V.X p,
      S.betti (R.betti (H.cycleClass p Z)) = target := by
  rintro ⟨Z,hZ⟩
  have hR : J.cycleClass q (R.native Z) =
      R.betti (H.cycleClass p Z) := R.naturality Z
  have hS : K.cycleClass r (S.native (R.native Z)) =
      S.betti (R.betti (H.cycleClass p Z)) := by
    rw [S.naturality,R.naturality]
  exact hnot ⟨S.native (R.native Z), hS.trans hZ⟩


/-! ## Generalized GST CM/NM multi-charge geometry: first new atom

The verified quadratic CM factorization handles a ONE-DIMENSIONAL
norm-one torus: characters come in opposite positive and negative weights.
Arbitrary Hodge varieties can carry HIGHER-RANK CM character
lattices, where an invariant degree-three atom may have NO
invariant quadratic subword.

The following exact new GST countermodel is a rank-two torus
whose three character weights are (1,0), (0,1), (-1,-1).
Their total charge is zero, but NONE of the three possible
quadratic pairings has charge zero (including repeated indices).
The proposed universal step "all CM invariants arise from
quadratic pairs" is therefore FALSE beyond the norm-one torus.

This does not refute algebraicity of that cubic Hodge character.
It isolates precisely the new type of geometry needed: genuine
algebraic realizations of higher-degree primitive CM invariants.
That is a construction obligation, not an assumed Chow preimage.
-/

/-- Two independent rational/integral CM-charge channels and
three primitive weights, in the GST CM/NM charge lattice. -/
def cubicCMWeight (i : Fin 3) (j : Fin 2) : ℤ :=
  if i = 0 then (if j = 0 then 1 else 0)
  else if i = 1 then (if j = 0 then 0 else 1)
  else -1

/-- Exact triadic GST CM invariant: all two charge channels cancel.
The result is a genuine degree-three weight-zero ATOM. -/
theorem cubic_CM_charge_invariant :
    ∀ j : Fin 2,
      cubicCMWeight 0 j + cubicCMWeight 1 j +
        cubicCMWeight 2 j = 0 := by
  intro j
  fin_cases j <;> norm_num [cubicCMWeight]

/-- There are NO opposite quadratic generators in this new
two-charge universe. Thus no path using only the OLD quadratic
norm-one pairing mechanism can generate the triadic invariant. -/
theorem no_quadratic_CM_invariant_in_three_weights :
    ∀ i k : Fin 3,
      ¬ (∀ j : Fin 2,
        cubicCMWeight i j + cubicCMWeight k j = 0) := by
  decide

/-- The next GST-CM primitive-generator law MUST contain cubic
or higher charge-balancing patterns: a degree-three invariant
cannot be assembled from zero-weight quadratic factors. -/
theorem cubic_CM_atom_requires_new_generator :
    (∀ j : Fin 2,
      cubicCMWeight 0 j + cubicCMWeight 1 j +
        cubicCMWeight 2 j = 0) ∧
    (∀ i k : Fin 3,
      ¬ (∀ j : Fin 2,
        cubicCMWeight i j + cubicCMWeight k j = 0)) :=
  ⟨cubic_CM_charge_invariant,
    no_quadratic_CM_invariant_in_three_weights⟩

#check cubic_CM_atom_requires_new_generator
#print axioms cubic_CM_atom_requires_new_generator

#check no_imaginary_quadratic_CM_on_rational_line
#check no_algebraic_source_transfer_hits_non_algebraic_target
#check no_composed_algebraic_transfer_hits_non_algebraic_target

#print axioms no_imaginary_quadratic_CM_on_rational_line
#print axioms no_algebraic_source_transfer_hits_non_algebraic_target
#print axioms no_composed_algebraic_transfer_hits_non_algebraic_target

end GSTUniversalCMArithmeticObstruction
