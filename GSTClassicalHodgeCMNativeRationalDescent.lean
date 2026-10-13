import GSTClassicalHodgeCMCoefficientDescentCore
import GSTClassicalHodgeExactClayStatement

/-!
# Rational algebraic cycle recovery from arbitrary coefficient extensions

This bridges the general field-extension descent lemma to HC-PROOF's actual
projective codimension cycles and rational singular Betti cohomology.

If a rational Betti class is a FINITE extension-linear combination of genuine
native cycle classes, we construct an actual RATIONAL native algebraic cycle
with exactly that class. No rationality assumption on the extension
coefficients and no finite-degree/Galois hypothesis is necessary.

It directly addresses the coefficient-descent part of the CM surface proof.
The hypothesis requires extension-coordinate identities for given concrete
cycles; it does not assert that arbitrary Hodge classes satisfy them.

NEEDS CI RUN LATER.
-/

set_option maxHeartbeats 35000000
set_option maxRecDepth 900000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeCMCoefficientDescentCore

namespace GSTClassicalHodgeCMNativeRationalDescent

variable {K : Type*} [Field K] [Algebra ℚ K]
variable {J : Type*}
variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {q : Nat}

/-- From an extension-linear representation by native algebraic cycles,
construct a RATIONAL native algebraic cycle representing the same class.
All geometric cycles and their cohomology classes are genuine repository
objects. Only the coefficients are allowed to lie in K. -/
theorem rational_native_cycle_of_extended_span
    (s : Finset J)
    (cycles : J → codimensionCycles V.X q)
    (coefficient : J → K)
    (alpha : RationalSingularCohomology H.analytification (2 * q))
    (hExtended :
      let b := Module.Free.chooseBasis ℚ
        (RationalSingularCohomology H.analytification (2 * q))
      ∀ i : Module.Free.ChooseBasisIndex ℚ
        (RationalSingularCohomology H.analytification (2 * q)),
        algebraMap ℚ K ((b.repr alpha) i) =
          ∑ j ∈ s,
            coefficient j * algebraMap ℚ K
              ((b.repr (H.cycleClass q (cycles j))) i)) :
    ∃ Z : codimensionCycles V.X q,
      H.cycleClass q Z = alpha := by
  let b := Module.Free.chooseBasis ℚ
    (RationalSingularCohomology H.analytification (2 * q))
  obtain ⟨d, hd⟩ :=
    finite_span_descends (K := K)
      (s := s) coefficient
      (fun j i => (b.repr (H.cycleClass q (cycles j))) i)
      (fun i => (b.repr alpha) i) hExtended
  let Z : codimensionCycles V.X q :=
    ∑ j ∈ s, d j • cycles j
  refine ⟨Z, ?_⟩
  apply b.repr.injective
  apply Finsupp.ext
  intro i
  calc
    (b.repr (H.cycleClass q Z)) i =
      ∑ j ∈ s,
        d j * (b.repr (H.cycleClass q (cycles j))) i := by
          simp [Z, map_sum, map_smul, Finset.sum_apply, smul_eq_mul]
    _ = (b.repr alpha) i := (hd i).symm

/-- A successful CM extension-coefficient construction gives membership
in the genuine range of the rational native cycle-class map. -/
theorem native_range_of_extended_span
    (s : Finset J)
    (cycles : J → codimensionCycles V.X q)
    (coefficient : J → K)
    (alpha : RationalSingularCohomology H.analytification (2 * q))
    (hExtended :
      let b := Module.Free.chooseBasis ℚ
        (RationalSingularCohomology H.analytification (2 * q))
      ∀ i : Module.Free.ChooseBasisIndex ℚ
        (RationalSingularCohomology H.analytification (2 * q)),
        algebraMap ℚ K ((b.repr alpha) i) =
          ∑ j ∈ s,
            coefficient j * algebraMap ℚ K
              ((b.repr (H.cycleClass q (cycles j))) i)) :
    alpha ∈ LinearMap.range (H.cycleClass q) := by
  exact rational_native_cycle_of_extended_span s cycles coefficient alpha hExtended

#check rational_native_cycle_of_extended_span
#print axioms rational_native_cycle_of_extended_span

end GSTClassicalHodgeCMNativeRationalDescent
