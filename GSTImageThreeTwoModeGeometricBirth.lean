import GSTImageThreeRealizedWordGeometry
import GSTGraphV2NativeCurvatureBirth
import Mathlib

/-!
# GST Image 3 — EXACT two-step / three-step native curvature birth test
# on the canonical rational Betti space of the ORIGINAL X

The owner's original U/J/SURVIVE 12-cell information model has EXACT
two missing source-free directions detected by d1,d2 at fold depths
2 and 3 with matrix [[-2,-8],[0,2]], determinant -4.

This file formulates the corresponding NECESSARY genuine original-X
source-birth certificate. It proves the 2-dimensional expansion
CONDITIONALLY on actual original-X Chow cycles, the true canonical
Betti map and genuine detectors on the actual original-X cohomology.

It also proves a crucial geometric firebreak: the detectors MUST NOT
be declared zero on the whole algebraic cycle-class range, since
then no real native Chow orbit can produce their nonzero readings.
"Old known source span" and "all algebraic cycles" are DIFFERENT.

There is no fabricated original-X universal detector, no assumed
Hodge-class preimage and no unqualified Hodge conjecture conclusion.
-/

set_option maxHeartbeats 5000000
noncomputable section

namespace GSTImageThreeTwoModeGeometricBirth

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeCycleOperatorNaturality

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Exact TRUE original-X codimension-p native cycle born at GST
fold depth 2 from ONE actual original seed cycle and actual operator. -/
def bornSecond (F : CycleClassOperatorPair V H p)
    (z : codimensionCycles V.X p) :
    codimensionCycles V.X p :=
  F.cycleOperator (F.cycleOperator z)

/-- The next TRUE original-X born cycle at GST fold depth 3. -/
def bornThird (F : CycleClassOperatorPair V H p)
    (z : codimensionCycles V.X p) :
    codimensionCycles V.X p :=
  F.cycleOperator (bornSecond F z)

/-- The original-X cycle-class square holds after TWO actual F
operations, with no unproved Hodge algebraicity. -/
theorem bornSecond_cycleClass
    (F : CycleClassOperatorPair V H p)
    (z : codimensionCycles V.X p) :
    H.cycleClass p (bornSecond F z) =
      F.cohomologyOperator (F.cohomologyOperator (H.cycleClass p z)) := by
  simp only [bornSecond, F.cycleClass_cycleOperator]

/-- The true canonical original-X class of the THREE-FOLD
algebraic source birth agrees exactly with the Betti cube. -/
theorem bornThird_cycleClass
    (F : CycleClassOperatorPair V H p)
    (z : codimensionCycles V.X p) :
    H.cycleClass p (bornThird F z) =
      F.cohomologyOperator
        (F.cohomologyOperator
          (F.cohomologyOperator (H.cycleClass p z))) := by
  simp only [bornThird, bornSecond, F.cycleClass_cycleOperator]

/-- A GEOMETRIC instance of the owner's exact original-wave dual
probe, now strictly on the original X's canonical Betti cohomology.

The "old" space must be ONLY previously known native sources:
the detector cannot annihilate the ENTIRE algebraic class range. -/
theorem two_actual_born_directions_independent_mod_known
    (F : CycleClassOperatorPair V H p)
    (z : codimensionCycles V.X p)
    (old : Submodule ℚ
      (RationalSingularCohomology H.analytification (2 * p)))
    (d1 d2 : RationalSingularCohomology H.analytification (2 * p)
       →ₗ[ℚ] ℚ)
    (hOld1 : ∀ a ∈ old, d1 a = 0)
    (hOld2 : ∀ a ∈ old, d2 a = 0)
    (h12 : d1 (H.cycleClass p (bornSecond F z)) = -2)
    (h22 : d2 (H.cycleClass p (bornSecond F z)) = 0)
    (h13 : d1 (H.cycleClass p (bornThird F z)) = -8)
    (h23 : d2 (H.cycleClass p (bornThird F z)) = 2)
    (a b : ℚ)
    (hmem :
      a • H.cycleClass p (bornSecond F z) +
      b • H.cycleClass p (bornThird F z) ∈ old) :
    a = 0 ∧ b = 0 := by
  have ha := hOld1 _ hmem
  have hb := hOld2 _ hmem
  have h1 : a * (-2) + b * (-8) = 0 := by
    simpa only [map_add, map_smul, smul_eq_mul, h12, h13] using ha
  have h2 : a * 0 + b * 2 = 0 := by
    simpa only [map_add, map_smul, smul_eq_mul, h22, h23] using hb
  constructor <;> linarith

/-- Fundamental geometry distinction: a detector annihilating ALL
actual algebraic cycle classes MUST annihilate every true F-born
source. Nonzero native-wave probe measurements cannot be transferred
to the actual original X by simply assuming such a detector. -/
theorem no_actual_cycle_born_outside_total_algebraic_range
    (d : RationalSingularCohomology H.analytification (2 * p)
       →ₗ[ℚ] ℚ)
    (hAll : ∀ alpha ∈ LinearMap.range (H.cycleClass p), d alpha = 0)
    (F : CycleClassOperatorPair V H p)
    (z : codimensionCycles V.X p) :
    d (H.cycleClass p (bornThird F z)) = 0 := by
  apply hAll
  exact ⟨bornThird F z, rfl⟩

#check bornSecond
#check bornThird
#check bornSecond_cycleClass
#check bornThird_cycleClass
#check two_actual_born_directions_independent_mod_known
#check no_actual_cycle_born_outside_total_algebraic_range
#print axioms bornSecond_cycleClass
#print axioms bornThird_cycleClass
#print axioms two_actual_born_directions_independent_mod_known
#print axioms no_actual_cycle_born_outside_total_algebraic_range

end GSTImageThreeTwoModeGeometricBirth
