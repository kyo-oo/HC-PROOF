import GSTImageThreePureCMOriginalXLanding
import GSTImageThreeGeometricTwoSourceBirth

/-!
# GST Image 3 — ACTUAL original-X TWO born CM-curvature sources
# from ONE genuine Chow seed, at the FIRST curvature layer.

At the author's ORIGINAL U+J 12-cell native signal level, the exact
true CM curvature K=[J,M] applied to v and to (U+J)v yields detector
matrix [[2,1],[0,2]], determinant 4, mod the old 10-dimensional
source-free orbit. Wolfram script:
  research/computations/GST_image3_pureCM_two_direction_first_birth_20261111.wl.

This file transfers the EXACT source-generation recipe to the
CANONICAL native original-X Chow arena:
  Z_K0 := [N_J,N_M] Z0
  Z_K1 := [N_J,N_M] (N_U+N_J) Z0.
Both are genuine Chow cycles from ONE GIVEN actual Chow seed Z0,
not preselected unknown Hodge-class cycle preimages.

If TWO actual geometric rational detectors annihilate the old
known source sector and have the SAME nonzero 2x2 readout matrix
on these ACTUAL generated cycles, then both classes are
independent mod the old sector. The Hodge-rank growth is thereby
proved *under these explicit geometric detector premises*.

This does NOT assert that the original symbolic detectors automatically
exist on every X or that there is an original-X geometric U/J/M
representation in every Hodge degree; those are exactly the
remaining universal Hodge-hypothesis obligations.
-/

set_option maxHeartbeats 4000000
noncomputable section

namespace GSTImageThreePureCMGeometricBornDirections

open GSTImageThreePureCMOriginalXLanding
open GSTImageThreeGeometricTwoSourceBirth
open GSTClassicalHodgeCycleOperatorNaturality
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- A NEW actual original-X Chow cycle from the TRUE derived CM
curvature on ONE original native seed. -/
def firstNativeCMSource
    (J M : CycleClassOperatorPair V H p)
    (Z₀ : codimensionCycles V.X p) :
    codimensionCycles V.X p :=
  (pureCMSourcePair J M).cycleOperator Z₀

/-- The SECOND actual original-X Chow cycle from the same seed:
apply original source-free U+J ONCE, then original true CM curvature. -/
def secondNativeCMSource
    (U J M : CycleClassOperatorPair V H p)
    (Z₀ : codimensionCycles V.X p) :
    codimensionCycles V.X p :=
  (pureCMSourcePair J M).cycleOperator
    (U.cycleOperator Z₀ + J.cycleOperator Z₀)

/-- The genuine original-X canonical Betti class of the FIRST
derived curvature source. -/
theorem firstNativeCMSource_class
    (J M : CycleClassOperatorPair V H p)
    (Z₀ : codimensionCycles V.X p) :
    H.cycleClass p (firstNativeCMSource J M Z₀) =
      (pureCMSourcePair J M).cohomologyOperator
        (H.cycleClass p Z₀) :=
  (pureCMSourcePair J M).cycleClass_cycleOperator Z₀

/-- The genuine original-X canonical Betti class of the SECOND
derived curvature source, built from the same single seed. -/
theorem secondNativeCMSource_class
    (U J M : CycleClassOperatorPair V H p)
    (Z₀ : codimensionCycles V.X p) :
    H.cycleClass p (secondNativeCMSource U J M Z₀) =
      (pureCMSourcePair J M).cohomologyOperator
        (U.cohomologyOperator (H.cycleClass p Z₀) +
          J.cohomologyOperator (H.cycleClass p Z₀)) := by
  rw [secondNativeCMSource,
    (pureCMSourcePair J M).cycleClass_cycleOperator,
    map_add, U.cycleClass_cycleOperator,
    J.cycleClass_cycleOperator]

/-- THE ORIGINAL-X FIRST-CURVATURE TWO-DIRECTION RANK-BIRTH GATE.

The only new premises beyond genuine U,J,M geometry and one true
native seed are the exact geometric readout values (2,0,1,2)
of the SOURCE-GENERATED ACTUAL cycles. These are NOT assumed to
hold automatically from the abstract native 12-cell wave computation.

Once actual geometric detectors with these readings are supplied,
the theorem proves BOTH born classes are independent MODULO the
older original-X source subspace. No previously unknown Hodge class
is postulated algebraic. -/
theorem first_layer_two_true_CM_sources_independent
    (U J M : CycleClassOperatorPair V H p)
    (Z₀ : codimensionCycles V.X p)
    (old : Submodule ℚ
      (RationalSingularCohomology H.analytification (2 * p)))
    (d₁ d₂ : RationalSingularCohomology H.analytification (2 * p)
      →ₗ[ℚ] ℚ)
    (hOld₁ : ∀ z ∈ old, d₁ z = 0)
    (hOld₂ : ∀ z ∈ old, d₂ z = 0)
    (h₁₁ :
      d₁ (H.cycleClass p (firstNativeCMSource J M Z₀)) = 2)
    (h₂₁ :
      d₂ (H.cycleClass p (firstNativeCMSource J M Z₀)) = 0)
    (h₁₂ :
      d₁ (H.cycleClass p (secondNativeCMSource U J M Z₀)) = 1)
    (h₂₂ :
      d₂ (H.cycleClass p (secondNativeCMSource U J M Z₀)) = 2)
    (a b : ℚ)
    (hOld :
      H.cycleClass p
        (a • firstNativeCMSource J M Z₀ +
         b • secondNativeCMSource U J M Z₀) ∈ old) :
    a = 0 ∧ b = 0 := by
  have hMinor :
      d₁ (H.cycleClass p (firstNativeCMSource J M Z₀)) *
        d₂ (H.cycleClass p (secondNativeCMSource U J M Z₀)) -
      d₁ (H.cycleClass p (secondNativeCMSource U J M Z₀)) *
        d₂ (H.cycleClass p (firstNativeCMSource J M Z₀)) ≠ 0 := by
    rw [h₁₁, h₂₂, h₁₂, h₂₁]
    norm_num
  exact originalX_two_native_source_directions_independent
    old d₁ d₂
    (firstNativeCMSource J M Z₀)
    (secondNativeCMSource U J M Z₀)
    hOld₁ hOld₂ hMinor a b hOld

#check firstNativeCMSource
#check secondNativeCMSource
#check firstNativeCMSource_class
#check secondNativeCMSource_class
#check first_layer_two_true_CM_sources_independent

#print axioms secondNativeCMSource_class
#print axioms first_layer_two_true_CM_sources_independent

end GSTImageThreePureCMGeometricBornDirections
