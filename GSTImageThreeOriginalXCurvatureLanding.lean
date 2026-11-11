import GSTClassicalHodgeCycleOperatorNaturality
import GSTGraphV2NativeCurvatureBirth
import GSTImageThreeCurvatureResonance
import Mathlib

/-!
# GST image-3 — original-X cycle-class operator compiler; geometric witnesses separate

This extension faithfully uses the OWNER'S ORIGINAL geometric
CycleClassOperatorPair and nativeCurvatureCycle semantics, plus its
new original 12-state [J,M] curvature-only source theorem.

The two-parameter ORIGINAL-X cycle F is
  F_(a,b) = U + J + a M + b (J o M - M o J)
on ACTUAL rational native cycles of the SAME ORIGINAL X.
Every operation has an actual cycle operator and its corresponding
canonical rational Betti operator, with an exactly proved commuting
cycle-class square. No basis of unknown rational Hodge classes or
nonexistent Chow inverse is supplied.

This compiler is CONDITIONAL on the independent construction of
TRUE original-X U,J,M pairs. The 12-state native determinant does
not automatically transfer to the target Betti Hodge space.
-/

set_option maxHeartbeats 2500000
noncomputable section

namespace GSTImageThreeOriginalXCurvatureLanding

open GSTClassicalHodgeCycleOperatorNaturality
open GSTGraphV2NativeCurvatureBirth
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- A cycle-class-compatible original-X SOURCE OPERATOR from the CM/source
commutator of GIVEN rational native and Betti endomorphisms.
This record does NOT by itself supply a closed geometric correspondence. -/
def cmSourcePair
    (J M : CycleClassOperatorPair V H p) :
    CycleClassOperatorPair V H p where
  cycleOperator :=
    J.cycleOperator.comp M.cycleOperator -
      M.cycleOperator.comp J.cycleOperator
  cohomologyOperator :=
    J.cohomologyOperator.comp M.cohomologyOperator -
      M.cohomologyOperator.comp J.cohomologyOperator
  cycleClass_natural := by
    apply LinearMap.ext
    intro Z
    simp [LinearMap.comp_apply, map_sub,
      J.cycleClass_cycleOperator, M.cycleClass_cycleOperator]

/-- Original-X version of the new TWO-PARAMETER native GST source,
with exact cycle-class-operator naturality semantics (not a constructed correspondence cycle). -/
def geometricCurvatureF
    (U J M : CycleClassOperatorPair V H p)
    (a b : ℚ) : CycleClassOperatorPair V H p where
  cycleOperator :=
    U.cycleOperator + J.cycleOperator +
      a • M.cycleOperator + b • (cmSourcePair J M).cycleOperator
  cohomologyOperator :=
    U.cohomologyOperator + J.cohomologyOperator +
      a • M.cohomologyOperator +
        b • (cmSourcePair J M).cohomologyOperator
  cycleClass_natural := by
    apply LinearMap.ext
    intro Z
    simp [LinearMap.comp_apply, map_add, map_smul,
      U.cycleClass_cycleOperator, J.cycleClass_cycleOperator,
      M.cycleClass_cycleOperator,
      (cmSourcePair J M).cycleClass_cycleOperator]

/-- The new GST curvature-only F=U+J+[J,M] has an original-X
cycle-class-compatible operator realization once U,J,M pairs are supplied.
A separate finite closed correspondence witness is not implied. -/
def geometricCurvatureOnlyF
    (U J M : CycleClassOperatorPair V H p) :
    CycleClassOperatorPair V H p :=
  geometricCurvatureF U J M 0 1

/-- The actual original-X rational Betti class of the new
CM/source curvature is the Betti commutator, never a formal
synthetic vector or unverified class inverse. -/
theorem cmSourcePair_canonicalClass
    (J M : CycleClassOperatorPair V H p)
    (Z : codimensionCycles V.X p) :
    H.cycleClass p ((cmSourcePair J M).cycleOperator Z) =
      J.cohomologyOperator (M.cohomologyOperator (H.cycleClass p Z)) -
        M.cohomologyOperator (J.cohomologyOperator (H.cycleClass p Z)) := by
  simpa [cmSourcePair] using
    (nativeCurvature_cycleClass J M Z)

/-- Entire original-X two-parameter F satisfies the canonical
geometric cycle-class square. -/
theorem geometricCurvatureF_canonicalClass
    (U J M : CycleClassOperatorPair V H p)
    (a b : ℚ) (Z : codimensionCycles V.X p) :
    H.cycleClass p ((geometricCurvatureF U J M a b).cycleOperator Z) =
      (geometricCurvatureF U J M a b).cohomologyOperator
        (H.cycleClass p Z) :=
  (geometricCurvatureF U J M a b).cycleClass_cycleOperator Z

/-- Exact cycle-class naturality, CONDITIONAL on the given native U/J/M
operator pairs; neither a new Chow correspondence nor a Hodge class basis
is manufactured by this equality. -/
theorem geometricCurvatureOnlyF_canonicalClass
    (U J M : CycleClassOperatorPair V H p)
    (Z : codimensionCycles V.X p) :
    H.cycleClass p ((geometricCurvatureOnlyF U J M).cycleOperator Z) =
      (geometricCurvatureOnlyF U J M).cohomologyOperator
        (H.cycleClass p Z) :=
  (geometricCurvatureOnlyF U J M).cycleClass_cycleOperator Z

/-! ## SOURCE-IMAGE SATURATION FIREWALL

A genuine cycle-class square preserves the EXISTING algebraic cycle-class
image, including under all original CM curvature commutators. This blocks
the incorrect promotion of a 12-state native rank calculation into a new
original-X algebraic Hodge direction.
-/

/-- The CM commutator preserves the full actual algebraic cycle-class range
for every supplied original-X naturality pair J,M. -/
theorem cmSourcePair_preserves_algebraic_range
    (J M : CycleClassOperatorPair V H p) :
    ∀ alpha,
      alpha ∈ LinearMap.range (H.cycleClass p) →
      (cmSourcePair J M).cohomologyOperator alpha ∈
        LinearMap.range (H.cycleClass p) :=
  (cmSourcePair J M).cycleClass_range_stable

/-- The ENTIRE two-parameter F family preserves the same full algebraic
image, for every rational direct strength a and curvature strength b.
It may enlarge an earlier finite algebraic frame, but cannot escape the
full current algebraic cycle-class range by operator iteration alone. -/
theorem geometricCurvatureF_preserves_algebraic_range
    (U J M : CycleClassOperatorPair V H p) (a b : ℚ) :
    ∀ alpha,
      alpha ∈ LinearMap.range (H.cycleClass p) →
      (geometricCurvatureF U J M a b).cohomologyOperator alpha ∈
        LinearMap.range (H.cycleClass p) :=
  (geometricCurvatureF U J M a b).cycleClass_range_stable

#check cmSourcePair_preserves_algebraic_range
#check geometricCurvatureF_preserves_algebraic_range
#print axioms geometricCurvatureF_preserves_algebraic_range

#check cmSourcePair
#check geometricCurvatureF
#check geometricCurvatureOnlyF
#check cmSourcePair_canonicalClass
#check geometricCurvatureF_canonicalClass
#check geometricCurvatureOnlyF_canonicalClass

#print axioms cmSourcePair_canonicalClass
#print axioms geometricCurvatureOnlyF_canonicalClass

end GSTImageThreeOriginalXCurvatureLanding
