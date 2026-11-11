import GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra
import GSTImageThreeOriginalXNativeLanding
import Mathlib

/-!
# GST Image 3 — SOURCE F is a TRUE finite rational word of CLOSED
# correspondences, not only an arbitrary cycle-class operator pair

The user's original step 01 is a genuine rational algebraic
correspondence on the ORIGINAL X x X with canonical Betti naturality.
An arbitrary CycleClassOperatorPair is insufficient to certify a
geometric closed correspondence. This upgrade begins with three
actually-realized closed correspondences U,J,M, constructs their
navigation-dependent finite RATIONAL CORRESPONDENCE WORD, and proves
that its ACTUAL native/Betti action is precisely the previously
formalized Image-3 F.

Each geometric generator remains an INPUT: this is not the missing
universal theorem asserting the ORIGINAL information-space U,J,M
exist on EVERY smooth projective X. It closes the semantic gap
between typed pairs and genuine closed-correspondence words.
-/

set_option maxHeartbeats 5000000
noncomputable section

namespace GSTImageThreeRealizedWordGeometry

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeCycleOperatorNaturality
open GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra
open GSTImageThreeOriginalXNativeLanding
open GSTPerfectPowerTailNavigation

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- The physical-navigation-controlled F is a REAL finite rational
algebraic correspondence WORD on the original X: three actual
geometrically realized closed correspondence atoms. -/
def originalXNativeFWord
    (U J M : RealizedFiniteClosedCorrespondence V H p)
    (R : Nat) : RealizedCorrespondenceWord V H p :=
  [(1, U), (1, J), (navigationCharge R, M)]

/-- The native rational CHOW action of the actual geometric F word
equals exactly the previously constructed original-X F-operator. -/
theorem originalXNativeFWord_cycle
    (U J M : RealizedFiniteClosedCorrespondence V H p)
    (R : Nat) :
    (realizedWordPair (originalXNativeFWord U J M R)).cycleOperator =
      (geometricF U.operatorPair J.operatorPair M.operatorPair R).cycleOperator := by
  ext z
  simp [originalXNativeFWord, realizedWordPair,
    CycleClassOperatorPair.add, CycleClassOperatorPair.smul,
    CycleClassOperatorPair.zero, geometricF,
    LinearMap.add_apply, LinearMap.smul_apply] <;> abel_nf

/-- The corresponding REAL Betti action is the SAME Image-3 F
expression, not a hand-selected unrelated cohomology endomorphism. -/
theorem originalXNativeFWord_betti
    (U J M : RealizedFiniteClosedCorrespondence V H p)
    (R : Nat) :
    (realizedWordPair (originalXNativeFWord U J M R)).cohomologyOperator =
      (geometricF U.operatorPair J.operatorPair M.operatorPair R).cohomologyOperator := by
  ext alpha
  simp [originalXNativeFWord, realizedWordPair,
    CycleClassOperatorPair.add, CycleClassOperatorPair.smul,
    CycleClassOperatorPair.zero, geometricF,
    LinearMap.add_apply, LinearMap.smul_apply] <;> abel_nf

/-- ACTUAL canonical Chow/Betti naturality for the finite rational
original-X realized word, now anchored in TRUE geometry. -/
theorem originalXNativeFWord_class
    (U J M : RealizedFiniteClosedCorrespondence V H p)
    (R : Nat) (z : codimensionCycles V.X p) :
    H.cycleClass p
      ((realizedWordPair (originalXNativeFWord U J M R)).cycleOperator z) =
      (realizedWordPair (originalXNativeFWord U J M R)).cohomologyOperator
        (H.cycleClass p z) := by
  exact (realizedWordPair (originalXNativeFWord U J M R)).cycleClass_cycleOperator z

/-- The owner's navigation-cut equivalence persists for the entire
TRUE original-X finite correspondence word at the level of both
native and Betti operators. -/
theorem originalXNativeFWord_navigation
    (U J M : RealizedFiniteClosedCorrespondence V H p)
    (s b : Nat) (hs : 1 ≤ s) :
    originalXNativeFWord U J M (4^(3^s*b)) =
      originalXNativeFWord U J M (canonicalTail s b) := by
  simp only [originalXNativeFWord,
    navigationCharge_canonicalTail s b hs]

/-- No rationally weighted genuine correspondence word can pull
previously nonalgebraic Hodge directions out of nowhere: the
TRUE original-X algebraic cycle-class range is invariant. -/
theorem originalXNativeFWord_algebraic_range_stable
    (U J M : RealizedFiniteClosedCorrespondence V H p)
    (R : Nat) :
    ∀ alpha,
      alpha ∈ LinearMap.range (H.cycleClass p) →
      (realizedWordPair (originalXNativeFWord U J M R)).cohomologyOperator alpha
        ∈ LinearMap.range (H.cycleClass p) :=
  realizedWord_range_stable (originalXNativeFWord U J M R)

#check originalXNativeFWord
#check originalXNativeFWord_cycle
#check originalXNativeFWord_betti
#check originalXNativeFWord_class
#check originalXNativeFWord_navigation
#print axioms originalXNativeFWord_cycle
#print axioms originalXNativeFWord_betti
#print axioms originalXNativeFWord_class

end GSTImageThreeRealizedWordGeometry
