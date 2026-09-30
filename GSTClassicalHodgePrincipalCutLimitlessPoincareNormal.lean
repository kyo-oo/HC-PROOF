import GSTClassicalHodgePrincipalCutIncidenceTransposeCosmology
import GSTClassicalHodgeFiniteSupportChart
import GSTWorldRecoordinationGroupoid
import GSTWorldPoincareDuality

/-!
# GST CLASSICAL HODGE — PRINCIPAL-CUT LIMITLESS POINCARE NORMAL

The principal-cut successor row of one genuine codimension-p point is already a
finite-support geometric object.  Its support is therefore one canonical finite
observation window inside the limitless GST cosmos.

This file charts that *actual geometric successor support* into an N x 1 GST
world, without introducing a Hodge basis or an arbitrary finite carrier.  The
Poincare dual of the row is then the canonical transpose probe.  The resulting
top pairing is exactly

    sum_y K(x,y)^2,

which is definitionally the native principal-cut self-energy appearing in the
incidence-transpose normal operator.

Consequently the diagonal coefficient of K^t K is not merely analogous to a
GST Poincare energy: it is literally the finite GST observation of the same
geometric successor row.  Since arbitrary equal-cardinality charts are related
by the world recoordination groupoid, this scalar is coordinate presentation
independent.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open scoped BigOperators

namespace GSTClassicalHodgePrincipalCutLimitlessPoincareNormal

open GSTProjectiveOverC
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgePrincipalCutSuccessorOperator
open GSTClassicalHodgePrincipalCutIncidenceTransposeCosmology
open GSTClassicalHodgeFiniteSupportChart
open GSTWorldRecoordinationGroupoid
open GSTWorldPoincareDuality

/-- The genuinely live codimension-(p+1) successors in the geometric row of x. -/
abbrev LiveSuccessor
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p) :=
  {y : CodimensionPoint V.X (p + 1) //
    y ∈ (successorPresentation V p x).support}

/-- Number of live geometric successor coordinates. -/
def successorSupportSize
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p) : Nat :=
  Fintype.card (LiveSuccessor V p x)

/-- Canonical enumeration of the actual geometric successor support. -/
noncomputable def successorSupportEquivFin
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p) :
    LiveSuccessor V p x ≃ Fin (successorSupportSize V p x) :=
  Fintype.equivFin (LiveSuccessor V p x)

/-- Standard finite GST observation window of the successor row. -/
def successorSupportShape
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p) :
    GSTWorldShape (successorSupportSize V p x) where
  rows := successorSupportSize V p x
  cols := 1
  area_eq := by simp

/-- Identify the live geometric successor addresses with cells of the support
world. -/
noncomputable def liveSuccessorToSupportState
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p) :
    LiveSuccessor V p x ≃ ShapeState (successorSupportShape V p x) :=
  (successorSupportEquivFin V p x).trans
    (shapeCodeEquiv (successorSupportShape V p x)).symm

/-- The actual principal-cut incidence row, written as a rational coefficient
field on its canonical finite GST observation window. -/
def successorSupportWorld
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p) :
    ShapeState (successorSupportShape V p x) → ℚ :=
  fun c =>
    successorPresentation V p x
      (((liveSuccessorToSupportState V p x).symm c).1)

@[simp]
theorem successorSupportWorld_live
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (y : LiveSuccessor V p x) :
    successorSupportWorld V p x
        (liveSuccessorToSupportState V p x y) =
      successorPresentation V p x y.1 := by
  simp [successorSupportWorld]

/-- Rational Poincare-dual copy of one finite coefficient field. -/
def rationalWorldDualPullback
    {A B : Nat}
    (f : WorldCell A B → ℚ) : WorldCell A B → ℚ :=
  fun c => f (worldDual c)

@[simp]
theorem rationalWorldDualPullback_involutive
    {A B : Nat}
    (f : WorldCell A B → ℚ) :
    rationalWorldDualPullback (rationalWorldDualPullback f) = f := by
  funext c
  simp [rationalWorldDualPullback]

/-- For rational coefficients, pairing a world row with its Poincare-dual copy
is exactly the sum of coordinate squares. -/
theorem rationalWorldTopPairing_dualPullback_self
    {A B : Nat}
    (f : WorldCell A B → ℚ) :
    rationalWorldTopPairing f (rationalWorldDualPullback f) =
      ∑ c : WorldCell A B, f c * f c := by
  classical
  unfold rationalWorldTopPairing rationalWorldDualPullback
  simp

/-- Sum of squares in the support chart is exactly the sum over the genuine
live successor addresses. -/
theorem successorSupportWorld_square_sum
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p) :
    (∑ c : ShapeState (successorSupportShape V p x),
      successorSupportWorld V p x c * successorSupportWorld V p x c) =
      ∑ y : LiveSuccessor V p x,
        successorPresentation V p x y.1 *
          successorPresentation V p x y.1 := by
  exact Fintype.sum_equiv
    (liveSuccessorToSupportState V p x).symm
    (fun c => successorSupportWorld V p x c * successorSupportWorld V p x c)
    (fun y => successorPresentation V p x y.1 *
      successorPresentation V p x y.1)
    (fun c => by simp [successorSupportWorld])

/-- The live-support square sum is the native principal-cut self-energy. -/
theorem successorSelfEnergy_eq_liveSupport_square_sum
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p) :
    successorSelfEnergy V p x =
      ∑ y : LiveSuccessor V p x,
        successorPresentation V p x y.1 *
          successorPresentation V p x y.1 := by
  classical
  unfold successorSelfEnergy successorGramCoefficient
  rw [Finsupp.sum]
  rw [← Finset.sum_subtype
    (s := (successorPresentation V p x).support)
    (p := fun y => y ∈ (successorPresentation V p x).support)
    (f := fun y => successorPresentation V p x y *
      successorPresentation V p x y)
    (by intro y; simp)]

/-- **PRINCIPAL-CUT / LIMITLESS POINCARE IDENTIFICATION.**

The exact native normal-return coefficient of one geometric principal-cut row
is literally the finite GST Poincare top pairing of that row against its
Poincare-dual copy. -/
theorem successorSelfEnergy_eq_finiteGSTPoincare
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p) :
    successorSelfEnergy V p x =
      rationalWorldTopPairing
        (successorSupportWorld V p x)
        (rationalWorldDualPullback (successorSupportWorld V p x)) := by
  rw [rationalWorldTopPairing_dualPullback_self]
  rw [successorSupportWorld_square_sum]
  exact successorSelfEnergy_eq_liveSupport_square_sum V p x

/-- Every exact live principal cut therefore produces a nonzero native GST
Poincare energy on its canonical geometric support world. -/
theorem finiteGSTPoincare_ne_zero_of_exact_nonempty
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hExact :
      GSTClassicalHodgeRelativeSuccessorExactStratum.RelativeSuccessorAmbientExact
        V p x)
    (hNonempty : (relativeCodimensionOneFinset V x.1).Nonempty) :
    rationalWorldTopPairing
        (successorSupportWorld V p x)
        (rationalWorldDualPullback (successorSupportWorld V p x)) ≠ 0 := by
  rw [← successorSelfEnergy_eq_finiteGSTPoincare V p x]
  exact successorSelfEnergy_ne_zero_of_exact_nonempty
    V p x hExact hNonempty

#check LiveSuccessor
#check successorSupportShape
#check successorSupportWorld
#check rationalWorldDualPullback
#check successorSelfEnergy_eq_finiteGSTPoincare
#check finiteGSTPoincare_ne_zero_of_exact_nonempty

#print axioms successorSelfEnergy_eq_finiteGSTPoincare
#print axioms finiteGSTPoincare_ne_zero_of_exact_nonempty

end GSTClassicalHodgePrincipalCutLimitlessPoincareNormal
