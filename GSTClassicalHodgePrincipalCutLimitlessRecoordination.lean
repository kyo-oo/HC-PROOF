import GSTClassicalHodgePrincipalCutLimitlessPoincareNormal

/-!
# GST CLASSICAL HODGE — LIMITLESS RECOORDINATION OF THE PRINCIPAL-CUT NORMAL

The principal-cut successor row has already been identified with one finite GST
Poincare energy.  Its initial N x 1 support chart is only a presentation.

This module removes even that choice.  Any equal-cardinality GST chart receives
the row by the exact world-recoordination groupoid, and its Poincare self-energy
is unchanged.  Thus the geometric normal coefficient can be evaluated after
reshaping the entire live successor neighborhood into whichever finite shadow
of the limitless cosmos is most convenient for a causal, dual, or spectral
argument.

The proof does not ask Poincare complement itself to commute with arbitrary
chart changes.  Instead it uses the stronger invariant description

    <f, D^* f>_top = sum_c f(c)^2,

and the sum of squares is preserved by every coordinate equivalence.  This is
exactly the correct chart-free Gram invariant.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open scoped BigOperators

namespace GSTClassicalHodgePrincipalCutLimitlessRecoordination

open GSTProjectiveOverC
open GSTNativeCodimensionCyclePresentation
open GSTWorldRecoordinationGroupoid
open GSTClassicalHodgeFiniteSupportChart
open GSTClassicalHodgePrincipalCutLimitlessPoincareNormal

/-- Rational coefficient transport along an arbitrary equal-cardinality GST
world recoordination. -/
def rationalTransportCoef
    {N : Nat}
    (S T : GSTWorldShape N)
    (f : ShapeState S → ℚ) : ShapeState T → ℚ :=
  fun y => f ((worldRecoordinate S T).symm y)

@[simp]
theorem rationalTransportCoef_self
    {N : Nat}
    (S : GSTWorldShape N)
    (f : ShapeState S → ℚ) :
    rationalTransportCoef S S f = f := by
  funext x
  simp [rationalTransportCoef, worldRecoordinate]

/-- Rational coefficient transport is functorial across arbitrary intermediate
world shapes. -/
theorem rationalTransportCoef_comp
    {N : Nat}
    (S T U : GSTWorldShape N)
    (f : ShapeState S → ℚ) :
    rationalTransportCoef T U (rationalTransportCoef S T f) =
      rationalTransportCoef S U f := by
  funext z
  simp [rationalTransportCoef, worldRecoordinate]

/-- Sum of coordinate squares is invariant under every GST world
recoordination. -/
theorem rational_square_energy_recoordinate
    {N : Nat}
    (S T : GSTWorldShape N)
    (f : ShapeState S → ℚ) :
    (∑ y : ShapeState T,
      rationalTransportCoef S T f y * rationalTransportCoef S T f y) =
      ∑ x : ShapeState S, f x * f x := by
  classical
  exact Fintype.sum_equiv
    (worldRecoordinate S T).symm
    (fun y => rationalTransportCoef S T f y *
      rationalTransportCoef S T f y)
    (fun x => f x * f x)
    (fun y => by simp [rationalTransportCoef])

/-- **POINCARE ENERGY IS A RECOORDINATION INVARIANT.**
Although the complement map is chart-dependent, pairing a row with its own
Poincare-dual copy gives the chart-free Gram energy, hence survives every
world recoordination exactly. -/
theorem rational_poincare_energy_recoordinate
    {N : Nat}
    (S T : GSTWorldShape N)
    (f : ShapeState S → ℚ) :
    rationalWorldTopPairing
        (rationalTransportCoef S T f)
        (rationalWorldDualPullback (rationalTransportCoef S T f)) =
      rationalWorldTopPairing f (rationalWorldDualPullback f) := by
  rw [rationalWorldTopPairing_dualPullback_self]
  rw [rationalWorldTopPairing_dualPullback_self]
  exact rational_square_energy_recoordinate S T f

/-- Rechart the actual principal-cut successor row into an arbitrary
same-cardinality GST world. -/
def recoordinatedSuccessorWorld
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (T : GSTWorldShape
      (successorSupportSize V p x)) :
    ShapeState T → ℚ :=
  rationalTransportCoef (successorSupportShape V p x) T
    (successorSupportWorld V p x)

/-- **LIMITLESS SHAPE-FREE PRINCIPAL-CUT NORMAL.**
The native principal-cut self-energy is the Poincare energy in *every* finite
GST chart of the live geometric successor support. -/
theorem successorSelfEnergy_eq_recoordinatedGSTPoincare
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (T : GSTWorldShape (successorSupportSize V p x)) :
    GSTClassicalHodgePrincipalCutIncidenceTransposeCosmology.successorSelfEnergy
        V p x =
      rationalWorldTopPairing
        (recoordinatedSuccessorWorld V p x T)
        (rationalWorldDualPullback
          (recoordinatedSuccessorWorld V p x T)) := by
  rw [successorSelfEnergy_eq_finiteGSTPoincare V p x]
  symm
  exact rational_poincare_energy_recoordinate
    (successorSupportShape V p x) T
    (successorSupportWorld V p x)

/-- Nonzero principal-cut energy therefore survives every reshaping of the live
geometric neighborhood. -/
theorem recoordinatedGSTPoincare_ne_zero_of_exact_nonempty
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (T : GSTWorldShape (successorSupportSize V p x))
    (hExact :
      GSTClassicalHodgeRelativeSuccessorExactStratum.RelativeSuccessorAmbientExact
        V p x)
    (hNonempty :
      (GSTClassicalHodgePrincipalCutSuccessorOperator.relativeCodimensionOneFinset
        V x.1).Nonempty) :
    rationalWorldTopPairing
        (recoordinatedSuccessorWorld V p x T)
        (rationalWorldDualPullback
          (recoordinatedSuccessorWorld V p x T)) ≠ 0 := by
  rw [← successorSelfEnergy_eq_recoordinatedGSTPoincare V p x T]
  exact
    GSTClassicalHodgePrincipalCutIncidenceTransposeCosmology.successorSelfEnergy_ne_zero_of_exact_nonempty
      V p x hExact hNonempty

#check rationalTransportCoef
#check rational_square_energy_recoordinate
#check rational_poincare_energy_recoordinate
#check recoordinatedSuccessorWorld
#check successorSelfEnergy_eq_recoordinatedGSTPoincare
#check recoordinatedGSTPoincare_ne_zero_of_exact_nonempty

#print axioms rational_poincare_energy_recoordinate
#print axioms successorSelfEnergy_eq_recoordinatedGSTPoincare
#print axioms recoordinatedGSTPoincare_ne_zero_of_exact_nonempty

end GSTClassicalHodgePrincipalCutLimitlessRecoordination
