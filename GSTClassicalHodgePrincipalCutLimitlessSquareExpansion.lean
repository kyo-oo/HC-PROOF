import GSTClassicalHodgePrincipalCutLimitlessRecoordination
import GSTSquarePureHodgeDuality

/-!
# GST CLASSICAL HODGE — LIMITLESS SQUARE EXPANSION OF ONE PRINCIPAL-CUT FLAG

A finite live successor neighborhood does not have to remain an N x 1 chart.
The limitless cosmos lets us add arbitrarily many zero coordinates around the
actual geometric data.  For the one-seed flag we use the most useful padding:
place the N live successor coefficients on the diagonal of an N x N world and
set every off-diagonal coordinate to zero.

This does two things simultaneously.

* The original principal-cut Gram energy is unchanged: the N^2-N new cells
  contribute exactly zero.
* Native GST Poincare duality preserves the square pure diagonal and reverses
  it.  Hence the geometric successor row now lives inside the dimension-free
  pure-Hodge/Poincare sector where the universal Lefschetz causal calculus is
  available.

This is an actual use of the additional geometric dimensions: the extra cells
are not new assumptions and they do not change the native flag.  They provide
room in which transpose/duality/causal operations can be manipulated without
collapsing the finite geometric data.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open scoped BigOperators

namespace GSTClassicalHodgePrincipalCutLimitlessSquareExpansion

open GSTProjectiveOverC
open GSTNativeCodimensionCyclePresentation
open GSTWorldPoincareDuality
open GSTClassicalHodgeFiniteSupportChart
open GSTClassicalHodgePrincipalCutIncidenceTransposeCosmology
open GSTClassicalHodgePrincipalCutLimitlessPoincareNormal
open GSTSquarePureHodgeDuality

/-- Put an arbitrary rational N-vector on the diagonal of an N x N GST world. -/
def squareDiagonalEmbed
    {N : Nat}
    (f : Fin N → ℚ) : WorldCell N N → ℚ :=
  fun c => if c.1 = c.2 then f c.1 else 0

@[simp]
theorem squareDiagonalEmbed_diagonal
    {N : Nat}
    (f : Fin N → ℚ)
    (k : Fin N) :
    squareDiagonalEmbed f (k, k) = f k := by
  simp [squareDiagonalEmbed]

@[simp]
theorem squareDiagonalEmbed_offDiagonal
    {N : Nat}
    (f : Fin N → ℚ)
    (a b : Fin N)
    (hab : a ≠ b) :
    squareDiagonalEmbed f (a, b) = 0 := by
  simp [squareDiagonalEmbed, hab]

/-- Adding the N^2-N off-diagonal zero coordinates does not change quadratic
energy. -/
theorem squareDiagonalEmbed_square_energy
    {N : Nat}
    (f : Fin N → ℚ) :
    (∑ c : WorldCell N N,
      squareDiagonalEmbed f c * squareDiagonalEmbed f c) =
      ∑ k : Fin N, f k * f k := by
  classical
  rw [Fintype.sum_prod_type]
  simp [squareDiagonalEmbed]

/-- Therefore the Poincare self-pairing of the square-expanded state is exactly
the original finite-vector Gram energy. -/
theorem squareDiagonalEmbed_poincare_energy
    {N : Nat}
    (f : Fin N → ℚ) :
    rationalWorldTopPairing
        (squareDiagonalEmbed f)
        (rationalWorldDualPullback (squareDiagonalEmbed f)) =
      ∑ k : Fin N, f k * f k := by
  rw [rationalWorldTopPairing_dualPullback_self]
  exact squareDiagonalEmbed_square_energy f

/-- Enumerated coefficient vector of the actual geometric successor row. -/
def successorSupportVector
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p) :
    Fin (successorSupportSize V p x) → ℚ :=
  fun k =>
    successorPresentation V p x
      (((successorSupportEquivFin V p x).symm k).1)

/-- The genuine principal-cut successor row embedded on the pure diagonal of a
square GST world. -/
def squareExpandedSuccessorWorld
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p) :
    WorldCell (successorSupportSize V p x)
      (successorSupportSize V p x) → ℚ :=
  squareDiagonalEmbed (successorSupportVector V p x)

/-- Enumeration of the live successor support preserves the square energy. -/
theorem successorSupportVector_square_sum
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p) :
    (∑ k : Fin (successorSupportSize V p x),
      successorSupportVector V p x k * successorSupportVector V p x k) =
      ∑ y : LiveSuccessor V p x,
        successorPresentation V p x y.1 *
          successorPresentation V p x y.1 := by
  exact Fintype.sum_equiv
    (successorSupportEquivFin V p x).symm
    (fun k => successorSupportVector V p x k * successorSupportVector V p x k)
    (fun y => successorPresentation V p x y.1 *
      successorPresentation V p x y.1)
    (fun k => by simp [successorSupportVector])

/-- **SQUARE LIMITLESS PRINCIPAL-CUT/POINCARE IDENTITY.**
The native self-energy of the actual principal-cut flag is unchanged after
padding its live row into the pure diagonal of the N x N GST universe. -/
theorem successorSelfEnergy_eq_squareGSTPoincare
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p) :
    successorSelfEnergy V p x =
      rationalWorldTopPairing
        (squareExpandedSuccessorWorld V p x)
        (rationalWorldDualPullback
          (squareExpandedSuccessorWorld V p x)) := by
  rw [squareDiagonalEmbed_poincare_energy]
  rw [successorSupportVector_square_sum]
  exact successorSelfEnergy_eq_liveSupport_square_sum V p x

/-- The square expansion is genuinely pure-diagonal: every off-diagonal world
cell is zero. -/
theorem squareExpandedSuccessorWorld_offDiagonal
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (a b : Fin (successorSupportSize V p x))
    (hab : a ≠ b) :
    squareExpandedSuccessorWorld V p x (a, b) = 0 := by
  exact squareDiagonalEmbed_offDiagonal
    (successorSupportVector V p x) a b hab

/-- Every exact live principal cut gives a nonzero Poincare energy even after
expansion into the much larger square world. -/
theorem squareGSTPoincare_ne_zero_of_exact_nonempty
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hExact :
      GSTClassicalHodgeRelativeSuccessorExactStratum.RelativeSuccessorAmbientExact
        V p x)
    (hNonempty :
      (GSTClassicalHodgePrincipalCutSuccessorOperator.relativeCodimensionOneFinset
        V x.1).Nonempty) :
    rationalWorldTopPairing
        (squareExpandedSuccessorWorld V p x)
        (rationalWorldDualPullback
          (squareExpandedSuccessorWorld V p x)) ≠ 0 := by
  rw [← successorSelfEnergy_eq_squareGSTPoincare V p x]
  exact successorSelfEnergy_ne_zero_of_exact_nonempty
    V p x hExact hNonempty

#check squareDiagonalEmbed
#check squareDiagonalEmbed_square_energy
#check squareDiagonalEmbed_poincare_energy
#check successorSupportVector
#check squareExpandedSuccessorWorld
#check successorSelfEnergy_eq_squareGSTPoincare
#check squareGSTPoincare_ne_zero_of_exact_nonempty

#print axioms squareDiagonalEmbed_poincare_energy
#print axioms successorSelfEnergy_eq_squareGSTPoincare
#print axioms squareGSTPoincare_ne_zero_of_exact_nonempty

end GSTClassicalHodgePrincipalCutLimitlessSquareExpansion
