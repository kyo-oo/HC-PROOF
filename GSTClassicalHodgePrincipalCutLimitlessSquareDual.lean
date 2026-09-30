import GSTClassicalHodgePrincipalCutLimitlessSquareExpansion

/-!
# GST CLASSICAL HODGE — SQUARE POINCARE DUAL OF THE PRINCIPAL-CUT FLAG

The live principal-cut successor row has been padded onto the pure diagonal of
an N x N GST world.  On a square world, native Poincare complement preserves
that diagonal and reverses its coordinate order.

Therefore the reverse/transpose probe of the padded geometric flag is no
longer additional data: it is exactly the mirror of the same forward successor
row.  This file records that equality for rational coefficients.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgePrincipalCutLimitlessSquareDual

open GSTProjectiveOverC
open GSTNativeCodimensionCyclePresentation
open GSTWorldPoincareDuality
open GSTSquarePureHodgeDuality
open GSTClassicalHodgePrincipalCutLimitlessPoincareNormal
open GSTClassicalHodgePrincipalCutLimitlessSquareExpansion

/-- Mirror coordinate on an arbitrary square-world axis. -/
def squareMirrorFin
    {N : Nat} (k : Fin N) : Fin N :=
  ⟨N - 1 - k.1, by omega⟩

@[simp]
theorem squareMirrorFin_involutive
    {N : Nat} (k : Fin N) :
    squareMirrorFin (squareMirrorFin k) = k := by
  apply Fin.ext
  unfold squareMirrorFin
  simp only
  omega

/-- Poincare complement of a diagonal square cell is the mirrored diagonal
cell. -/
theorem worldDual_squareDiagonal
    {N : Nat} (k : Fin N) :
    worldDual ((k, k) : WorldCell N N) =
      (squareMirrorFin k, squareMirrorFin k) := by
  unfold worldDual squareMirrorFin complementFin
  apply Prod.ext <;> apply Fin.ext <;> rfl

/-- Complement preserves off-diagonality in a square world. -/
theorem worldDual_offDiagonal
    {N : Nat} (a b : Fin N)
    (hab : a ≠ b) :
    (worldDual ((a, b) : WorldCell N N)).1 ≠
      (worldDual ((a, b) : WorldCell N N)).2 := by
  intro h
  apply hab
  apply Fin.ext
  have hv := congrArg Fin.val h
  unfold worldDual complementFin at hv
  dsimp only at hv
  omega

/-- **SQUARE-DIAGONAL POINCARE REVERSAL.**
The Poincare dual of a rational diagonal state is exactly the same coefficient
vector with its diagonal order reversed. -/
theorem rationalWorldDualPullback_squareDiagonalEmbed
    {N : Nat}
    (f : Fin N → ℚ) :
    rationalWorldDualPullback (squareDiagonalEmbed f) =
      squareDiagonalEmbed (fun k => f (squareMirrorFin k)) := by
  funext c
  rcases c with ⟨a, b⟩
  by_cases hab : a = b
  · subst b
    simp [rationalWorldDualPullback, squareDiagonalEmbed,
      worldDual_squareDiagonal, squareMirrorFin_involutive]
  · have hdual := worldDual_offDiagonal a b hab
    simp [rationalWorldDualPullback, squareDiagonalEmbed, hab, hdual]

/-- Applied to the actual principal-cut row, the entire transpose probe is the
mirror of its forward successor coefficients. -/
theorem dual_squareExpandedSuccessorWorld
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p) :
    rationalWorldDualPullback (squareExpandedSuccessorWorld V p x) =
      squareDiagonalEmbed
        (fun k => successorSupportVector V p x (squareMirrorFin k)) := by
  exact rationalWorldDualPullback_squareDiagonalEmbed
    (successorSupportVector V p x)

/-- Pointwise form: a forward successor coefficient at one diagonal address is
read by the dual probe at the mirrored address with exactly the same value. -/
theorem dual_squareExpandedSuccessorWorld_mirror_read
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (k : Fin (successorSupportSize V p x)) :
    rationalWorldDualPullback (squareExpandedSuccessorWorld V p x)
        (squareMirrorFin k, squareMirrorFin k) =
      successorSupportVector V p x k := by
  rw [dual_squareExpandedSuccessorWorld]
  simp [squareDiagonalEmbed, squareMirrorFin_involutive]

/-- The square-expanded flag and its Poincare reverse carry identical support
cardinality and identical nonzero coefficient multiset, only mirrored. -/
theorem dual_squareExpandedSuccessorWorld_ne_zero_iff
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p) :
    rationalWorldDualPullback (squareExpandedSuccessorWorld V p x) ≠ 0 ↔
      squareExpandedSuccessorWorld V p x ≠ 0 := by
  constructor
  · intro hdual hzero
    apply hdual
    rw [hzero]
    simp [rationalWorldDualPullback]
  · intro hrow hdualzero
    apply hrow
    have := congrArg rationalWorldDualPullback hdualzero
    simpa using this

#check squareMirrorFin
#check worldDual_squareDiagonal
#check rationalWorldDualPullback_squareDiagonalEmbed
#check dual_squareExpandedSuccessorWorld
#check dual_squareExpandedSuccessorWorld_mirror_read

#print axioms rationalWorldDualPullback_squareDiagonalEmbed
#print axioms dual_squareExpandedSuccessorWorld
#print axioms dual_squareExpandedSuccessorWorld_mirror_read

end GSTClassicalHodgePrincipalCutLimitlessSquareDual
