import Mathlib

/-!
# GST exact universal middle-intersection Gram unimodularity

The genuine intersection pairing of the three algebraic codimension-two
cycle classes h², j_*(point), j_*(xi) on the blow-up of P^4 along a smooth
curve is numerically

      [1,0,0; 0,0,-1; 0,-1,-n],

where n=5 degree(C)+2 genus(C)-2. This file checks the symbolic rational
unimodular inverse for arbitrary n; it does not assume target Hodge
surjectivity or target-native reconstruction.

The identification with the true scheme intersection form is the geometric
projective bundle and Gysin comparison obligation, not asserted to be
proved by the matrix multiplication alone.
-/
set_option maxHeartbeats 2000000

namespace GSTBlowupGramUnimodularity

def geometricGram (n : ℚ) : Matrix (Fin 3) (Fin 3) ℚ :=
  !![1, 0, 0; 0, 0, -1; 0, -1, -n]

def geometricGramInverse (n : ℚ) : Matrix (Fin 3) (Fin 3) ℚ :=
  !![1, 0, 0; 0, n, -1; 0, -1, 0]

/-- Rational intersection Gram is invertible with an exact inverse at
EVERY normal degree n, with no geometric nonvanishing hypothesis. -/
theorem gram_mul_inverse (n : ℚ) :
    geometricGram n * geometricGramInverse n = 1 := by
  classical
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [geometricGram, geometricGramInverse,
      Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

/-- The other multiplication is also exactly identity: no right-inverse
only artifact is possible in this three-dimensional rational setting. -/
theorem inverse_mul_gram (n : ℚ) :
    geometricGramInverse n * geometricGram n = 1 := by
  classical
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [geometricGram, geometricGramInverse,
      Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

#check gram_mul_inverse
#check inverse_mul_gram
#print axioms gram_mul_inverse

end GSTBlowupGramUnimodularity
