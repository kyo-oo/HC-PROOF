import Mathlib
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import GSTUniversalLefschetzBasisPaths

/-!
# GST UNIVERSAL PASCAL LEFSCHETZ BLOCKS

The exact basis-path kernel is reorganized here into the canonical square
Pascal blocks which occur between complementary degree sectors.

The entry at row i and column j is the binomial coefficient with lower
index r+i-j, with the negative-index region represented by zero.

The old HC determinants 10, 6 and 1 are immediate finite shadows of this
single matrix family.
-/

set_option maxHeartbeats 20000000
set_option maxRecDepth 1000000

namespace GSTUniversalPascalLefschetzBlocks

open Matrix

/-- Consecutive Toeplitz/Pascal block of width s. -/
def pascalBlock (n r s : Nat) : Matrix (Fin s) (Fin s) ℤ :=
  fun i j =>
    if h : j.1 ≤ r + i.1 then
      (n.choose (r + i.1 - j.1) : ℤ)
    else 0

@[simp]
theorem pascalBlock_apply_of_le
    (n r s : Nat) (i j : Fin s)
    (h : j.1 ≤ r + i.1) :
    pascalBlock n r s i j =
      (n.choose (r + i.1 - j.1) : ℤ) := by
  simp [pascalBlock, h]

@[simp]
theorem pascalBlock_apply_of_lt
    (n r s : Nat) (i j : Fin s)
    (h : r + i.1 < j.1) :
    pascalBlock n r s i j = 0 := by
  simp [pascalBlock, Nat.not_le.mpr h]

/-- Degree zero to top in the historical 4 x 3 world. -/
theorem hc_pascal_det_degree0 :
    (pascalBlock 5 2 1).det = 10 := by
  rw [Matrix.det_fin_one]
  norm_num [pascalBlock]

/-- Degree one to degree four in the historical 4 x 3 world. -/
theorem hc_pascal_det_degree1 :
    (pascalBlock 3 1 2).det = 6 := by
  rw [Matrix.det_fin_two]
  norm_num [pascalBlock]

/-- Middle degree two to degree three in the historical 4 x 3 world. -/
theorem hc_pascal_det_degree2 :
    (pascalBlock 1 0 3).det = 1 := by
  rw [Matrix.det_fin_three]
  norm_num [pascalBlock]

/-- All three historical determinant certificates are shadows of one
consecutive-Pascal family. -/
theorem hc_pascal_determinant_profile :
    (pascalBlock 5 2 1).det = 10
    ∧ (pascalBlock 3 1 2).det = 6
    ∧ (pascalBlock 1 0 3).det = 1 :=
  ⟨hc_pascal_det_degree0,
    hc_pascal_det_degree1,
    hc_pascal_det_degree2⟩

#check pascalBlock
#check pascalBlock_apply_of_le
#check pascalBlock_apply_of_lt
#check hc_pascal_det_degree0
#check hc_pascal_det_degree1
#check hc_pascal_det_degree2
#check hc_pascal_determinant_profile

#print axioms hc_pascal_det_degree0
#print axioms hc_pascal_det_degree1
#print axioms hc_pascal_det_degree2
#print axioms hc_pascal_determinant_profile

end GSTUniversalPascalLefschetzBlocks
