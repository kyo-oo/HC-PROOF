import GSTClassicalHodgeFiberedCosmology
import GSTClassicalHodgeTransferSeedUniverse

/-!
# GST CLASSICAL HODGE — MULTIPLICITY-FORGETTING KERNEL

The limitless GST base has one diagonal generator at each weight, while a
genuine rational `(p,p)` Hodge fiber may have many independent multiplicity
sheets above the same weight.  The fibered completion retains those sheets,
but `forgetMultiplicityToGST` deliberately collapses them to the single base
GST generator.

This file makes the resulting kernel explicit.  Any two distinct classical
Hodge basis sheets at the same weight have a nonzero difference in the fibered
universe, while their difference projects to zero in the un-fibered limitless
GST address universe.

Therefore no proof that factors only through `forgetMultiplicityToGST` can
distinguish arbitrary classical Hodge multiplicity.  The final Hodge argument
must remain in the fibered/tomographic layer until genuine geometry resolves
those sheet differences.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeMultiplicityForgettingKernel

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Difference of two multiplicity sheets above the same GST weight. -/
def sheetDifference
    (i j : ClassicalHodgeBasisIndex V H p) :
    FiberedHodgeAddress V H :=
  Finsupp.single (⟨p, i⟩ : FiberedHodgeIndex V H) 1 -
    Finsupp.single (⟨p, j⟩ : FiberedHodgeIndex V H) 1

/-- The multiplicity-forgetting projection kills the zero address. -/
theorem forgetMultiplicityToGST_zero
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) :
    forgetMultiplicityToGST (0 : FiberedHodgeAddress V H) = 0 := by
  simp [forgetMultiplicityToGST, Finsupp.sum_zero_index]

/-- The multiplicity-forgetting projection is a group homomorphism on finite
addresses, hence distributes over subtraction. -/
theorem forgetMultiplicityToGST_sub
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (φ ψ : FiberedHodgeAddress V H) :
    forgetMultiplicityToGST (φ - ψ) =
      forgetMultiplicityToGST φ - forgetMultiplicityToGST ψ := by
  unfold forgetMultiplicityToGST
  refine Finsupp.sum_sub_index fun s q₁ q₂ => ?_
  ext t
  classical
  simp only [Finsupp.single_apply, Finsupp.sub_apply]
  by_cases ht : GSTTransferBridgeV2.compactClCode s.1 = t
  · rw [if_pos ht, if_pos ht, if_pos ht]
  · rw [if_neg ht, if_neg ht, if_neg ht, sub_self]

/-- Distinct multiplicity sheets have a genuinely nonzero difference before
multiplicity is forgotten. -/
theorem sheetDifference_ne_zero
    (i j : ClassicalHodgeBasisIndex V H p)
    (hij : i ≠ j) :
    sheetDifference (V := V) (H := H) i j ≠ 0 := by
  intro hz
  have hi := congrArg
    (fun f : FiberedHodgeAddress V H =>
      f (⟨p, i⟩ : FiberedHodgeIndex V H)) hz
  simp [sheetDifference, hij] at hi

/-- The same nonzero sheet difference disappears completely after projecting to
the un-fibered GST base address universe. -/
theorem forgetMultiplicity_sheetDifference
    (i j : ClassicalHodgeBasisIndex V H p) :
    forgetMultiplicityToGST
      (sheetDifference (V := V) (H := H) i j) = 0 := by
  unfold sheetDifference
  rw [forgetMultiplicityToGST_sub]
  rw [forgetMultiplicityToGST_single V H p i 1]
  rw [forgetMultiplicityToGST_single V H p j 1]
  simp

/-- Whenever one Hodge weight has two distinct multiplicity sheets,
`forgetMultiplicityToGST` is not injective. -/
theorem forgetMultiplicityToGST_not_injective_of_two_sheets
    (i j : ClassicalHodgeBasisIndex V H p)
    (hij : i ≠ j) :
    ¬ Function.Injective
      (@forgetMultiplicityToGST V H) := by
  intro hinj
  have hzero := forgetMultiplicity_sheetDifference (V := V) (H := H) i j
  have hsame :
      sheetDifference (V := V) (H := H) i j = 0 :=
    hinj (hzero.trans (forgetMultiplicityToGST_zero V H).symm)
  exact sheetDifference_ne_zero (V := V) (H := H) i j hij hsame

/-- Basis-vector form: two distinct genuine classical Hodge basis vectors have
identical un-fibered GST images. -/
theorem distinct_basis_same_baseGST_image
    (i j : ClassicalHodgeBasisIndex V H p) :
    forgetMultiplicityToGST
        (fiberedWeightCoordinates V H p (classicalHodgeBasis V H p i)) =
      forgetMultiplicityToGST
        (fiberedWeightCoordinates V H p (classicalHodgeBasis V H p j)) := by
  rw [classical_basis_projects_to_gst_diagonal V H p i]
  rw [classical_basis_projects_to_gst_diagonal V H p j]

#check sheetDifference
#check sheetDifference_ne_zero
#check forgetMultiplicity_sheetDifference
#check forgetMultiplicityToGST_not_injective_of_two_sheets
#check distinct_basis_same_baseGST_image

#print axioms sheetDifference_ne_zero
#print axioms forgetMultiplicity_sheetDifference
#print axioms forgetMultiplicityToGST_not_injective_of_two_sheets
#print axioms distinct_basis_same_baseGST_image

end GSTClassicalHodgeMultiplicityForgettingKernel
