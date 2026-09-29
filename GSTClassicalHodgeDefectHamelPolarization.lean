import GSTClassicalHodgeDefectPolarizedCoupledReciprocity
import Mathlib.LinearAlgebra.FreeModule.Basic

/-!
# GST CLASSICAL HODGE — HAMEL POLARIZATION OF THE ATOMIC-DEFECT UNIVERSE

The defect-polarized coupled reciprocity theorem uses a right-nondegenerate
rational pairing on each atomic-defect quotient.  That pairing is not new
geometry and must not remain as an artificial hypothesis.

Every `DefectAt V H p` is a rational vector space.  Choice supplies a Hamel
basis, and the finite-support coordinate representation of every vector gives
the algebraic dot product

    <x,y> = sum_i x_i y_i.

Because each Hamel coordinate vector has finite support, this pairing is
well-defined even when the defect space has unrestricted rank.  Evaluating
against a basis vector recovers the corresponding coordinate of `y`, so the
pairing separates the second input.  Thus every atomic-defect space carries a
right-perfect pairing unconditionally.

This removes the pairing-existence burden from the new coisometric Hodge
route.  The remaining content is genuinely geometric: construct the descended
return operator and prove its adjoint/scaled-return laws.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeDefectHamelPolarization

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeCrossWeightAtomicDefectDescent
open GSTClassicalHodgeDefectPolarizedCoupledReciprocity

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Choice of one Hamel basis of the rational atomic-defect quotient. -/
noncomputable def defectHamelBasis (p : Nat) :
    Basis
      (Module.Free.ChooseBasisIndex ℚ (DefectAt V H p))
      ℚ
      (DefectAt V H p) :=
  Module.Free.chooseBasis ℚ (DefectAt V H p)

/-- The coordinate dot-product pairing induced by the chosen Hamel basis.

`Finsupp.linearCombination` turns a finite coordinate vector `repr x` into the
same finite linear combination of the coordinate functionals `coord i`. -/
noncomputable def hamelDefectPair (p : Nat) :
    DefectAt V H p →ₗ[ℚ] (DefectAt V H p →ₗ[ℚ] ℚ) :=
  (Finsupp.linearCombination ℚ
      (fun i : Module.Free.ChooseBasisIndex ℚ (DefectAt V H p) =>
        (defectHamelBasis (V := V) (H := H) p).coord i)).comp
    (defectHamelBasis (V := V) (H := H) p).repr.toLinearMap

/-- Pairing against a basis vector on the left reads exactly the corresponding
Hamel coordinate on the right. -/
@[simp]
theorem hamelDefectPair_basis_left
    (p : Nat)
    (i : Module.Free.ChooseBasisIndex ℚ (DefectAt V H p))
    (y : DefectAt V H p) :
    hamelDefectPair (V := V) (H := H) p
        ((defectHamelBasis (V := V) (H := H) p) i) y =
      (defectHamelBasis (V := V) (H := H) p).repr y i := by
  classical
  simp [hamelDefectPair, Finsupp.linearCombination_apply]

/-- The Hamel coordinate pairing separates its second argument. -/
theorem hamelDefectPair_right_nondegenerate
    (p : Nat)
    (y : DefectAt V H p)
    (hy : ∀ x : DefectAt V H p,
      hamelDefectPair (V := V) (H := H) p x y = 0) :
    y = 0 := by
  let b := defectHamelBasis (V := V) (H := H) p
  apply b.repr.injective
  apply Finsupp.ext
  intro i
  have hi := hy (b i)
  have hcoord : b.repr y i = 0 := by
    simpa [b] using hi
  simpa using hcoord

/-- **UNCONDITIONAL DEFECT POLARIZATION.**
Every rational atomic-defect quotient carries a right-perfect pairing, with no
finite-dimensionality or Hodge-algebraicity assumption. -/
noncomputable def hamelRightPerfectDefectPairing (p : Nat) :
    RightPerfectDefectPairing V H p where
  pair := hamelDefectPair (V := V) (H := H) p
  right_nondegenerate :=
    hamelDefectPair_right_nondegenerate (V := V) (H := H) p

/-- Pairing existence is therefore never an obstruction to building a
coisometric defect return. -/
theorem exists_rightPerfectDefectPairing (p : Nat) :
    Nonempty (RightPerfectDefectPairing V H p) :=
  ⟨hamelRightPerfectDefectPairing (V := V) (H := H) p⟩

/-- The source/target pairings required by one adjacent-weight coisometry can
always be supplied simultaneously. -/
theorem exists_adjacent_defect_pairings (p : Nat) :
    Nonempty
      (RightPerfectDefectPairing V H p ×
        RightPerfectDefectPairing V H (p + 1)) :=
  ⟨(hamelRightPerfectDefectPairing (V := V) (H := H) p,
    hamelRightPerfectDefectPairing (V := V) (H := H) (p + 1))⟩

#check defectHamelBasis
#check hamelDefectPair
#check hamelDefectPair_basis_left
#check hamelDefectPair_right_nondegenerate
#check hamelRightPerfectDefectPairing
#check exists_rightPerfectDefectPairing
#check exists_adjacent_defect_pairings

#print axioms hamelDefectPair_basis_left
#print axioms hamelDefectPair_right_nondegenerate
#print axioms exists_rightPerfectDefectPairing
#print axioms exists_adjacent_defect_pairings

end GSTClassicalHodgeDefectHamelPolarization
