import GSTClassicalHodgePrimitiveArsenalIrreducibility
import GSTClassicalHodgeSheetSpectralExtraction
import GSTSquarePureHodgeDuality

/-!
# GST CLASSICAL HODGE — PRIMITIVE ARSENAL RATIONALIZATION

This module removes the last coordinate-only interpretation from the finite
primitive arsenal.  Each rational operator used by the irreducibility engine
is identified with the rational scalar extension of an operator already
constructed in the limitless GST world universe.

* `sheetProjectorQ` is the rationalized matrix of the integer code-sector
  projector `sheetSpectralProj` on pure diagonal atoms;
* `diagonalLefschetzQ` was defined directly from the native `worldAct` matrix
  coefficients of `L^t`;
* `poincareReverseQ` is the rational coordinate transport of the native
  square-world Poincare involution.

Thus the finite irreducibility mechanism is genuinely driven by the existing
world operator algebra.
-/

set_option maxHeartbeats 30000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open GSTWorldCosmology
open GSTWorldPoincareDuality
open GSTDimensionFreeHodgeDiagonal
open GSTGlobalPureHodgeCosmology
open GSTSquarePureHodgeDuality
open GSTClassicalHodgeSheetSpectralExtraction
open GSTClassicalHodgeFullArsenalIrreducibility
open GSTClassicalHodgeExplicitArsenalGeneration
open GSTClassicalHodgePrimitiveArsenalIrreducibility

namespace GSTClassicalHodgePrimitiveArsenalRationalization

/-- Matrix coefficient of the actual integer spectral projector between two
pure diagonal basis sheets, viewed in Q. -/
def spectralProjectorMatrixCoeff
    {N : Nat} (i r q : Fin N) : ℚ :=
  (sheetSpectralProj i (sheetDiagonalAtom r 1) (q,q) : ℚ)

/-- Rational scalar extension of the actual integer spectral projector. -/
noncomputable def rationalizedSheetSpectralProj
    {N : Nat} (i : Fin N) :
    Module.End ℚ (RationalPureWindow N) where
  toFun a := fun q =>
    ∑ r : Fin N, spectralProjectorMatrixCoeff i r q * a r
  map_add' := by
    intro a b
    funext q
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro c a
    funext q
    simp [mul_assoc, Finset.mul_sum]

/-- The actual integer spectral projector sends a pure basis atom to itself
when its code matches the selected sheet and to zero otherwise. -/
theorem sheetSpectralProj_basis_atom
    {N : Nat} (i r : Fin N) :
    sheetSpectralProj i (sheetDiagonalAtom r 1) =
      if r = i then sheetDiagonalAtom i 1 else 0 := by
  by_cases hri : r = i
  · subst r
    rw [sheetSpectralProj_pure_eq_atom]
    · funext x
      simp [sheetDiagonalAtom, worldDiagonalClass, worldBasis]
    · intro x hx
      simp [sheetDiagonalAtom,
        worldDiagonalClass_off_diagonal r.2 r.2 x (Or.inl hx)]
  · apply sheetSpectralProj_orthogonal i r hri
      (sheetDiagonalAtom r 1) |>.symm.trans ?_
    rw [sheetSpectralProj_pure_eq_atom]
    · funext x
      simp [sheetDiagonalAtom, worldDiagonalClass, worldBasis]
    · intro x hx
      simp [sheetDiagonalAtom,
        worldDiagonalClass_off_diagonal r.2 r.2 x (Or.inl hx)]

/-- Exact matrix coefficient of the native spectral projector. -/
theorem spectralProjectorMatrixCoeff_eq
    {N : Nat} (i r q : Fin N) :
    spectralProjectorMatrixCoeff i r q =
      if r = i ∧ q = i then 1 else 0 := by
  unfold spectralProjectorMatrixCoeff
  rw [sheetSpectralProj_basis_atom i r]
  by_cases hri : r = i
  · subst r
    simp [sheetDiagonalAtom, worldDiagonalClass, worldBasis]
  · simp [hri]

/-- **NATIVE SPECTRAL PROJECTOR = RATIONAL SHEET PROJECTOR.** -/
theorem rationalizedSheetSpectralProj_eq
    {N : Nat} (i : Fin N) :
    rationalizedSheetSpectralProj i = sheetProjectorQ i := by
  apply LinearMap.ext
  intro a
  funext q
  simp [rationalizedSheetSpectralProj, spectralProjectorMatrixCoeff_eq,
    sheetProjectorQ, rationalPureBasis]

/-- Matrix coefficient of the rationalized native Poincare involution. -/
def poincareMatrixCoeff
    {N : Nat} (r q : Fin N) : ℚ :=
  if q = pureMirror r then 1 else 0

/-- Rational matrix extension of native pure-Hodge Poincare reversal. -/
noncomputable def rationalizedWorldPoincare
    (N : Nat) : Module.End ℚ (RationalPureWindow N) where
  toFun a := fun q =>
    ∑ r : Fin N, poincareMatrixCoeff r q * a r
  map_add' := by
    intro a b
    funext q
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro c a
    funext q
    simp [mul_assoc, Finset.mul_sum]

/-- Native Poincare scalar extension is exactly coordinate reversal. -/
theorem rationalizedWorldPoincare_eq
    (N : Nat) :
    rationalizedWorldPoincare N = (poincareReverseQ N).toLinearMap := by
  apply LinearMap.ext
  intro a
  funext q
  classical
  simp [rationalizedWorldPoincare, poincareMatrixCoeff,
    poincareReverseQ]

/-- The Lefschetz primitive was already defined directly from native world
matrix coefficients; this theorem records the exact basis formula. -/
theorem diagonalLefschetzQ_basis
    {N t : Nat} (p q : Fin N) :
    diagonalLefschetzQ N t (rationalPureBasis p) q =
      (worldAct N N ((L N N)^t)
        (worldBasis (pureDiagonalState p))
        (pureDiagonalState q) : ℚ) := by
  simp [diagonalLefschetzQ, rationalPureBasis]

/-- Primitive-arena identification crown. -/
theorem primitive_arsenal_rationalization_crown :
    (∀ N (i : Fin N),
      rationalizedSheetSpectralProj i = sheetProjectorQ i)
    ∧ (∀ N,
      rationalizedWorldPoincare N = (poincareReverseQ N).toLinearMap)
    ∧ (∀ N t (p q : Fin N),
      diagonalLefschetzQ N t (rationalPureBasis p) q =
        (worldAct N N ((L N N)^t)
          (worldBasis (pureDiagonalState p))
          (pureDiagonalState q) : ℚ)) := by
  exact ⟨
    fun _ i => rationalizedSheetSpectralProj_eq i,
    rationalizedWorldPoincare_eq,
    fun _ _ p q => diagonalLefschetzQ_basis p q⟩

#check spectralProjectorMatrixCoeff
#check rationalizedSheetSpectralProj
#check rationalizedSheetSpectralProj_eq
#check rationalizedWorldPoincare
#check rationalizedWorldPoincare_eq
#check diagonalLefschetzQ_basis
#check primitive_arsenal_rationalization_crown

#print axioms rationalizedSheetSpectralProj_eq
#print axioms rationalizedWorldPoincare_eq
#print axioms diagonalLefschetzQ_basis
#print axioms primitive_arsenal_rationalization_crown

end GSTClassicalHodgePrimitiveArsenalRationalization
