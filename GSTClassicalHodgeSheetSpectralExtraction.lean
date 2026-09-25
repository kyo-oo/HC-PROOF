import GSTClassicalHodgeIntegralSquareLocalization
import GSTWorldRecoordinationGroupoid
import GSTDimensionFreeHodgeDiagonal
import GSTSquarePureHodgeDuality

/-!
# GST CLASSICAL HODGE — SINGLE-SHEET SPECTRAL EXTRACTION

After denominator clearing, every hypothetical separator witness lives inside
one finite integral pure GST square.  The world-recoordination theory already
contains exact invariant code-sector projectors, and every such projector is
an explicit integer spectral polynomial.

On a pure square, only diagonal code sectors can be live.  Hence the full
state decomposes into independent diagonal multiplicity sheets.  A nonzero
Poincare pairing forces at least one complementary pair of individual sheets
to pair nontrivially.

This reduces any global classical witness to one spectrally isolated sheet
atom, while retaining the original classical codimension as an external base
label rather than confusing it with the local sheet coordinate.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open GSTProjectiveOverC
open GSTWorldRecoordinationGroupoid
open GSTWorldPoincareDuality
open GSTDimensionFreeHodgeDiagonal
open GSTGlobalPureHodgeCosmology
open GSTSquarePureHodgeDuality
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeSeparatorProbe
open GSTClassicalHodgeSquareStrandLocalization
open GSTClassicalHodgeIntegralSquareLocalization

namespace GSTClassicalHodgeSheetSpectralExtraction

/-- Invariant world code of the i-th multiplicity-sheet diagonal cell. -/
def sheetCode {N : Nat} (i : Fin N) : Nat :=
  worldCode (outputShape N N) (i,i)

/-- Exact numeric sheet code in the row-major square chart. -/
theorem sheetCode_val
    {N : Nat} (i : Fin N) :
    sheetCode i = (N + 1) * i.1 := by
  unfold sheetCode
  rw [worldCode_expanded]
  ring

/-- The world-code observable is injective on every shaped world because its
underlying coding map is an equivalence. -/
theorem worldCode_injective
    {M : Nat} (S : GSTWorldShape M) :
    Function.Injective (worldCode S) := by
  intro x y h
  apply (shapeCodeEquiv S).injective
  apply Fin.ext
  exact h

/-- Integral diagonal atom carried by one local multiplicity sheet. -/
def sheetDiagonalAtom
    {N : Nat} (i : Fin N) (z : ℤ) :
    ShapeCoef (outputShape N N) :=
  fun c => z * worldDiagonalClass i.2 i.2 c

/-- Spectral projector onto one local multiplicity-sheet code. -/
def sheetSpectralProj
    {N : Nat} (i : Fin N)
    (f : ShapeCoef (outputShape N N)) :
    ShapeCoef (outputShape N N) :=
  codeSectorProj (outputShape N N) (sheetCode i) f

/-- A sheet projector is exactly an explicit integer polynomial spectral
operator, up to its nonzero normalization scalar. -/
theorem sheetSpectralProj_is_polynomial
    {N : Nat} (i : Fin N) :
    ∃ (P : Polynomial ℤ) (c : ℤ), c ≠ 0 ∧
      ∀ (f : ShapeCoef (outputShape N N))
        (x : ShapeState (outputShape N N)),
        codePolyOp (outputShape N N) P f x =
          c * sheetSpectralProj i f x := by
  apply codeSector_projector_polynomial
  unfold sheetCode
  exact worldCode_lt (outputShape N N) (i,i)

/-- On a pure integral square, the i-th spectral sector is exactly the i-th
coefficient times its single diagonal sheet atom. -/
theorem sheetSpectralProj_pure_eq_atom
    {N : Nat} (i : Fin N)
    (f : ShapeCoef (outputShape N N))
    (hf : isWorldPureHodge f) :
    sheetSpectralProj i f =
      sheetDiagonalAtom i (f (i,i)) := by
  funext x
  by_cases hcode : worldCode (outputShape N N) x = sheetCode i
  · have hx : x = (i,i) :=
      worldCode_injective (outputShape N N) hcode
    subst x
    simp [sheetSpectralProj, codeSectorProj,
      sheetDiagonalAtom, sheetCode, worldDiagonalClass, worldBasis]
  · have hxne : x ≠ (i,i) := by
      intro hx
      subst x
      exact hcode rfl
    have hdiagOr : x.1.1 ≠ x.2.1 ∨
        (x.1.1 = x.2.1 ∧ x.1 ≠ i) := by
      by_cases hd : x.1.1 = x.2.1
      · right
        refine ⟨hd, ?_⟩
        intro hxi
        have hyi : x.2 = i := by
          apply Fin.ext
          simpa [hxi] using hd.symm
        exact hxne (Prod.ext hxi hyi)
      · exact Or.inl hd
    rw [show sheetSpectralProj i f x = 0 by
      simp [sheetSpectralProj, codeSectorProj, hcode]]
    rcases hdiagOr with hoff | ⟨hdiag,hxi⟩
    · simp [sheetDiagonalAtom,
        worldDiagonalClass_off_diagonal i.2 i.2 x
          (Or.inl (by
            intro hxp
            have : x.1.1 = i.1 := hxp
            exact hoff (this.trans (by
              have := congrArg Fin.val
                (show x.2 = i from by
                  apply Fin.ext
                  omega)
              simpa using this.symm))))]
    · have hright : x.2 ≠ i := by
        intro hxi2
        apply hxi
        apply Fin.ext
        have := congrArg Fin.val hxi2
        omega
      have hoffWeight : x.1.1 ≠ i.1 ∨ x.2.1 ≠ i.1 := by
        left
        intro hval
        apply hxi
        exact Fin.ext hval
      simp [sheetDiagonalAtom,
        worldDiagonalClass_off_diagonal i.2 i.2 x hoffWeight]

/-- Different local sheet projectors are orthogonal. -/
theorem sheetSpectralProj_orthogonal
    {N : Nat} (i j : Fin N) (hij : i ≠ j)
    (f : ShapeCoef (outputShape N N)) :
    sheetSpectralProj i (sheetSpectralProj j f) = 0 := by
  apply codeSectorProj_orthogonal
  intro hcode
  have hdiag : (i,i) = (j,j) :=
    worldCode_injective (outputShape N N) hcode
  exact hij (congrArg Prod.fst hdiag)

/-- Every integral pure square is the finite sum of its independent sheet
atoms. -/
theorem pureWorld_sheet_decomposition
    {N : Nat}
    (f : ShapeCoef (outputShape N N))
    (hf : isWorldPureHodge f) :
    f = ∑ i : Fin N, sheetDiagonalAtom i (f (i,i)) := by
  funext x
  by_cases hdiag : x.1.1 = x.2.1
  · let i : Fin N := x.1
    have hx : x = (i,i) := by
      apply Prod.ext
      · rfl
      · apply Fin.ext
        exact hdiag.symm
    subst x
    classical
    rw [Finset.sum_eq_single i]
    · simp [sheetDiagonalAtom, worldDiagonalClass, worldBasis]
    · intro j hj hji
      have hne : (i,i) ≠ (j,j) := by
        intro h
        exact hji (congrArg Prod.fst h).symm
      simp [sheetDiagonalAtom, worldDiagonalClass, worldBasis, hne]
    · simp
  · rw [hf x hdiag]
    classical
    apply Finset.sum_eq_zero
    intro i hi
    simp [sheetDiagonalAtom,
      worldDiagonalClass_off_diagonal i.2 i.2 x
        (Or.inl (by
          intro hxi
          apply hdiag
          have h1 : x.1 = i := Fin.ext hxi
          have h2 : x.2 = i := by
            apply Fin.ext
            omega
          exact congrArg Fin.val (h1.trans h2.symm)))]

/-- Complementary local multiplicity-sheet index under square Poincare
reflection. -/
def sheetMirror {N : Nat} (i : Fin N) : Fin N :=
  complementFin i

@[simp]
theorem worldDual_sheetDiagonal
    {N : Nat} (i : Fin N) :
    worldDual ((i,i) : WorldCell N N) =
      (sheetMirror i, sheetMirror i) := by
  rfl

/-- A nonzero pure-vs-pure integral Poincare pairing contains one nonzero
complementary sheet product. -/
theorem nonzero_purePairing_yields_nonzero_sheet_product
    {N : Nat}
    (A B : ShapeCoef (outputShape N N))
    (hA : isWorldPureHodge A)
    (hpair : worldTopPairing A B ≠ 0) :
    ∃ i : Fin N,
      A (i,i) * B (sheetMirror i, sheetMirror i) ≠ 0 := by
  unfold worldTopPairing at hpair
  by_contra hnone
  push_neg at hnone
  apply hpair
  apply Finset.sum_eq_zero
  intro c hc
  by_cases hdiag : c.1.1 = c.2.1
  · let i : Fin N := c.1
    have hcdiag : c = (i,i) := by
      apply Prod.ext
      · rfl
      · apply Fin.ext
        exact hdiag.symm
    subst c
    simpa [sheetMirror] using hnone i
  · simp [hA c hdiag]

/-- The corresponding single-sheet spectral projectors already retain a
nonzero Poincare pairing. -/
theorem nonzero_purePairing_yields_nonzero_projected_pairing
    {N : Nat}
    (A B : ShapeCoef (outputShape N N))
    (hA : isWorldPureHodge A)
    (hB : isWorldPureHodge B)
    (hpair : worldTopPairing A B ≠ 0) :
    ∃ i : Fin N,
      worldTopPairing
        (sheetSpectralProj i A)
        (sheetSpectralProj (sheetMirror i) B) ≠ 0 := by
  obtain ⟨i,hi⟩ :=
    nonzero_purePairing_yields_nonzero_sheet_product A B hA hpair
  refine ⟨i, ?_⟩
  rw [sheetSpectralProj_pure_eq_atom i A hA]
  rw [sheetSpectralProj_pure_eq_atom (sheetMirror i) B hB]
  classical
  unfold worldTopPairing sheetDiagonalAtom
  rw [Finset.sum_eq_single ((i,i) : WorldCell N N)]
  · simpa [worldDual_sheetDiagonal, worldDiagonalClass, worldBasis,
      sheetMirror] using hi
  · intro c hc hci
    have hzero : worldDiagonalClass i.2 i.2 c = 0 := by
      unfold worldDiagonalClass worldBasis
      simp [hci]
    simp [hzero]
  · simp

/-- **SINGLE-SHEET REDUCTION OF CLASSICAL HODGE FAILURE.**
Any Stage-2G failure witness yields a finite integral pure square and one
spectrally isolated multiplicity sheet whose complementary projected pairing
is nonzero.  The original classical codimension p is retained separately. -/
theorem not_hodge_yields_single_sheet_spectral_witness
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (hnot : ¬ GSTGeometricRealizationStage2G.BigradedBettiHodgeStatement V H) :
    ∃ p : Nat,
    ∃ S : AtomicSeparatorProbe V H p,
    ∃ N : Nat,
    ∃ A B : ShapeCoef (outputShape N N),
    ∃ i : Fin N,
      isWorldPureHodge A ∧
      isWorldPureHodge B ∧
      worldTopPairing
        (sheetSpectralProj i A)
        (sheetSpectralProj (sheetMirror i) B) ≠ 0 := by
  obtain ⟨p,S,a,b,ha,hb,hpair⟩ :=
    not_hodge_yields_nonzero_pureSquare_pairing V H hnot
  let IA := canonicalIntegralPureSquareModel a ha
  let IB := canonicalIntegralPureSquareModel b hb
  have hIntegral : worldTopPairing IA.world IB.world ≠ 0 :=
    nonzero_rationalPairing_yields_nonzero_integralPairing
      a b ha hb hpair
  obtain ⟨i,hi⟩ :=
    nonzero_purePairing_yields_nonzero_projected_pairing
      IA.world IB.world IA.world_pure IB.world_pure hIntegral
  exact ⟨p,S,
    fiberedSupportSize (fiberedWeightCoordinates V H p S.alpha),
    IA.world, IB.world, i,
    IA.world_pure, IB.world_pure, hi⟩

#check sheetCode
#check sheetCode_val
#check worldCode_injective
#check sheetDiagonalAtom
#check sheetSpectralProj
#check sheetSpectralProj_is_polynomial
#check sheetSpectralProj_pure_eq_atom
#check sheetSpectralProj_orthogonal
#check pureWorld_sheet_decomposition
#check sheetMirror
#check nonzero_purePairing_yields_nonzero_sheet_product
#check nonzero_purePairing_yields_nonzero_projected_pairing
#check not_hodge_yields_single_sheet_spectral_witness

#print axioms sheetSpectralProj_is_polynomial
#print axioms sheetSpectralProj_pure_eq_atom
#print axioms pureWorld_sheet_decomposition
#print axioms nonzero_purePairing_yields_nonzero_projected_pairing
#print axioms not_hodge_yields_single_sheet_spectral_witness

end GSTClassicalHodgeSheetSpectralExtraction
