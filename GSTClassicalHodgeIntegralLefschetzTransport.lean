import GSTClassicalHodgeLiveSheetIntertwining
import GSTPureHodgeLefschetzKernel
import GSTSquarePureHodgeDuality
import GSTClassicalHodgeFullArsenalIrreducibility

/-!
# GST CLASSICAL HODGE — INTEGRAL LEFSCHETZ SHEET TRANSPORT

A live classical multiplicity coordinate has already been identified with one
nonzero integral diagonal atom in a finite pure GST square.  This module runs
the actual universal Lefschetz action on that atom.

For source sheet `r` and forward target sheet `s`, the unique live time is
`2(s-r)` and the target coefficient is the source coefficient multiplied by
the central binomial coefficient `choose (2(s-r)) (s-r)`.  This coefficient
is strictly nonzero.  Wrong times vanish.  Poincare reflection converts every
backward request into a forward request on mirrored sheets.

Thus projector isolation + universal Lefschetz evolution + Poincare reflection
supply the concrete integer movement stage of the full matrix-unit arsenal on
the integralized live classical support.
-/

set_option maxHeartbeats 20000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTWorldCosmology
open GSTWorldPoincareDuality
open GSTDimensionFreeHodgeDiagonal
open GSTGlobalPureHodgeCosmology
open GSTTruncatedWorldCohomologyRing
open GSTUniversalLefschetzCosmology
open GSTPureHodgeLefschetzKernel
open GSTSquarePureHodgeDuality
open GSTClassicalHodgeSheetSpectralExtraction
open GSTClassicalHodgeLiveSheetIntertwining
open GSTClassicalHodgeFullArsenalIrreducibility

namespace GSTClassicalHodgeIntegralLefschetzTransport

/-- An integral sheet atom is exactly the scalar multiple of the canonical
pure diagonal basis vector. -/
theorem sheetDiagonalAtom_eq_smul_basis
    {N : Nat} (r : Fin N) (z : ℤ) :
    sheetDiagonalAtom r z =
      z • worldBasis ((r,r) : WorldCell N N) := by
  funext x
  simp [sheetDiagonalAtom, worldDiagonalClass, worldBasis]

/-- Exact forward transport coefficient of one isolated integral sheet atom. -/
theorem sheetAtom_lefschetz_forward_exact
    {N : Nat}
    (r s : Fin N)
    (hrs : r.1 ≤ s.1)
    (z : ℤ) :
    worldAct N N
        ((L N N) ^ (2 * (s.1 - r.1)))
        (sheetDiagonalAtom r z)
        ((s,s) : WorldCell N N) =
      z * ((2 * (s.1 - r.1)).choose (s.1 - r.1) : ℤ) := by
  rw [sheetDiagonalAtom_eq_smul_basis]
  change
    ((worldOperatorHom N N
      ((L N N) ^ (2 * (s.1-r.1))) : WorldOperatorRing N N) :
        Module.End ℤ (WorldCoef N N))
      (z • worldBasis ((r,r) : WorldCell N N)) ((s,s) : WorldCell N N) = _
  rw [LinearMap.map_smul]
  change z *
    worldAct N N ((L N N) ^ (2 * (s.1-r.1)))
      (worldBasis ((r,r) : WorldCell N N)) ((s,s) : WorldCell N N) = _
  have hkernel := pure_diagonal_lefschetz_forward_exact
    (A := N) (B := N)
    (show Fin (min N N) from r)
    (show Fin (min N N) from s)
    (by simpa using hrs)
  simpa [pureWeightGap, pureDiagonalState, diagonalState] using
    congrArg (fun q : ℤ => z * q) hkernel

/-- The central-binomial movement coefficient is nonzero. -/
theorem sheetAtom_forward_scalar_ne_zero
    {N : Nat} (r s : Fin N) :
    ((2 * (s.1-r.1)).choose (s.1-r.1) : ℤ) ≠ 0 := by
  exact_mod_cast Nat.ne_of_gt (Nat.choose_pos (by omega))

/-- A nonzero isolated source sheet reaches every forward target sheet
nontrivially at the unique Lefschetz time. -/
theorem sheetAtom_lefschetz_forward_ne_zero
    {N : Nat}
    (r s : Fin N)
    (hrs : r.1 ≤ s.1)
    {z : ℤ} (hz : z ≠ 0) :
    worldAct N N
        ((L N N) ^ (2 * (s.1-r.1)))
        (sheetDiagonalAtom r z)
        ((s,s) : WorldCell N N) ≠ 0 := by
  rw [sheetAtom_lefschetz_forward_exact r s hrs z]
  exact mul_ne_zero hz (sheetAtom_forward_scalar_ne_zero r s)

/-- Wrong Lefschetz times give zero forward target coefficient. -/
theorem sheetAtom_lefschetz_wrong_time_zero
    {N n : Nat}
    (r s : Fin N)
    (hrs : r.1 ≤ s.1)
    (htime : n ≠ 2 * (s.1-r.1))
    (z : ℤ) :
    worldAct N N ((L N N)^n)
        (sheetDiagonalAtom r z)
        ((s,s) : WorldCell N N) = 0 := by
  rw [sheetDiagonalAtom_eq_smul_basis]
  change z *
      worldAct N N ((L N N)^n)
        (worldBasis ((r,r) : WorldCell N N)) ((s,s) : WorldCell N N) = 0
  have hz := pure_diagonal_lefschetz_wrong_time_zero
    (A := N) (B := N) (n := n)
    (show Fin (min N N) from r)
    (show Fin (min N N) from s)
    (by simpa using hrs)
    (by simpa [pureWeightGap] using htime)
  simpa [pureDiagonalState, diagonalState] using congrArg (fun q : ℤ => z*q) hz

/-- Poincare reflection turns every backward sheet request into an ordered
forward request on the mirrored diagonal. -/
theorem backward_request_reflects_forward
    {N : Nat}
    (r s : Fin N)
    (hsr : s.1 ≤ r.1) :
    (pureMirror (show Fin (min N N) from r)).1 ≤
      (pureMirror (show Fin (min N N) from s)).1 := by
  exact mirror_turns_backward_forward
    (show Fin (min N N) from r)
    (show Fin (min N N) from s)
    (by simpa using hsr)

/-- The Poincare dual of a sheet atom is the mirrored sheet atom with the same
integer coefficient. -/
theorem squarePureDual_sheetAtom
    {N : Nat} (r : Fin N) (z : ℤ) :
    squarePureDual
      (⟨sheetDiagonalAtom r z, by
        intro x hx
        simp [sheetDiagonalAtom, worldDiagonalClass, worldBasis, hx]⟩ :
        PureWorldHodge N N) =
      (⟨sheetDiagonalAtom
          (show Fin N from pureMirror (show Fin (min N N) from r)) z,
        by
          intro x hx
          simp [sheetDiagonalAtom, worldDiagonalClass, worldBasis, hx]⟩ :
        PureWorldHodge N N) := by
  apply Subtype.ext
  funext x
  simp [squarePureDual, sheetDiagonalAtom, worldDiagonalClass,
    worldBasis, worldDual_pureDiagonalState]

#check sheetDiagonalAtom_eq_smul_basis
#check sheetAtom_lefschetz_forward_exact
#check sheetAtom_forward_scalar_ne_zero
#check sheetAtom_lefschetz_forward_ne_zero
#check sheetAtom_lefschetz_wrong_time_zero
#check backward_request_reflects_forward
#check squarePureDual_sheetAtom

#print axioms sheetAtom_lefschetz_forward_exact
#print axioms sheetAtom_lefschetz_forward_ne_zero
#print axioms sheetAtom_lefschetz_wrong_time_zero
#print axioms backward_request_reflects_forward
#print axioms squarePureDual_sheetAtom

end GSTClassicalHodgeIntegralLefschetzTransport
