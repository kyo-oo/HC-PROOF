import Mathlib
import GSTUniversalLefschetzPathFormula
import GSTWorldPoincareDuality

/-!
# GST UNIVERSAL LEFSCHETZ BASIS PATHS

This layer turns the universal path expansion into exact matrix-entry data.

For a source basis state (C,d), an n-step Lefschetz evolution has one
possible coefficient for every split m + (n-m) = n:

* m digit-axis moves,
* n-m carry-axis moves.

At the corresponding target state the coefficient is exactly Nat.choose n m.
Every target not reached by such a path has coefficient zero.

This is the direct parent theorem behind all complementary-degree Lefschetz
matrices, including the historical 4 x 3 determinants 10, 6 and 1.
-/

set_option maxHeartbeats 20000000
set_option maxRecDepth 1000000

namespace GSTUniversalLefschetzBasisPaths

open GSTWorldCosmology
open GSTWorldPoincareDuality
open GSTTruncatedWorldCohomologyRing
open GSTUniversalLefschetzPathFormula
open scoped BigOperators

/-- Exact target cell reached from (C,d) by an n-step path with m
digit moves and n-m carry moves. -/
def pathTarget
    {A B : Nat}
    (n m C d : Nat)
    (hC : C < A) (hd : d < B)
    (hm : m ≤ n)
    (hcarry : C + (n-m) < A)
    (hdigit : d + m < B) :
    WorldCell A B :=
  (⟨C + (n-m), hcarry⟩, ⟨d + m, hdigit⟩)

/-- Exact basis-path coefficient. -/
theorem lefschetz_basis_path_coefficient
    {A B : Nat}
    (n m C d : Nat)
    (hC : C < A) (hd : d < B)
    (hm : m ≤ n)
    (hcarry : C + (n-m) < A)
    (hdigit : d + m < B) :
    worldAct A B ((L A B)^n)
      (worldBasis (⟨C,hC⟩,⟨d,hd⟩))
      (pathTarget n m C d hC hd hm hcarry hdigit)
      = (n.choose m : ℤ) := by
  unfold pathTarget
  rw [worldAct_L_pow_coordinate_formula]
  classical
  rw [Finset.sum_eq_single m]
  · have hm_digit : m ≤ d + m := by omega
    have hm_carry : n-m ≤ C + (n-m) := by omega
    simp [hm_digit, hm_carry, worldBasis, hm]
  · intro q hq hqm
    by_cases hpath :
        q ≤ d + m ∧ n-q ≤ C + (n-m)
    · have hne :
          (⟨C + (n-m) - (n-q), by omega⟩,
            ⟨d + m - q, by omega⟩ : WorldCell A B) ≠
          (⟨C,hC⟩,⟨d,hd⟩) := by
        intro hs
        have hdEq := congrArg (fun x : WorldCell A B => x.2.1) hs
        omega
      simp [hpath, worldBasis, hne]
    · simp [hpath]
  · intro hnot
    have hmrange : m < n+1 := by omega
    exact (hnot (Finset.mem_range.mpr hmrange)).elim

/-- A target which cannot be represented by any admissible split of the
n steps has zero coefficient from the chosen source basis cell. -/
theorem lefschetz_basis_unreachable_zero
    {A B : Nat}
    (n C d : Nat)
    (hC : C < A) (hd : d < B)
    (target : WorldCell A B)
    (hunreachable :
      ∀ m, m ≤ n ->
        target.1.1 ≠ C + (n-m) ∨
        target.2.1 ≠ d + m) :
    worldAct A B ((L A B)^n)
      (worldBasis (⟨C,hC⟩,⟨d,hd⟩)) target = 0 := by
  rw [worldAct_L_pow_paths_at]
  apply Finset.sum_eq_zero
  intro m hmrange
  have hm : m ≤ n := by omega
  by_cases hdm : m ≤ target.2.1
  · by_cases hCm : n-m ≤ target.1.1
    · have hne :
          (⟨target.1.1 - (n-m), by omega⟩,
            ⟨target.2.1 - m, by omega⟩ : WorldCell A B) ≠
          (⟨C,hC⟩,⟨d,hd⟩) := by
        intro hs
        have hCeq := congrArg (fun x : WorldCell A B => x.1.1) hs
        have hdeq := congrArg (fun x : WorldCell A B => x.2.1) hs
        have hreach := hunreachable m hm
        apply hreach.elim
        · intro hbad
          apply hbad
          omega
        · intro hbad
          apply hbad
          omega
      simp [digitShiftN, carryShiftN, hdm, hCm, worldBasis, hne]
    · simp [digitShiftN, carryShiftN, hdm, hCm]
  · simp [digitShiftN, hdm]

/-- The basis path is unique: two admissible splits reaching the same target
must use the same number of digit moves. -/
theorem pathTarget_split_unique
    {A B : Nat}
    {n m q C d : Nat}
    {hC : C < A} {hd : d < B}
    {hm : m ≤ n} {hq : q ≤ n}
    {hcarryM : C + (n-m) < A}
    {hdigitM : d + m < B}
    {hcarryQ : C + (n-q) < A}
    {hdigitQ : d + q < B}
    (h :
      pathTarget n m C d hC hd hm hcarryM hdigitM =
      pathTarget n q C d hC hd hq hcarryQ hdigitQ) :
    m = q := by
  have hdEq := congrArg (fun x : WorldCell A B => x.2.1) h
  simp [pathTarget] at hdEq
  omega

/-- Historical bottom-to-top coefficient is one instance of the basis-path
kernel: five steps, two digit moves, three carry moves. -/
theorem hc_basis_bottom_to_top :
    worldAct 4 3 ((L 4 3)^5)
      (worldBasis (⟨0,by decide⟩,⟨0,by decide⟩))
      (⟨3,by decide⟩,⟨2,by decide⟩)
      = 10 := by
  simpa using
    (lefschetz_basis_path_coefficient
      (A:=4) (B:=3)
      5 2 0 0
      (by decide) (by decide)
      (by decide) (by decide) (by decide))

#check pathTarget
#check lefschetz_basis_path_coefficient
#check lefschetz_basis_unreachable_zero
#check pathTarget_split_unique
#check hc_basis_bottom_to_top

#print axioms lefschetz_basis_path_coefficient
#print axioms lefschetz_basis_unreachable_zero
#print axioms pathTarget_split_unique
#print axioms hc_basis_bottom_to_top

end GSTUniversalLefschetzBasisPaths
