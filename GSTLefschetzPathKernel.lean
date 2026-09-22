import Mathlib
import GSTUniversalLefschetzDynamics
import GSTWorldPoincareDuality

/-!
# GST LEFSCHETZ PATH KERNEL

The dimension-free Lefschetz theorem proves the upper bound

    L^(A+B-1) = 0

on every positive A x B world.

This file identifies every coefficient of the wave launched from the origin.
After n Lefschetz steps, the value at (C,d) is exactly the number of lattice
paths from (0,0) to (C,d):

    (L^n delta_(0,0))(C,d)
      = choose(n,C)   if C+d=n,
        0             otherwise.

The proof is internal to GST and follows the one-step digit/carry predecessor
laws together with Pascal's recursion.

Consequences:
* the top-cell coefficient at n=A+B-2 is a positive binomial coefficient;
* therefore L^(A+B-2) is nonzero;
* combined with the universal upper bound, A+B-1 is the exact nilpotence
  ceiling of the total Lefschetz dynamics.
-/

set_option maxHeartbeats 20000000
set_option maxRecDepth 1000000

namespace GSTLefschetzPathKernel

open GSTWorldCosmology
open GSTGradedWorldAlgebra
open GSTUniversalLefschetzDynamics
open GSTWorldPoincareDuality

/-- Origin of a positive rectangular world. -/
def worldOrigin
    {A B : Nat} (hA : 0 < A) (hB : 0 < B) :
    WorldCell A B :=
  (⟨0,hA⟩, ⟨0,hB⟩)

/-- Delta class launched from the world origin. -/
def worldOriginBasis
    {A B : Nat} (hA : 0 < A) (hB : 0 < B) :
    WorldCoef A B :=
  worldBasis (worldOrigin hA hB)

/-- Exact value of the origin basis. -/
theorem worldOriginBasis_at
    {A B C d : Nat}
    (hA : 0 < A) (hB : 0 < B)
    (hC : C < A) (hd : d < B) :
    worldOriginBasis hA hB (⟨C,hC⟩,⟨d,hd⟩) =
      if C = 0 ∧ d = 0 then 1 else 0 := by
  unfold worldOriginBasis worldOrigin worldBasis
  by_cases h : C = 0 ∧ d = 0
  · rcases h with ⟨rfl,rfl⟩
    simp
  · have hne :
      (⟨C,hC⟩,⟨d,hd⟩) ≠
        ((⟨0,hA⟩,⟨0,hB⟩) : WorldCell A B) := by
      intro heq
      apply h
      constructor
      · exact congrArg (fun x => x.1.1) heq
      · exact congrArg (fun x => x.2.1) heq
    simp [h, hne]

/-- **EXACT LEFSCHETZ PATH KERNEL.**

Starting from the origin delta class, n polarizations reach exactly total
degree n, and the coefficient at carry coordinate C is choose(n,C). -/
theorem lefschetz_origin_path_formula
    {A B : Nat}
    (hA : 0 < A) (hB : 0 < B)
    (n C d : Nat) (hC : C < A) (hd : d < B) :
    (Nat.iterate worldLefschetz n (worldOriginBasis hA hB))
        (⟨C,hC⟩,⟨d,hd⟩)
      =
    if C+d = n then (n.choose C : ℤ) else 0 := by
  induction n generalizing C d with
  | zero =>
      rw [Function.iterate_zero_apply]
      rw [worldOriginBasis_at hA hB hC hd]
      by_cases hC0 : C = 0
      · subst C
        by_cases hd0 : d = 0
        · subst d
          simp
        · have hsum : 0 + d ≠ 0 := by omega
          simp [hd0, hsum]
      · have hsum : C + d ≠ 0 := by omega
        simp [hC0, hsum]
  | succ n ih =>
      rw [Function.iterate_succ', Function.comp_apply]
      unfold worldLefschetz
      by_cases hC0 : C = 0
      · subst C
        by_cases hd0 : d = 0
        · subst d
          rw [digitShift_one_zero
                (Nat.iterate worldLefschetz n (worldOriginBasis hA hB))
                0 hA hB]
          rw [carryShift_one_zero
                (Nat.iterate worldLefschetz n (worldOriginBasis hA hB))
                0 hA hB]
          simp
        · rw [digitShift_one_at
                (Nat.iterate worldLefschetz n (worldOriginBasis hA hB))
                0 d hA hd (by omega)]
          rw [carryShift_one_zero
                (Nat.iterate worldLefschetz n (worldOriginBasis hA hB))
                d hA hd]
          rw [ih 0 (d-1) hA (by omega)]
          by_cases hs : d = n+1
          · have hp : 0 + (d-1) = n := by omega
            simp [hs, hp]
          · have hp : 0 + (d-1) ≠ n := by omega
            have hs' : 0 + d ≠ n+1 := by omega
            simp [hp, hs']
      · by_cases hd0 : d = 0
        · subst d
          rw [digitShift_one_zero
                (Nat.iterate worldLefschetz n (worldOriginBasis hA hB))
                C hC hB]
          rw [carryShift_one_at
                (Nat.iterate worldLefschetz n (worldOriginBasis hA hB))
                C 0 hC hB (by omega)]
          rw [ih (C-1) 0 (by omega) hB]
          by_cases hs : C = n+1
          · have hp : (C-1) + 0 = n := by omega
            have hself : (n+1).choose C = 1 := by
              subst C
              simp
            simp [hp, hs, hself]
          · have hp : (C-1) + 0 ≠ n := by omega
            have hs' : C + 0 ≠ n+1 := by omega
            simp [hp, hs']
        · rw [digitShift_one_at
                (Nat.iterate worldLefschetz n (worldOriginBasis hA hB))
                C d hC hd (by omega)]
          rw [carryShift_one_at
                (Nat.iterate worldLefschetz n (worldOriginBasis hA hB))
                C d hC hd (by omega)]
          rw [ih C (d-1) hC (by omega)]
          rw [ih (C-1) d (by omega) hd]
          by_cases hs : C+d = n+1
          · have hdpre : C + (d-1) = n := by omega
            have hCpre : (C-1) + d = n := by omega
            simp [hdpre, hCpre, hs]
            have hchoose :=
              Nat.choose_succ_left n C (by omega)
            norm_cast
            omega
          · have hdpre : C + (d-1) ≠ n := by omega
            have hCpre : (C-1) + d ≠ n := by omega
            simp [hdpre, hCpre, hs]

/-- Top cell of a positive rectangular world. -/
def worldTopCell
    {A B : Nat} (hA : 0 < A) (hB : 0 < B) :
    WorldCell A B :=
  (⟨A-1, by omega⟩, ⟨B-1, by omega⟩)

/-- The last nonzero Lefschetz wave has an explicit positive top coefficient. -/
theorem lefschetz_origin_top_value
    {A B : Nat} (hA : 0 < A) (hB : 0 < B) :
    (Nat.iterate worldLefschetz (A+B-2) (worldOriginBasis hA hB))
        (worldTopCell hA hB)
      =
    ((A+B-2).choose (A-1) : ℤ) := by
  unfold worldTopCell
  rw [lefschetz_origin_path_formula hA hB]
  have hsum : (A-1) + (B-1) = A+B-2 := by omega
  simp [hsum]

/-- The top path coefficient is nonzero. -/
theorem lefschetz_origin_top_value_ne_zero
    {A B : Nat} (hA : 0 < A) (hB : 0 < B) :
    (Nat.iterate worldLefschetz (A+B-2) (worldOriginBasis hA hB))
        (worldTopCell hA hB) ≠ 0 := by
  rw [lefschetz_origin_top_value hA hB]
  have hle : A-1 ≤ A+B-2 := by omega
  have hpos := Nat.choose_pos hle
  exact_mod_cast (Nat.ne_of_gt hpos)

/-- **SHARPNESS OF THE UNIVERSAL LEFSCHETZ CEILING.**
The (A+B-2)-nd iterate is still globally nonzero. -/
theorem worldLefschetz_before_boundary_ne_zero
    {A B : Nat} (hA : 0 < A) (hB : 0 < B) :
    Nat.iterate worldLefschetz (A+B-2) (worldOriginBasis hA hB)
      ≠ fun _ => 0 := by
  intro hz
  have htop := congrFun hz (worldTopCell hA hB)
  exact lefschetz_origin_top_value_ne_zero hA hB htop

/-- The universal upper and lower bounds meet exactly: the total Lefschetz
nilpotence ceiling is A+B-1 on every positive rectangular world. -/
theorem worldLefschetz_nilpotence_is_sharp
    {A B : Nat} (hA : 0 < A) (hB : 0 < B) :
    Nat.iterate worldLefschetz (A+B-1) (worldOriginBasis hA hB)
        = fun _ => 0
    ∧
    Nat.iterate worldLefschetz (A+B-2) (worldOriginBasis hA hB)
        ≠ fun _ => 0 := by
  exact ⟨
    worldLefschetz_nilpotent hA hB (worldOriginBasis hA hB),
    worldLefschetz_before_boundary_ne_zero hA hB⟩

/-- Historical 4 x 3 world: the fifth iterate still reaches the top cell
with coefficient choose(5,3)=10, while the sixth iterate vanishes. -/
theorem hc_top_path_coefficient :
    (Nat.iterate worldLefschetz 5
        (worldOriginBasis (A:=4) (B:=3) (by decide) (by decide)))
        (worldTopCell (A:=4) (B:=3) (by decide) (by decide))
      = 10 := by
  norm_num [lefschetz_origin_top_value]

theorem hc_lefschetz_ceiling_sharp :
    Nat.iterate worldLefschetz 6
        (worldOriginBasis (A:=4) (B:=3) (by decide) (by decide))
        = fun _ => 0
    ∧
    Nat.iterate worldLefschetz 5
        (worldOriginBasis (A:=4) (B:=3) (by decide) (by decide))
        ≠ fun _ => 0 := by
  simpa using
    (worldLefschetz_nilpotence_is_sharp
      (A:=4) (B:=3) (by decide) (by decide))

/-- Capstone: exact path kernel plus sharp universal ceiling. -/
theorem lefschetz_path_kernel_crown :
    (∀ A B, 0 < A -> 0 < B ->
      ∀ n C d (hC : C < A) (hd : d < B),
        (Nat.iterate worldLefschetz n
          (worldOriginBasis (A:=A) (B:=B) (by assumption) (by assumption)))
          (⟨C,hC⟩,⟨d,hd⟩)
        =
        if C+d=n then (n.choose C : ℤ) else 0)
    ∧
    (∀ A B, 0 < A -> 0 < B ->
      Nat.iterate worldLefschetz (A+B-1)
          (worldOriginBasis (A:=A) (B:=B) (by assumption) (by assumption))
          = fun _ => 0
      ∧
      Nat.iterate worldLefschetz (A+B-2)
          (worldOriginBasis (A:=A) (B:=B) (by assumption) (by assumption))
          ≠ fun _ => 0) := by
  constructor
  · intro A B hA hB n C d hC hd
    exact lefschetz_origin_path_formula hA hB n C d hC hd
  · intro A B hA hB
    exact worldLefschetz_nilpotence_is_sharp hA hB

#check lefschetz_origin_path_formula
#check lefschetz_origin_top_value
#check worldLefschetz_before_boundary_ne_zero
#check worldLefschetz_nilpotence_is_sharp
#check hc_top_path_coefficient
#check hc_lefschetz_ceiling_sharp
#check lefschetz_path_kernel_crown

#print axioms lefschetz_origin_path_formula
#print axioms worldLefschetz_before_boundary_ne_zero
#print axioms worldLefschetz_nilpotence_is_sharp
#print axioms lefschetz_path_kernel_crown

end GSTLefschetzPathKernel
