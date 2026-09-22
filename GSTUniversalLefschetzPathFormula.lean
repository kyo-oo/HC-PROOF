import Mathlib
import GSTTruncatedWorldCohomologyRing

/-!
# GST UNIVERSAL LEFSCHETZ PATH FORMULA

The upgraded HC cosmology already has:

* arbitrary rectangular worlds;
* commuting native axis operators H and V;
* the quotient cohomology ring Z[H,V]/(H^B,V^A);
* the universal Lefschetz class L = H+V;
* dimension-derived nilpotence L^(A+B-1)=0.

This file adds the missing exact path calculus.

Every n-step Lefschetz evolution is the sum of all mixed digit/carry paths,
with multiplicity given by the binomial coefficient.  This is the parent law
behind every fixed complementary-power matrix in the historical 4 x 3 crown.

No fixed Fin 12 carrier and no interval case split appears.
-/

set_option maxHeartbeats 20000000
set_option maxRecDepth 1000000

namespace GSTUniversalLefschetzPathFormula

open GSTWorldCosmology
open GSTUniversalLefschetzCosmology
open GSTTruncatedWorldCohomologyRing
open scoped BigOperators

variable {A B : Nat}

/-! ## 1. Ring-level path expansion -/

/-- **UNIVERSAL RING BINOMIAL LAW.**
Every power of the universal Lefschetz class expands into all mixed
H/V paths with exact binomial multiplicity. -/
theorem L_pow_expansion (A B n : Nat) :
    (L A B)^n =
      ∑ m ∈ Finset.range (n+1),
        (H A B)^m * (V A B)^(n-m) *
          (n.choose m : WorldCohomologyRing A B) := by
  exact (Commute.all (H A B) (V A B)).add_pow n

/-- Terms which cross either rectangular wall vanish in the quotient ring
representation. -/
theorem L_path_term_acts_zero
    (A B n m : Nat)
    (g : WorldCoef A B)
    (hwall : B ≤ m ∨ A ≤ n-m) :
    worldAct A B
      ((H A B)^m * (V A B)^(n-m) *
        (n.choose m : WorldCohomologyRing A B)) g = 0 := by
  rw [worldAct_mul]
  have hzero :
      worldAct A B ((H A B)^m * (V A B)^(n-m))
        (worldAct A B (n.choose m : WorldCohomologyRing A B) g) = 0 := by
    rw [worldAct_monomial]
    exact mixed_boundary_extinction _ (by
      rcases hwall with hm | hn
      · exact Or.inr hm
      · exact Or.inl hn)
  exact hzero

/-! ## 2. Operator-level exact path calculus -/

/-- Quotient-ring powers act exactly as powers of the native Lefschetz
endomorphism. -/
theorem worldAct_L_pow_eq_endo
    (A B n : Nat) (g : WorldCoef A B) :
    worldAct A B ((L A B)^n) g =
      ((lefschetzEndo A B)^n) g := by
  induction n generalizing g with
  | zero =>
      simp [worldAct_one]
  | succ n ih =>
      rw [pow_succ, worldAct_mul, worldAct_L, ih]
      rw [pow_succ, Module.End.mul_apply]

/-- **UNIVERSAL LEFSCHETZ PATH FORMULA.**
The n-th Lefschetz power is the exact sum of all paths containing m digit
steps and n-m carry steps. -/
theorem worldAct_L_pow_paths
    (A B n : Nat) (g : WorldCoef A B) :
    worldAct A B ((L A B)^n) g =
      ∑ m ∈ Finset.range (n+1),
        (n.choose m : ℤ) •
          digitShiftN m (carryShiftN (n-m) g) := by
  rw [worldAct_L_pow_eq_endo]
  rw [lefschetz_binomial]
  simp only [Module.End.mul_apply, digitEndo_pow_apply,
    carryEndo_pow_apply]
  rfl

/-- Pointwise form of the universal path formula. -/
theorem worldAct_L_pow_paths_at
    (A B n : Nat) (g : WorldCoef A B)
    (c : WorldCell A B) :
    worldAct A B ((L A B)^n) g c =
      ∑ m ∈ Finset.range (n+1),
        (n.choose m : ℤ) *
          digitShiftN m (carryShiftN (n-m) g) c := by
  have h := congrFun (worldAct_L_pow_paths A B n g) c
  simpa using h

/-- Exact surviving-path formula at one coordinate.  A path contributes
iff the evaluation cell has enough digit depth for its m digit steps and
enough carry depth for its n-m carry steps. -/
theorem worldAct_L_pow_coordinate_formula
    (A B n : Nat) (g : WorldCoef A B)
    (C d : Nat) (hC : C < A) (hd : d < B) :
    worldAct A B ((L A B)^n) g (⟨C,hC⟩,⟨d,hd⟩) =
      ∑ m ∈ Finset.range (n+1),
        if hpath : m ≤ d ∧ n-m ≤ C then
          (n.choose m : ℤ) *
            g (⟨C-(n-m), by omega⟩, ⟨d-m, by omega⟩)
        else 0 := by
  rw [worldAct_L_pow_paths_at]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hpath : m ≤ d ∧ n-m ≤ C
  · rcases hpath with ⟨hdm,hCm⟩
    simp [digitShiftN, carryShiftN, hdm, hCm]
  · by_cases hdm : m ≤ d
    · have hCm : ¬ n-m ≤ C := by
        intro h
        exact hpath ⟨hdm,h⟩
      simp [digitShiftN, carryShiftN, hdm, hCm]
    · simp [digitShiftN, hdm]

/-- Below n total degree there are no surviving n-step paths.  This
recovers the universal degree-descent theorem directly from path calculus. -/
theorem path_formula_zero_below_degree
    (A B n : Nat) (g : WorldCoef A B)
    (C d : Nat) (hC : C < A) (hd : d < B)
    (hdeg : C+d < n) :
    worldAct A B ((L A B)^n) g (⟨C,hC⟩,⟨d,hd⟩) = 0 := by
  rw [worldAct_L_pow_coordinate_formula]
  apply Finset.sum_eq_zero
  intro m hm
  have hnot : ¬ (m ≤ d ∧ n-m ≤ C) := by
    intro h
    rcases h with ⟨hdm,hCm⟩
    omega
  simp [hnot]

/-- At the exact boundary degree C+d=n, only one path can survive, and its
coefficient is the corresponding binomial coefficient. -/
theorem path_formula_exact_boundary
    (A B C d : Nat) (hC : C < A) (hd : d < B)
    (g : WorldCoef A B) :
    worldAct A B ((L A B)^(C+d)) g (⟨C,hC⟩,⟨d,hd⟩) =
      ((C+d).choose d : ℤ) * g (⟨0,hC⟩,⟨0,hd⟩) := by
  rw [worldAct_L_pow_coordinate_formula]
  classical
  rw [Finset.sum_eq_single d]
  · simp
  · intro m hm hmd
    have hnot : ¬ (m ≤ d ∧ C+d-m ≤ C) := by
      intro h
      rcases h with ⟨hmle,hcarry⟩
      have : d ≤ m := by omega
      exact hmd (Nat.le_antisymm this hmle)
    simp [hnot]
  · intro hnot
    have : d < C+d+1 := by omega
    exact (hnot (Finset.mem_range.mpr this)).elim

/-- The historical top-cell coefficient in the 4 x 3 world is therefore
the binomial multiplicity choose(5,2)=10. -/
theorem hc_bottom_to_top_coefficient
    (g : WorldCoef 4 3) :
    worldAct 4 3 ((L 4 3)^5) g (⟨3,by decide⟩,⟨2,by decide⟩) =
      10 * g (⟨0,by decide⟩,⟨0,by decide⟩) := by
  simpa using
    (path_formula_exact_boundary
      4 3 3 2 (by decide) (by decide) g)

/-- Capstone: ring expansion, path expansion, exact coordinate formula,
and historical 10-fold top coefficient are all one theorem family. -/
theorem universal_lefschetz_path_crown :
    (∀ A B n,
      (L A B)^n =
        ∑ m ∈ Finset.range (n+1),
          (H A B)^m * (V A B)^(n-m) *
            (n.choose m : WorldCohomologyRing A B))
    ∧ (∀ A B n (g : WorldCoef A B),
      worldAct A B ((L A B)^n) g =
        ∑ m ∈ Finset.range (n+1),
          (n.choose m : ℤ) •
            digitShiftN m (carryShiftN (n-m) g))
    ∧ (∀ g : WorldCoef 4 3,
      worldAct 4 3 ((L 4 3)^5) g
        (⟨3,by decide⟩,⟨2,by decide⟩) =
        10 * g (⟨0,by decide⟩,⟨0,by decide⟩)) := by
  exact ⟨L_pow_expansion, worldAct_L_pow_paths,
    hc_bottom_to_top_coefficient⟩

#check L_pow_expansion
#check L_path_term_acts_zero
#check worldAct_L_pow_eq_endo
#check worldAct_L_pow_paths
#check worldAct_L_pow_paths_at
#check worldAct_L_pow_coordinate_formula
#check path_formula_zero_below_degree
#check path_formula_exact_boundary
#check hc_bottom_to_top_coefficient
#check universal_lefschetz_path_crown

#print axioms L_pow_expansion
#print axioms worldAct_L_pow_paths
#print axioms worldAct_L_pow_coordinate_formula
#print axioms path_formula_exact_boundary
#print axioms hc_bottom_to_top_coefficient
#print axioms universal_lefschetz_path_crown

end GSTUniversalLefschetzPathFormula
