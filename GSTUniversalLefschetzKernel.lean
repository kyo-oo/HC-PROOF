import Mathlib
import GSTUniversalLefschetzPathFormula

/-!
# GST UNIVERSAL LEFSCHETZ TRANSITION KERNEL

The universal path formula expands every Lefschetz power into all mixed
digit/carry paths.  This file closes the next layer: it evaluates that whole
path sum on the canonical world basis.

For arbitrary rectangular worlds, arbitrary source and target cells, and
arbitrary time n, a matrix coefficient of L^n is completely determined by
three pieces of native GST data:

* the target must lie in the source's forward digit/carry cone;
* n must equal the exact Manhattan depth between source and target;
* when both conditions hold, the coefficient is the corresponding binomial
  path multiplicity.

Thus every Lefschetz power has a closed transition kernel in every finite GST
world.  No fixed Fin 12 carrier, fixed exponent, or hand-written matrix occurs.
-/

set_option maxHeartbeats 20000000
set_option maxRecDepth 1000000

namespace GSTUniversalLefschetzKernel

open GSTWorldCosmology
open GSTWorldPoincareDuality
open GSTTruncatedWorldCohomologyRing
open GSTUniversalLefschetzPathFormula

/-- A target is causally forward of a source when neither native axis
moves backwards. -/
def worldForward
    {A B : Nat} (s t : WorldCell A B) : Prop :=
  s.1.1 ≤ t.1.1 ∧ s.2.1 ≤ t.2.1

/-- Native carry-axis distance from source to target. -/
def carryDistance
    {A B : Nat} (s t : WorldCell A B) : Nat :=
  t.1.1 - s.1.1

/-- Native digit-axis distance from source to target. -/
def digitDistance
    {A B : Nat} (s t : WorldCell A B) : Nat :=
  t.2.1 - s.2.1

/-- Total causal depth between two world cells. -/
def worldCausalDistance
    {A B : Nat} (s t : WorldCell A B) : Nat :=
  carryDistance s t + digitDistance s t

/-- **UNIVERSAL LEFSCHETZ TRANSITION KERNEL.**

Every matrix coefficient of every power of the universal Lefschetz class is
closed form.  A coefficient is zero outside the forward cone or at the wrong
time.  At the unique causal time it is the exact binomial number of mixed
digit/carry paths. -/
theorem worldAct_L_pow_basis_kernel
    (A B n : Nat) (s t : WorldCell A B) :
    worldAct A B ((L A B)^n) (worldBasis s) t =
      if hfuture : worldForward s t then
        if htime : n = worldCausalDistance s t then
          (n.choose (digitDistance s t) : ℤ)
        else 0
      else 0 := by
  classical
  rcases s with ⟨⟨Cs,hCs⟩,⟨ds,hds⟩⟩
  rcases t with ⟨⟨Ct,hCt⟩,⟨dt,hdt⟩⟩
  unfold worldForward worldCausalDistance carryDistance digitDistance
  rw [worldAct_L_pow_coordinate_formula]
  by_cases hfuture : Cs ≤ Ct ∧ ds ≤ dt
  · simp only [hfuture]
    by_cases htime : n = (Ct-Cs) + (dt-ds)
    · simp only [htime]
      rw [Finset.sum_eq_single (dt-ds)]
      · have hpath :
            dt-ds ≤ dt ∧ n-(dt-ds) ≤ Ct := by
          constructor
          · exact Nat.sub_le _ _
          · omega
        rw [dif_pos hpath]
        have hpred :
            ((⟨Ct-(n-(dt-ds)), by omega⟩,
              ⟨dt-(dt-ds), by omega⟩) : WorldCell A B) =
              (⟨Cs,hCs⟩,⟨ds,hds⟩) := by
          apply Prod.ext
          · apply Fin.ext
            omega
          · apply Fin.ext
            omega
        rw [hpred]
        simp [worldBasis]
      · intro m hm hne
        by_cases hpath : m ≤ dt ∧ n-m ≤ Ct
        · rw [dif_pos hpath]
          have hpred_ne :
              ((⟨Ct-(n-m), by omega⟩,
                ⟨dt-m, by omega⟩) : WorldCell A B) ≠
                (⟨Cs,hCs⟩,⟨ds,hds⟩) := by
            intro heq
            have hdEq :=
              congrArg (fun x : WorldCell A B => x.2.1) heq
            apply hne
            omega
          simp [worldBasis, hpred_ne]
        · simp [hpath]
      · intro hnot
        have hmem : dt-ds ∈ Finset.range (n+1) := by
          apply Finset.mem_range.mpr
          omega
        exact (hnot hmem).elim
    · simp only [htime]
      apply Finset.sum_eq_zero
      intro m hm
      by_cases hpath : m ≤ dt ∧ n-m ≤ Ct
      · rw [dif_pos hpath]
        have hmn : m ≤ n := by
          have hm' := Finset.mem_range.mp hm
          omega
        have hpred_ne :
            ((⟨Ct-(n-m), by omega⟩,
              ⟨dt-m, by omega⟩) : WorldCell A B) ≠
              (⟨Cs,hCs⟩,⟨ds,hds⟩) := by
          intro heq
          have hCEq :=
            congrArg (fun x : WorldCell A B => x.1.1) heq
          have hdEq :=
            congrArg (fun x : WorldCell A B => x.2.1) heq
          apply htime
          omega
        simp [worldBasis, hpred_ne]
      · simp [hpath]
  · simp only [hfuture]
    have hout : Ct < Cs ∨ dt < ds := by
      omega
    apply Finset.sum_eq_zero
    intro m hm
    by_cases hpath : m ≤ dt ∧ n-m ≤ Ct
    · rw [dif_pos hpath]
      have hpred_ne :
          ((⟨Ct-(n-m), by omega⟩,
            ⟨dt-m, by omega⟩) : WorldCell A B) ≠
            (⟨Cs,hCs⟩,⟨ds,hds⟩) := by
        intro heq
        have hCEq :=
          congrArg (fun x : WorldCell A B => x.1.1) heq
        have hdEq :=
          congrArg (fun x : WorldCell A B => x.2.1) heq
        rcases hout with hCout | hdout
        · have hle : Ct-(n-m) ≤ Ct := Nat.sub_le _ _
          omega
        · have hle : dt-m ≤ dt := Nat.sub_le _ _
          omega
      simp [worldBasis, hpred_ne]
    · simp [hpath]

/-- Exact coefficient at the unique causal time. -/
theorem worldAct_L_pow_basis_exact
    {A B n : Nat} (s t : WorldCell A B)
    (hfuture : worldForward s t)
    (htime : n = worldCausalDistance s t) :
    worldAct A B ((L A B)^n) (worldBasis s) t =
      (n.choose (digitDistance s t) : ℤ) := by
  rw [worldAct_L_pow_basis_kernel]
  simp [hfuture, htime]

/-- Every wrong-time matrix coefficient vanishes even inside the forward
causal cone. -/
theorem worldAct_L_pow_basis_wrong_time_zero
    {A B n : Nat} (s t : WorldCell A B)
    (hfuture : worldForward s t)
    (htime : n ≠ worldCausalDistance s t) :
    worldAct A B ((L A B)^n) (worldBasis s) t = 0 := by
  rw [worldAct_L_pow_basis_kernel]
  simp [hfuture, htime]

/-- No Lefschetz path propagates backwards along either native world axis. -/
theorem worldAct_L_pow_basis_outside_future_zero
    {A B n : Nat} (s t : WorldCell A B)
    (hfuture : ¬ worldForward s t) :
    worldAct A B ((L A B)^n) (worldBasis s) t = 0 := by
  rw [worldAct_L_pow_basis_kernel]
  simp [hfuture]

/-- A nonzero matrix coefficient forces both causal reachability and the
unique exact propagation time. -/
theorem nonzero_lefschetz_transition_forces_causality
    {A B n : Nat} (s t : WorldCell A B)
    (hne :
      worldAct A B ((L A B)^n) (worldBasis s) t ≠ 0) :
    worldForward s t ∧ n = worldCausalDistance s t := by
  constructor
  · by_contra hfuture
    have hz :=
      worldAct_L_pow_basis_outside_future_zero
        (A:=A) (B:=B) (n:=n) s t hfuture
    exact hne hz
  · have hfuture : worldForward s t := by
      by_contra hfuture
      have hz :=
        worldAct_L_pow_basis_outside_future_zero
          (A:=A) (B:=B) (n:=n) s t hfuture
      exact hne hz
    by_contra htime
    have hz :=
      worldAct_L_pow_basis_wrong_time_zero
        (A:=A) (B:=B) (n:=n) s t hfuture htime
    exact hne hz

/-- Origin-to-cell propagation is the universal binomial kernel.  The earlier
bottom-to-top coefficient is just the maximal-degree specialization. -/
theorem origin_to_cell_kernel
    (A B C d : Nat) (hC : C < A) (hd : d < B) :
    worldAct A B ((L A B)^(C+d))
      (worldBasis
        (⟨0, by omega⟩, ⟨0, by omega⟩))
      (⟨C,hC⟩,⟨d,hd⟩) =
        ((C+d).choose d : ℤ) := by
  apply worldAct_L_pow_basis_exact
  · constructor <;> simp [worldForward]
  · unfold worldCausalDistance carryDistance digitDistance
    simp

/-- The historical 4 x 3 top transition is one entry of the universal
transition kernel. -/
theorem hc_origin_to_top_kernel :
    worldAct 4 3 ((L 4 3)^5)
      (worldBasis
        (⟨0, by decide⟩, ⟨0, by decide⟩))
      (⟨3, by decide⟩, ⟨2, by decide⟩) = 10 := by
  simpa using origin_to_cell_kernel 4 3 3 2 (by decide) (by decide)

/-- Capstone: every matrix entry is classified, every nonzero transition has
a unique causal time, and the historical coefficient 10 is absorbed as one
special case. -/
theorem universal_lefschetz_kernel_crown :
    (∀ A B n (s t : WorldCell A B),
      worldAct A B ((L A B)^n) (worldBasis s) t =
        if hfuture : worldForward s t then
          if htime : n = worldCausalDistance s t then
            (n.choose (digitDistance s t) : ℤ)
          else 0
        else 0)
    ∧ (∀ A B n (s t : WorldCell A B),
      worldAct A B ((L A B)^n) (worldBasis s) t ≠ 0 →
        worldForward s t ∧ n = worldCausalDistance s t)
    ∧ worldAct 4 3 ((L 4 3)^5)
        (worldBasis
          (⟨0, by decide⟩, ⟨0, by decide⟩))
        (⟨3, by decide⟩, ⟨2, by decide⟩) = 10 := by
  exact ⟨
    worldAct_L_pow_basis_kernel,
    fun A B n s t h =>
      nonzero_lefschetz_transition_forces_causality s t h,
    hc_origin_to_top_kernel⟩

#check worldForward
#check carryDistance
#check digitDistance
#check worldCausalDistance
#check worldAct_L_pow_basis_kernel
#check worldAct_L_pow_basis_exact
#check worldAct_L_pow_basis_wrong_time_zero
#check worldAct_L_pow_basis_outside_future_zero
#check nonzero_lefschetz_transition_forces_causality
#check origin_to_cell_kernel
#check hc_origin_to_top_kernel
#check universal_lefschetz_kernel_crown

#print axioms worldAct_L_pow_basis_kernel
#print axioms nonzero_lefschetz_transition_forces_causality
#print axioms origin_to_cell_kernel
#print axioms universal_lefschetz_kernel_crown


/-! ## The exact kernel on the unbounded grid -/
open GSTUniversalLefschetzCosmology

def cosmicBasis (s : CosmicCell) : CompletedCosmos := fun t => if t=s then 1 else 0

theorem cosmicLefschetz_kernel (n : ℕ) (s t : CosmicCell) :
    (cosmicLefschetz^n) (cosmicBasis s) t =
      if s.1 ≤ t.1 ∧ s.2 ≤ t.2 then
        if n = (t.1-s.1)+(t.2-s.2) then (n.choose (t.2-s.2) : ℤ) else 0
      else 0 := by
  let A := max s.1 t.1 + 1
  let B := max s.2 t.2 + 1
  let sf : WorldCell A B := (⟨s.1, by dsimp [A]; omega⟩,⟨s.2, by dsimp [B]; omega⟩)
  let tf : WorldCell A B := (⟨t.1, by dsimp [A]; omega⟩,⟨t.2, by dsimp [B]; omega⟩)
  have hb : observe A B (cosmicBasis s) = worldBasis sf := by
    funext c
    simp [observe, cosmicBasis, worldBasis, sf, Prod.ext_iff, Fin.ext_iff]
  have ho := congrFun (worldAct_is_cosmic_observation A B n (cosmicBasis s)) tf
  rw [hb, worldAct_L_pow_basis_kernel] at ho
  simpa [observe, worldForward, worldCausalDistance, carryDistance, digitDistance, sf, tf]
    using ho.symm

/-- A unit source propagates at every natural time: there is no global ceiling. -/
theorem cosmicLefschetz_never_extinguishes (n : ℕ) :
    (cosmicLefschetz^n) (cosmicBasis (0,0)) (0,n) = 1 := by
  simp [cosmicLefschetz_kernel]

theorem cosmicLefschetz_not_nilpotent : ¬ IsNilpotent cosmicLefschetz := by
  rintro ⟨n, hn⟩
  have h := cosmicLefschetz_never_extinguishes n
  rw [hn] at h
  norm_num at h

#print axioms cosmicLefschetz_kernel
#print axioms cosmicLefschetz_not_nilpotent

end GSTUniversalLefschetzKernel
