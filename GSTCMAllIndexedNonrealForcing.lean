import GSTCMNumberManipulationTrace

/-!
# Every corrected Gaussian CM NM index creates a nonreal isogeny

Previous exact mathematics in the research record derived
  u_n=(1+i)^n-i^(n+1) for n>=1,
and demonstrated that the Gaussian-imaginary component NEVER
vanishes at ANY index. This file transfers the ALL-INDEX
arithmetic claim from a document into a Lean kernel theorem.

The concrete native geometric implication is that multiplication
by u_n is a nontrivial imaginary-CM elliptic isogeny and that
the genuine graph intersection determinant is -4*Im(u_n)^2,
which is strictly negative. The algebraicity of those projective
graph divisors and the intersection class comparison remain
external elliptic-geometry theorems, not fabricated Lean axioms.

No Hodge (p,p) target class is supplied as an input.
-/

set_option maxHeartbeats 20000000
noncomputable section
namespace GSTCMNumberManipulationTrace

/-- Pair arithmetic respects associativity of Gaussian multiplication. -/
theorem cmMul_assoc (x y z : CMQ) :
    cmMul (cmMul x y) z = cmMul x (cmMul y z) := by
  rcases x with ⟨a,b⟩
  rcases y with ⟨c,d⟩
  rcases z with ⟨e,f⟩
  simp [cmMul]
  ring

theorem cmPow_add (z : CMQ) (m n : ℕ) :
    cmPow z (m+n) = cmMul (cmPow z m) (cmPow z n) := by
  induction m with
  | zero =>
      simp [cmPow,cmMul]
  | succ m ih =>
      change cmMul z (cmPow z (m+n)) =
        cmMul (cmMul z (cmPow z m)) (cmPow z n)
      rw [ih]
      exact (cmMul_assoc z _ _).symm

/-- (1+i)^(4k) = (-4)^k exactly over Gaussian rationals. -/
theorem cmPow_one_plus_i_four (k : ℕ) :
    cmPow ((1,1):CMQ) (4*k) = (((-4:ℚ)^k), 0) := by
  induction k with
  | zero =>
      norm_num [cmPow]
  | succ k ih =>
      have he : 4*(k+1)=4*k+4 := by omega
      rw [he, cmPow_add, ih]
      norm_num [cmPow,cmMul,pow_succ]
      apply Prod.ext <;> dsimp <;> ring

/-- i^(4k)=1 exactly. -/
theorem cmPow_i_four (k : ℕ) :
    cmPow ((0,1):CMQ) (4*k) = (1,0) := by
  induction k with
  | zero => norm_num [cmPow]
  | succ k ih =>
      have he : 4*(k+1)=4*k+4 := by omega
      rw [he,cmPow_add,ih]
      norm_num [cmPow,cmMul]

/-- First Gaussian imaginary component of the contributor's corrected
NM index in each four-index residue block. -/
theorem cmIndexedDenominator_imag_four_blocks (k : ℕ) :
    (cmIndexedDenominator ((1,1):CMQ) ((0,1):CMQ) (4*k)).2 =
      (-4:ℚ)^k ∧
    (cmIndexedDenominator ((1,1):CMQ) ((0,1):CMQ) (4*k+1)).2 =
      2 * (-4:ℚ)^k+1 ∧
    (cmIndexedDenominator ((1,1):CMQ) ((0,1):CMQ) (4*k+2)).2 =
      2 * (-4:ℚ)^k ∧
    (cmIndexedDenominator ((1,1):CMQ) ((0,1):CMQ) (4*k+3)).2 = -1 := by
  have hgauss := cmPow_one_plus_i_four k
  have hi := cmPow_i_four k
  have hh (r : ℕ) :
      cmPow ((1,1):CMQ) (4*k+r) =
        cmMul (((-4:ℚ)^k),0) (cmPow ((1,1):CMQ) r) := by
    rw [cmPow_add, hgauss]
  have hhi (r : ℕ) :
      cmPow ((0,1):CMQ) (4*k+r) =
        cmPow ((0,1):CMQ) r := by
    rw [cmPow_add,hi]
    rcases cmPow ((0,1):CMQ) r with ⟨a,b⟩
    simp [cmMul]
  constructor
  · have hs1:=hh 1
    have hs2:=hhi 2
    norm_num [cmIndexedDenominator,cmSub,cmPow,cmMul] at *
    have : 4*k+1 = (4*k)+1 := by omega
    have : 4*k+2 = (4*k)+2 := by omega
    simp [hh, hhi, cmIndexedDenominator,cmSub,cmPow,cmMul]
  constructor
  · simp [hh, hhi, cmIndexedDenominator,cmSub,cmPow,cmMul]
    ring
  constructor
  · simp [hh, hhi, cmIndexedDenominator,cmSub,cmPow,cmMul]
    ring
  · simp [hh, hhi, cmIndexedDenominator,cmSub,cmPow,cmMul]
    ring

/-- Arithmetic four-block decomposition: EVERY positive index is
one of four residue classes. -/
theorem cmIndexedDenominator_nonreal_every_index (m : ℕ) :
    (cmIndexedDenominator ((1,1):CMQ) ((0,1):CMQ) m).2 ≠ 0 := by
  obtain ⟨k,r,hr,hm⟩ :
      ∃ k r : ℕ, r < 4 ∧ m = 4*k+r := by
    refine ⟨m/4,m%4,by omega,by omega⟩
  have hblocks := cmIndexedDenominator_imag_four_blocks k
  have hpower : (-4:ℚ)^k ≠ 0 := pow_ne_zero _ (by norm_num)
  interval_cases r
  · subst m
    simpa using hpower
  · subst m
    have hodd : 2*(-4:ℚ)^k+1 ≠ 0 := by
      intro hz
      have hzInt : 2*(-4:ℤ)^k+1 = 0 := by
        exact_mod_cast hz
      omega
    simpa [hblocks.2.1] using hodd
  · subst m
    exact (by simpa [hblocks.2.2.1] using mul_ne_zero (by norm_num : (2:ℚ) ≠ 0) hpower)
  · subst m
    norm_num [hblocks.2.2.2]

#check cmIndexedDenominator_nonreal_every_index
#print axioms cmIndexedDenominator_nonreal_every_index
end GSTCMNumberManipulationTrace
