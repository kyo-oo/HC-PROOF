import Mathlib

/-!
# Exact nonlinear spectral source and its boundary defects

Uncompiled proof draft. In geometric K0, x,y are actual eigenline classes.
The two defect terms record the failure of the direct-sum and determinant
relations. Neither relation is silently imposed across singular branching.
-/

namespace GSTSpectralBoundaryDefect
variable {R : Type*} [CommRing R]

def sumDefect (x y : R) : R := 2-x-y
def determinantDefect (x y : R) : R := 1-x*y

theorem anti_square_exact_defect (x y : R) :
    (x-y)^2=(sumDefect x y)^2-4*sumDefect x y+4*determinantDefect x y := by
  unfold sumDefect determinantDefect
  ring

theorem anti_square_zero (x y : R) (hs : x+y=2) (hd : x*y=1) :
    (x-y)^2=0 := by
  calc
    (x-y)^2=(x+y)^2-4*(x*y) := by ring
    _ = 0 := by rw [hs,hd]; ring

theorem line_augmentation_square_zero (x y : R) (hs : x+y=2) (hd : x*y=1) :
    (x-1)^2=0 := by
  calc
    (x-1)^2=x*(x+y-2)-(x*y-1) := by ring
    _ = 0 := by rw [hs,hd]; ring

theorem repeated_anti_power_zero (x y : R) (hs : x+y=2) (hd : x*y=1) (k : ℕ) :
    (x-y)^(k+2)=0 := by
  rw [Nat.add_comm k 2,pow_add,anti_square_zero x y hs hd,zero_mul]

theorem power_of_square_zero_augmentation (x : R) (h : (x-1)^2=0) (n : ℕ) :
    x^n=1+(n : R)*(x-1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ,ih,Nat.cast_add,Nat.cast_one]
      calc
        (1+(n : R)*(x-1))*x =
            1+((n : R)+1)*(x-1)+(n : R)*(x-1)^2 := by ring
        _ = 1+((n : R)+1)*(x-1) := by rw [h]; ring

theorem all_power_sums_neutral (x y : R) (hs : x+y=2) (hd : x*y=1) (n : ℕ) :
    x^n+y^n=2 := by
  rw [power_of_square_zero_augmentation x (line_augmentation_square_zero x y hs hd),
    power_of_square_zero_augmentation y
      (line_augmentation_square_zero y x (by simpa [add_comm] using hs)
        (by simpa [mul_comm] using hd))]
  calc
    1+(n : R)*(x-1)+(1+(n : R)*(y-1))=2+(n : R)*(x+y-2) := by ring
    _ = 2 := by rw [hs]; ring

/-- Exact ideal containment, rather than an assertion that boundary defects vanish. -/
theorem anti_square_in_boundary_ideal (I : Ideal R) (x y : R)
    (hs : x+y-2∈I) (hd : x*y-1∈I) : (x-y)^2∈I := by
  have hidentity : (x-y)^2=(x+y-2)*(x+y+2)-4*(x*y-1) := by ring
  rw [hidentity]
  exact I.sub_mem (I.mul_mem_right _ hs) (I.mul_mem_left _ hd)

theorem restriction_kills_repeated_source {S : Type*} [CommRing S]
    (res : R →+* S) (x y : R)
    (hs : res x+res y=2) (hd : res x*res y=1) (k : ℕ) :
    res ((x-y)^(k+2))=0 := by
  rw [map_pow,map_sub]
  exact repeated_anti_power_zero (res x) (res y) hs hd k

/-- Mixed independent sources are intentionally not killed by the square law. -/
theorem mixed_product_exact (x y u v : R)
    (hs : x+y=2) (ht : u+v=2) :
    (x-y)*(u-v)=4*((x-1)*(u-1)) := by
  have hy : y=2-x := by linear_combination hs
  have hv : v=2-u := by linear_combination ht
  rw [hy,hv]
  ring

#print axioms anti_square_exact_defect
#print axioms anti_square_in_boundary_ideal
#print axioms all_power_sums_neutral
end GSTSpectralBoundaryDefect
