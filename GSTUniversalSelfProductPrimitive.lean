import Mathlib

/-!
# GST dimension-free universal self-product algebraic primitive

A completely uniform geometric construction for EVERY smooth
projective complex variety X, without assuming X is cellular,
K3, CM, abelian or a blow-up.

Given dim_C X = d and any ample algebraic hyperplane divisor h,
the two ACTUAL algebraic divisors on X×X are
a=pr_1^* h, b=pr_2^* h. Define the genuine rational algebraic
codimension-d cycle

    P_d(X,h) = sum_{j=0}^d (-1)^j a^(d-j) b^j.

The only ring-theoretic geometry needed is the independently known
dimension bound a^(d+1)=b^(d+1)=0. We prove the UNIFORM identity

 (a+b) P_d = a^(d+1) - (-b)^(d+1) = 0.

Nonzero on REAL X×X then follows by the independent projective
top-degree pairing with b^d:

    integral_(X×X) P_d cup b^d = (integral_X h^d)^2 > 0.

That final top-degree comparison is standard Künneth/projective
intersection geometry and is NOT formalized in this ring-only file.

This produces at least ONE true algebraic primitive class in the
middle cohomology of X×X for EVERY smooth projective X and all d.
It does NOT produce arbitrary primitive Hodge cycles on X itself,
nor all primitive classes on X×X. No target preimage or Hodge
surjectivity is supplied.
-/

set_option maxHeartbeats 6000000
noncomputable section

namespace GSTUniversalSelfProductPrimitive

variable {R : Type*} [CommRing R]

/-- An alternate-sign finite hyperplane combination of total degree d.
Recursive form is precisely sum_{j=0}^d (-1)^j a^(d-j)b^j,
without a geometric-source-dependent bound. -/
def universalPrimitive (a b : R) : Nat → R
  | 0 => 1
  | n + 1 => a^(n+1) - b * universalPrimitive a b n

@[simp]
theorem universalPrimitive_zero (a b : R) :
    universalPrimitive a b 0 = 1 := rfl

@[simp]
theorem universalPrimitive_succ (a b : R) (n : Nat) :
    universalPrimitive a b (n+1) =
      a^(n+1) - b * universalPrimitive a b n := rfl

/-- Exact telescoping identity valid over EVERY commutative ring,
uniformly in natural-number dimension d. -/
theorem universalPrimitive_telescopes
    (a b : R) (d : Nat) :
    (a+b) * universalPrimitive a b d =
      a^(d+1) - (-b)^(d+1) := by
  induction d with
  | zero =>
      simp [universalPrimitive]
  | succ d ih =>
      rw [universalPrimitive_succ]
      calc
        (a+b) * (a^(d+1) - b * universalPrimitive a b d) =
          (a+b)*a^(d+1) - b*((a+b)*universalPrimitive a b d) := by ring
        _ = (a+b)*a^(d+1) - b*(a^(d+1)-(-b)^(d+1)) := by rw [ih]
        _ = a^((d+1)+1) - (-b)^((d+1)+1) := by
          rw [pow_succ, pow_succ]
          ring

/-- Algebraic middle-primitivity of the universal self-product
hyperplane cycle follows from dimension-truncation alone.
There is no restriction on dimension d. -/
theorem universalPrimitive_in_middle_Lefschetz_kernel
    (a b : R) (d : Nat)
    (ha : a^(d+1) = 0) (hb : b^(d+1) = 0) :
    (a+b) * universalPrimitive a b d = 0 := by
  rw [universalPrimitive_telescopes, ha]
  rw [neg_pow]
  rw [hb]
  simp

/-- For every d, the proposed native-cycle expression is
a genuine finite integer-coefficient polynomial in the actual
two hyperplane divisors. There is no infinite formal sum or
limit and no denominator to rationally descend. -/
theorem universalPrimitive_succ_native
    (a b : R) (d : Nat) :
    universalPrimitive a b (d+1) +
      b * universalPrimitive a b d = a^(d+1) := by
  rw [universalPrimitive_succ]
  ring

#check universalPrimitive_telescopes
#check universalPrimitive_in_middle_Lefschetz_kernel
#check universalPrimitive_succ_native
#print axioms universalPrimitive_in_middle_Lefschetz_kernel

end GSTUniversalSelfProductPrimitive
