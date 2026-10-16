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


/-! ## Functorial and homogeneous GST primitive conservation laws

In actual projective intersection rings these are independent
mathematical identities: the universal primitive respects
all ring-functorial pullbacks (when the cup-product comparison
is established) and rescales homogeneously under common
ample-class rescaling. Neither law asserts arbitrary Hodge
surjectivity.
-/

/-- Exact homogeneous degree-d law for the integer GST primitive.
This is an all-dimensional strengthening beyond nilpotence. -/
theorem universalPrimitive_homogeneous
    (a b t : R) (d : Nat) :
    universalPrimitive (t*a) (t*b) d =
      t^d * universalPrimitive a b d := by
  induction d with
  | zero => simp [universalPrimitive]
  | succ d ih =>
      rw [universalPrimitive_succ, universalPrimitive_succ, ih, mul_pow, pow_succ]
      ring

/-- Naturality under EVERY commutative-ring homomorphism.
The GST primitive polynomial has no representation-dependent
or recoordination-specific correction term. -/
theorem universalPrimitive_natural
    {S : Type*} [CommRing S] (f : R →+* S)
    (a b : R) (d : Nat) :
    f (universalPrimitive a b d) =
      universalPrimitive (f a) (f b) d := by
  induction d with
  | zero => simp [universalPrimitive]
  | succ d ih =>
      rw [universalPrimitive_succ, map_sub, map_mul, map_pow,
          ih, universalPrimitive_succ]

/-- The primitive constraint is conserved under any ring
homomorphism preserving the two nilpotence bounds. -/
theorem universalPrimitive_natural_and_primitive
    {S : Type*} [CommRing S] (f : R →+* S)
    (a b : R) (d : Nat)
    (ha : a^(d+1)=0) (hb : b^(d+1)=0) :
    ((f a)+(f b)) *
      f (universalPrimitive a b d) = 0 := by
  rw [universalPrimitive_natural]
  apply universalPrimitive_in_middle_Lefschetz_kernel
  · rw [← map_pow, ha, map_zero]
  · rw [← map_pow, hb, map_zero]

#check universalPrimitive_homogeneous
#check universalPrimitive_natural_and_primitive
#print axioms universalPrimitive_natural_and_primitive



/-! ## Exact primitive top-degree pairing and nonvanishing

Before this upgrade, the file proved middle Lefschetz primitivity
but referred to projective top-degree nonvanishing only in its
prose. These new theorems close that RING-THEORETIC step for every
dimension, leaving only the separately stated positive projective
intersection pairing required to instantiate it on a real X.
-/

/-- For EVERY d in EVERY commutative ring with b^(d+1)=0, the
universal GST primitive has exact TOP pairing a^d b^d.
In real projective X×X this pairs with the other factor's
hyperplane top class, detecting a genuine nonzero primitive. -/
theorem universalPrimitive_top_pairing
    (a b : R) (d : Nat) (hb : b^(d+1) = 0) :
    universalPrimitive a b d * b^d = a^d * b^d := by
  cases d with
  | zero =>
    simp [universalPrimitive]
  | succ n =>
    rw [universalPrimitive_succ]
    calc
      (a^(n+1) - b * universalPrimitive a b n) * b^(n+1) =
          a^(n+1) * b^(n+1) -
            b^((n+1)+1) * universalPrimitive a b n := by
              rw [pow_succ]
              ring
      _ = a^(n+1) * b^(n+1) := by
            rw [hb]
            ring

/-- A positive top intersection proves the entire universal GST
middle primitive is NONZERO, even with nilpotent hyperplanes.
This detects nonzero algebraic primitive geometry on X×X
for EVERY smooth projective X once its ample degree is supplied. -/
theorem universalPrimitive_nonzero_of_top_pairing
    (a b : R) (d : Nat)
    (hb : b^(d+1) = 0)
    (htop : a^d * b^d ≠ 0) :
    universalPrimitive a b d ≠ 0 := by
  intro hzero
  have heq := universalPrimitive_top_pairing a b d hb
  rw [hzero] at heq
  exact htop heq.symm

#check universalPrimitive_top_pairing
#check universalPrimitive_nonzero_of_top_pairing
#print axioms universalPrimitive_nonzero_of_top_pairing

end GSTUniversalSelfProductPrimitive
