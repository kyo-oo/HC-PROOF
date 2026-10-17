import GSTUniversalSurfaceGraphAugmentation

/-!
# GST primitive algebraic product stabilization in every dimension

A primitive algebraic middle class z on a smooth fourfold X has
L_X*z=0. Form Y=X×P^k with the product ample class
L_Y=pr_X^*L_X + pr_P^*h and the native cycle Z×P^k.

The resulting rational Betti class is z⊗1 and its primitive-test
power is L_Y^(k+1). Since all monomials containing L_X kill z
and h^(k+1)=0 on P^k, the product cycle stays primitive.

The following UNIFORM algebraic theorem proves the binomial
cancellation for any commutative cup-algebra model; it is the
ring-theoretic core of the genuine projective/Kunneth construction.
All geometric cycle inputs come from already constructed algebraic
graph differences; the geometric product and canonical Betti
Kunneth identifications are the independent realization step.
-/

set_option maxHeartbeats 10000000
noncomputable section

namespace GSTPrimitiveProductTowerStabilization

/-- A primitive source class annihilated by L_X sees only the
projective factor under every power of L_X+h. -/
theorem primitive_source_binomial_collapse
    {R : Type*} [CommRing R]
    (Lx h z : R)
    (hLx : Lx * z = 0)
    (k : ℕ) :
    (Lx + h)^k * z = h^k * z := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      calc
        (Lx + h)^(k + 1) * z =
            (Lx + h) * ((Lx + h)^k * z) := by
              rw [pow_succ]
              ring
        _ = (Lx + h) * (h^k * z) := by rw [ih]
        _ = Lx * (h^k * z) + h * (h^k * z) := by ring
        _ = 0 + h * (h^k * z) := by
              have hzero : Lx * (h^k * z) = 0 := by
                calc
                  Lx * (h^k * z) = h^k * (Lx * z) := by ring
                  _ = 0 := by simp [hLx]
              rw [hzero]
        _ = h^(k + 1) * z := by
              rw [pow_succ]
              ring

/-- Product Lefschetz primitiveness for EVERY projective-space
dimension k, from source primitiveness and projective nilpotence. -/
theorem primitive_projective_product_power_zero
    {R : Type*} [CommRing R]
    (Lx h z : R)
    (k : ℕ)
    (hLx : Lx * z = 0)
    (hTop : h^(k + 1) * z = 0) :
    (Lx + h)^(k + 1) * z = 0 := by
  calc
    (Lx + h)^(k + 1) * z = h^(k + 1) * z :=
      primitive_source_binomial_collapse Lx h z hLx (k + 1)
    _ = 0 := hTop

#check primitive_source_binomial_collapse
#check primitive_projective_product_power_zero
#print axioms primitive_projective_product_power_zero

end GSTPrimitiveProductTowerStabilization
