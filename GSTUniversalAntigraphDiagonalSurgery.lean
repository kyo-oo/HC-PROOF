import GSTUniversalSelfProductPrimitive

/-!
# GST universal antiholomorphic graph / diagonal integer surgery

For EVERY n>=1, on the ACTUAL smooth projective variety
X_n = P^n(C) x P^n(C), let A,B be factor hyperplane classes.

The graph Γ_c of complex conjugation c:P^n->P^n has middle integral
Poincare-dual polynomial
  sum_{j=0}^n (-1)^(n-j) A^(n-j) B^j.
It is the GST self-product universal primitive polynomial with
the variables SWAPPED: universalPrimitive B A n.

The holomorphic diagonal Δ has class
  sum_{j=0}^n A^(n-j) B^j.

Thus their sum has EXACTLY the positive even-parity monomials:
  [Γ_c]+[Δ] =
     2 sum_{0<=j<=n, Even(n-j)} A^(n-j) B^j.

Every monomial is represented by the holomorphic product of two
linear subspaces P^j x P^(n-j). Hence this identity produces an
actual integral-homology-preserving surgery
  Γ_c + Δ --> 2 sum_{Even(n-j)} (P^j x P^(n-j)).
All output components are Kähler calibrated; input Γ_c is
Lagrangian and NOT calibrated.

Lean proves the universal coefficient identity in ANY commutative
ring and confirms the parity-positive normal form. The analytical
interpretation uses genuine projective graph, diagonal and linear
subspace fundamental classes, and standard geometry; this file
does NOT assert every Hodge class on an arbitrary X is algebraic.
-/

set_option maxHeartbeats 12000000
noncomputable section

namespace GSTUniversalAntigraphDiagonalSurgery

variable {R : Type*} [CommRing R]

/-- Homology class of the holomorphic diagonal in
H^{2n}(P^n x P^n) from its actual factor-hyperplane expansion. -/
def diagonalClass (a b : R) (n : Nat) : R :=
  ∑ j ∈ Finset.range (n+1), a^(n-j) * b^j

/-- Homology class of the graph of antiholomorphic conjugation.
The sign is topologically its action c*h=-h on H²(P^n). -/
def antiGraphClass (a b : R) (n : Nat) : R :=
  ∑ j ∈ Finset.range (n+1),
    if Even (n-j) then a^(n-j) * b^j else -(a^(n-j) * b^j)

/-- Explicitly EFFECTIVE polynomial with INTEGER-positive coefficients.
In geometry each term represents a holomorphic product of linear
subspaces of total codimension n. -/
def calibratedReplacementClass (a b : R) (n : Nat) : R :=
  ∑ j ∈ Finset.range (n+1),
    if Even (n-j) then 2*(a^(n-j) * b^j) else 0

/-- Exact all-dimensional integral homology relation, no division by two
and no rationalized equality. It is therefore suitable for an INTEGER
boundary filling on every P^n x P^n. -/
theorem universal_integer_homology_surgery
    (a b : R) (n : Nat) :
    diagonalClass a b n + antiGraphClass a b n =
      calibratedReplacementClass a b n := by
  classical
  unfold diagonalClass antiGraphClass calibratedReplacementClass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases he : Even (n-j)
  · simp [he]
    ring
  · simp [he]

/-- The n=1 relation is the known GST anti-graph + diagonal = 2 fiber. -/
theorem projective_line_surgery
    (a b : R) :
    diagonalClass a b 1 + antiGraphClass a b 1 = 2*b := by
  rw [universal_integer_homology_surgery]
  simp [calibratedReplacementClass, Finset.sum_range_succ] <;> ring

/-- The n=2 relation acts on genuine middle codimension TWO,
the first nontrivial higher-Hodge codimension, yielding two kinds
of positive holomorphic projective plane surfaces. -/
theorem projective_plane_middle_surgery
    (a b : R) :
    diagonalClass a b 2 + antiGraphClass a b 2 =
      2*(a^2+b^2) := by
  rw [universal_integer_homology_surgery]
  simp [calibratedReplacementClass, Finset.sum_range_succ] <;> ring

#check universal_integer_homology_surgery
#check projective_plane_middle_surgery
#print axioms universal_integer_homology_surgery

end GSTUniversalAntigraphDiagonalSurgery
