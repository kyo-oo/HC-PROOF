import Mathlib

/-!
# GST exact non-circular three-cycle intersection-rank compiler

For Y = Bl_C(P^4) with smooth connected curve C, the proposed three actual
codimension-two cycle classes are:
  v0 = pullback of the square of a projective hyperplane;
  v1 = exceptional Gysin of the class of a point on C;
  v2 = exceptional Gysin of the tautological hyperplane on E.

Their geometric middle-intersection matrix, in compatible signs, is

    [ 1   0   0 ]
    [ 0   0  -1 ]
    [ 0  -1  -n ]

where n is the degree of the normal bundle of C inside P^4.
Its determinant is -1 independent of n, and the inverse matrix is

    [ 1   0   0 ]
    [ 0   n  -1 ]
    [ 0  -1   0 ].

This file kernel-proves the associated EXPLICIT cycle reconstruction for
every class of the true rational Hodge fiber whenever the intersection
readouts distinguish classes. In the geometric blowup of P^4 along a smooth
curve, H^4 has rank 3 and the intersection pairing is nondegenerate, so
the three geometric readouts indeed separate classes. Those topological
inputs and the scheme-specific intersection numbers remain separate
geometric obligations; no full-rank assumption on the target cycleClass
and no target class preimage occur here.
-/

set_option maxHeartbeats 2000000
noncomputable section

namespace GSTBlowupThreeCycleIntersectionRank

variable {W : Type*} [AddCommGroup W] [Module ℚ W]

/-- The exact rational three-cycle reconstruction obtained by inverting
the geometric Gram matrix, not guessing an algebraic preimage. -/
def reconstructFromIntersection
    (ell0 ell1 ell2 : W →ₗ[ℚ] ℚ)
    (v0 v1 v2 : W) (n : ℚ) (alpha : W) : W :=
  (ell0 alpha) • v0 +
    (n * ell1 alpha - ell2 alpha) • v1 -
    (ell1 alpha) • v2

/-- First row of the geometric identity: 1,0,0. -/
theorem readout_zero_reconstructed
    (ell0 ell1 ell2 : W →ₗ[ℚ] ℚ)
    (v0 v1 v2 : W) (n : ℚ)
    (h00 : ell0 v0 = 1)
    (h01 : ell0 v1 = 0)
    (h02 : ell0 v2 = 0)
    (alpha : W) :
    ell0 (reconstructFromIntersection ell0 ell1 ell2 v0 v1 v2 n alpha) =
      ell0 alpha := by
  simp [reconstructFromIntersection, map_add, map_sub, map_smul,
    h00, h01, h02]

/-- Second row: 0,0,-1. -/
theorem readout_one_reconstructed
    (ell0 ell1 ell2 : W →ₗ[ℚ] ℚ)
    (v0 v1 v2 : W) (n : ℚ)
    (h10 : ell1 v0 = 0)
    (h11 : ell1 v1 = 0)
    (h12 : ell1 v2 = -1)
    (alpha : W) :
    ell1 (reconstructFromIntersection ell0 ell1 ell2 v0 v1 v2 n alpha) =
      ell1 alpha := by
  simp [reconstructFromIntersection, map_add, map_sub, map_smul,
    h10, h11, h12]

/-- Third row: 0,-1,-n. -/
theorem readout_two_reconstructed
    (ell0 ell1 ell2 : W →ₗ[ℚ] ℚ)
    (v0 v1 v2 : W) (n : ℚ)
    (h20 : ell2 v0 = 0)
    (h21 : ell2 v1 = -1)
    (h22 : ell2 v2 = -n)
    (alpha : W) :
    ell2 (reconstructFromIntersection ell0 ell1 ell2 v0 v1 v2 n alpha) =
      ell2 alpha := by
  simp [reconstructFromIntersection, map_add, map_sub, map_smul,
    h20, h21, h22]
  ring

/-- Given a geometrically certified *separating* triple of intersection
readouts, the exact three-cycle formula reconstructs EVERY Hodge vector.
Separation is independent of the algebraic cycle-class image: on the
blowup benchmark it follows from H^4-rank 3, Poincare duality, and the
explicit nonzero Gram determinant. -/
theorem reconstruct_exact
    (ell0 ell1 ell2 : W →ₗ[ℚ] ℚ)
    (v0 v1 v2 : W) (n : ℚ)
    (h00 : ell0 v0 = 1) (h01 : ell0 v1 = 0) (h02 : ell0 v2 = 0)
    (h10 : ell1 v0 = 0) (h11 : ell1 v1 = 0) (h12 : ell1 v2 = -1)
    (h20 : ell2 v0 = 0) (h21 : ell2 v1 = -1) (h22 : ell2 v2 = -n)
    (hsep : Function.Injective (fun x : W => (ell0 x, ell1 x, ell2 x)))
    (alpha : W) :
    reconstructFromIntersection ell0 ell1 ell2 v0 v1 v2 n alpha = alpha := by
  apply hsep
  apply Prod.ext
  · exact readout_zero_reconstructed ell0 ell1 ell2 v0 v1 v2 n
      h00 h01 h02 alpha
  · apply Prod.ext
    · exact readout_one_reconstructed ell0 ell1 ell2 v0 v1 v2 n
        h10 h11 h12 alpha
    · exact readout_two_reconstructed ell0 ell1 ell2 v0 v1 v2 n
        h20 h21 h22 alpha

variable {C : Type*} [AddCommGroup C] [Module ℚ C]

/-- Construct an actual native rational algebraic cycle using only the
three independently defined algebraic cycles and rational coefficients. -/
def nativeCycleFromIntersection
    (cl : C →ₗ[ℚ] W)
    (ell0 ell1 ell2 : W →ₗ[ℚ] ℚ)
    (Z0 Z1 Z2 : C) (n : ℚ) (alpha : W) : C :=
  (ell0 alpha) • Z0 +
    (n * ell1 alpha - ell2 alpha) • Z1 -
    (ell1 alpha) • Z2

/-- Native-to-cohomology compatibility is proved rather than assumed for
the resulting target cycle: it follows from linearity of the genuine
cycle-class map on the three already given native cycles. -/
theorem nativeCycleFromIntersection_cycleClass
    (cl : C →ₗ[ℚ] W)
    (ell0 ell1 ell2 : W →ₗ[ℚ] ℚ)
    (Z0 Z1 Z2 : C) (n : ℚ) (alpha : W) :
    cl (nativeCycleFromIntersection cl ell0 ell1 ell2 Z0 Z1 Z2 n alpha) =
      reconstructFromIntersection ell0 ell1 ell2
        (cl Z0) (cl Z1) (cl Z2) n alpha := by
  simp [nativeCycleFromIntersection, reconstructFromIntersection,
    map_add, map_sub, map_smul]

/-- One explicit all-class algebraic cycle constructor, conditional ONLY
on independently measurable intersection numbers and the separation of
the target rational Hodge fiber by its three geometric readouts. -/
theorem three_native_cycles_represent_every_hodge_class
    (cl : C →ₗ[ℚ] W)
    (ell0 ell1 ell2 : W →ₗ[ℚ] ℚ)
    (Z0 Z1 Z2 : C) (n : ℚ)
    (h00 : ell0 (cl Z0) = 1)
    (h01 : ell0 (cl Z1) = 0)
    (h02 : ell0 (cl Z2) = 0)
    (h10 : ell1 (cl Z0) = 0)
    (h11 : ell1 (cl Z1) = 0)
    (h12 : ell1 (cl Z2) = -1)
    (h20 : ell2 (cl Z0) = 0)
    (h21 : ell2 (cl Z1) = -1)
    (h22 : ell2 (cl Z2) = -n)
    (hsep : Function.Injective (fun x : W => (ell0 x, ell1 x, ell2 x)))
    (alpha : W) :
    cl (nativeCycleFromIntersection cl ell0 ell1 ell2 Z0 Z1 Z2 n alpha) =
      alpha := by
  rw [nativeCycleFromIntersection_cycleClass]
  exact reconstruct_exact ell0 ell1 ell2
    (cl Z0) (cl Z1) (cl Z2) n
    h00 h01 h02 h10 h11 h12 h20 h21 h22 hsep alpha

#check reconstruct_exact
#check nativeCycleFromIntersection_cycleClass
#check three_native_cycles_represent_every_hodge_class
#print axioms three_native_cycles_represent_every_hodge_class

end GSTBlowupThreeCycleIntersectionRank
