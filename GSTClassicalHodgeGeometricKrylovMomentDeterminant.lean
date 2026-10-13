import GSTClassicalHodgeRealizedCorrespondenceKrylovFinale
import GSTClassicalHodgeGeometricPeriodDeterminant
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# THE FULL HODGE ATTACK THROUGH ONE REALIZED CORRESPONDENCE, ONE NATIVE
# ALGEBRAIC SEED AND ONE PROJECTIVE-STYLE TRACE

The older GSTClassicalHodgeRealizedCorrespondenceKrylovFinale assumes the
native/cohomological orbit of one actual correspondence word spans the
Hodge fiber. That geometric CYCLICITY property is substantial.

We replace it with a NUMERICAL SCALAR NONVANISHING CRITERION.

Let n be the genuine rational dimension of the p,p Hodge fiber.
Choose ONE genuine realized correspondence word T, ONE native
algebraic cycle Z, and ONE rational linear trace ell. Build
v_j = T^j cl(Z) and the n-by-n moment matrix

             H_ij = ell(T^i v_j)
                  = ell(T^(i+j) cl(Z)).

If det(H) != 0, the native cycles
        Z, T_native Z, ..., T_native^(n-1) Z
span the ENTIRE Hodge fiber under the exact cycle-class map.

The proof is direct: H is the period matrix of the n genuine
native orbit classes against the n rational detectors ell o T^i.
Its nonzero determinant forces the Hodge coordinate matrix to be
invertible. Multiply its inverse by the arbitrary Hodge coordinates
and form the resulting RATIONAL sum of the native orbit cycles.
Naturality of the actual realized correspondence gives its exact class.

THERE IS NO assumption of orbit cyclicity or basis algebraicity.

This is the strongest compact numerical target discovered in the
repo's existing genuine-correspondence line: instead of realizing
every matrix unit or finding n different correspondences, it suffices
to construct ONE scheme-realized correspondence and verify ONE
Hankel determinant by genuine period/intersection geometry.

This DOES NOT prove nonvanishing for every V. A universal nonzero
Hankel construction remains the mathematical theorem to derive.
A word acting by a scalar on a higher-dimensional Hodge fiber
necessarily has a singular Hankel matrix, so a nontrivial geometric
operator is indispensable.

NEEDS CI RUN LATER.
-/

set_option maxHeartbeats 55000000
set_option maxRecDepth 900000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRealizedCorrespondenceKrylovFinale
open GSTClassicalHodgeRealizedCorrespondenceKrylovFinale.RealizedCorrespondenceKrylovCertificate
open GSTClassicalHodgeGeometricMatrixRankLanding
open GSTClassicalHodgeGeometricPeriodDeterminant

namespace GSTClassicalHodgeGeometricKrylovMomentDeterminant

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- The genuine matrix size is the FULL rational Hodge dimension, not
a fixed artificial GST observation-window size. -/
abbrev KrylovRank :=
  Module.finrank ℚ (ClassicalHodgeFiber V H p)

/-- The ith detector reads the ith moment of the EXISTING
correspondence action, followed by one rational geometric trace. -/
noncomputable def krylovMomentDetector
    (C : RealizedCorrespondenceKrylovCertificate V H p)
    (trace : ClassicalHodgeFiber V H p →ₗ[ℚ] ℚ)
    (i : Fin (KrylovRank (V := V) (H := H) (p := p))) :
    ClassicalHodgeFiber V H p →ₗ[ℚ] ℚ :=
  trace.comp (C.hodgeOperator ^ i.val)

/-- Entire geometric moment/Hankel matrix from one correspondence, seed,
and trace. Each column is an actual native cycle-class iterate. -/
noncomputable def krylovHankelMatrix
    [FiniteDimensional ℚ (ClassicalHodgeFiber V H p)]
    (C : RealizedCorrespondenceKrylovCertificate V H p)
    (trace : ClassicalHodgeFiber V H p →ₗ[ℚ] ℚ) :
    Matrix
      (Fin (KrylovRank (V := V) (H := H) (p := p)))
      (Fin (KrylovRank (V := V) (H := H) (p := p))) ℚ :=
  periodMatrix
    (fun j => C.hodgeOrbit j.val)
    (krylovMomentDetector C trace)

/-- A nonsingular scalar Hankel matrix constructs the rational-native
cycle representing an ARBITRARY genuine Hodge fiber vector.

Unlike the historical Krylov finale, NO orbit-cyclicity assumption
is supplied: it is numerically certified by determinant nonvanishing. -/
theorem native_cycle_of_nonzero_krylov_hankel_determinant
    [FiniteDimensional ℚ (ClassicalHodgeFiber V H p)]
    (C : RealizedCorrespondenceKrylovCertificate V H p)
    (trace : ClassicalHodgeFiber V H p →ₗ[ℚ] ℚ)
    (hdet : (krylovHankelMatrix C trace).det ≠ 0)
    (alpha : ClassicalHodgeFiber V H p) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha.1 := by
  classical
  let b := Module.finBasis ℚ (ClassicalHodgeFiber V H p)
  let z : Fin (KrylovRank (V := V) (H := H) (p := p)) →
      ClassicalHodgeFiber V H p :=
    fun j => C.hodgeOrbit j.val
  let M : Matrix
      (Fin (KrylovRank (V := V) (H := H) (p := p)))
      (Fin (KrylovRank (V := V) (H := H) (p := p))) ℚ :=
    geometricCoordinateMatrix b z
  have hMdet : M.det ≠ 0 :=
    coordinate_det_ne_zero_of_period_det_ne_zero
      b z (krylovMomentDetector C trace) hdet
  have hMunit : IsUnit M.det := isUnit_iff_ne_zero.mpr hMdet
  let coefficients :
      Fin (KrylovRank (V := V) (H := H) (p := p)) → ℚ :=
    (M⁻¹).mulVec (fun i => (b.repr alpha) i)
  let Z : codimensionCycles V.X p :=
    ∑ j : Fin (KrylovRank (V := V) (H := H) (p := p)),
      coefficients j • C.nativeOrbit j.val
  have hreconstruct :
      ∑ j : Fin (KrylovRank (V := V) (H := H) (p := p)),
        coefficients j • z j = alpha := by
    exact geometric_matrix_right_inverse_reconstructs
      b z M⁻¹ (Matrix.mul_nonsing_inv M hMunit) alpha
  have hZ :
      H.cycleClass p Z =
        (∑ j : Fin (KrylovRank (V := V) (H := H) (p := p)),
          coefficients j • z j).1 := by
    simp [Z, coefficients, z,
      map_sum, map_smul, C.nativeOrbit_cycleClass,
      Submodule.coe_sum, Submodule.coe_smul_of_tower]
  refine ⟨Z, ?_⟩
  exact hZ.trans (congrArg Subtype.val hreconstruct)

/-- Universal target at all codimensions using ONE genuine realized
correspondence, ONE algebraic seed, and ONE rational trace per weight.
Everything is in HC-PROOF's pre-existing strict correspondence language. -/
def UniversalGSTKrylovHankelNondegeneracy
    (F : GSTHodgeChannelFinale.Stage2GHodgeFiniteness V H) : Prop :=
  ∀ q : Nat,
    letI : FiniteDimensional ℚ (ClassicalHodgeFiber V H q) := F.finite q
    ∃ C : RealizedCorrespondenceKrylovCertificate V H q,
    ∃ trace : ClassicalHodgeFiber V H q →ₗ[ℚ] ℚ,
      (krylovHankelMatrix C trace).det ≠ 0

/-- FULL rational Hodge on the arbitrary smooth projective carrier V
from the single-correspondence scalar Hankel criterion at every weight.
The proof constructs each target native cycle from genuine iterates. -/
theorem full_hodge_of_universal_Krylov_Hankel_geometry
    (F : GSTHodgeChannelFinale.Stage2GHodgeFiniteness V H)
    (h : UniversalGSTKrylovHankelNondegeneracy F) :
    BigradedBettiHodgeStatement V H := by
  intro q alpha halpha
  letI : FiniteDimensional ℚ (ClassicalHodgeFiber V H q) := F.finite q
  obtain ⟨C, trace, hDet⟩ := h q
  exact native_cycle_of_nonzero_krylov_hankel_determinant
    C trace hDet ⟨alpha, halpha⟩

#check krylovHankelMatrix
#check native_cycle_of_nonzero_krylov_hankel_determinant
#check full_hodge_of_universal_Krylov_Hankel_geometry
#print axioms full_hodge_of_universal_Krylov_Hankel_geometry

end GSTClassicalHodgeGeometricKrylovMomentDeterminant
