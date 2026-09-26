import Mathlib

/-!
# GST MATHLIB FINITE BASIS ADAPTER

A small adapter isolating the only Mathlib basis API needed by the Hodge
channel architecture.

For a basis B : Basis (Fin N) Q V we expose the ordinary coordinate function
Fin N -> Q and the inverse finite linear superposition.  The two operations
are inverse.  Downstream Hodge files therefore reason only with ordinary
finite channel vectors and not with Finsupp implementation details.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

noncomputable section

namespace GSTMathlibFiniteBasis

variable {V : Type*} [AddCommGroup V] [Module ℚ V]
variable {N : Nat}

/-- Ordinary finite coordinate vector of x in a Fin N-indexed basis. -/
noncomputable def basisCoordinates
    (B : Basis (Fin N) ℚ V) : V →ₗ[ℚ] (Fin N → ℚ) where
  toFun := fun x i => B.repr x i
  map_add' := by
    intro x y
    funext i
    simp
  map_smul' := by
    intro q x
    funext i
    simp

/-- Decode an ordinary coordinate vector by finite basis superposition. -/
noncomputable def basisDecode
    (B : Basis (Fin N) ℚ V) : (Fin N → ℚ) →ₗ[ℚ] V where
  toFun := fun a => ∑ i : Fin N, a i • B i
  map_add' := by
    intro a b
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' := by
    intro q a
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

/-- Decoding the coordinates of a vector reconstructs it exactly. -/
theorem basisDecode_basisCoordinates
    (B : Basis (Fin N) ℚ V) (x : V) :
    basisDecode B (basisCoordinates B x) = x := by
  classical
  change (∑ i : Fin N, (B.repr x i) • B i) = x
  exact B.sum_repr x

/-- Consequently finite basis decoding is surjective. -/
theorem basisDecode_surjective
    (B : Basis (Fin N) ℚ V) :
    Function.Surjective (basisDecode B) := by
  intro x
  exact ⟨basisCoordinates B x, basisDecode_basisCoordinates B x⟩

/-- Coordinates after decoding are exactly the original finite vector. -/
theorem basisCoordinates_basisDecode
    (B : Basis (Fin N) ℚ V) (a : Fin N → ℚ) :
    basisCoordinates B (basisDecode B a) = a := by
  classical
  funext j
  simp [basisCoordinates, basisDecode]

/-- The i-th Kronecker coordinate vector decodes to the i-th basis vector. -/
theorem basisDecode_kronecker
    (B : Basis (Fin N) ℚ V) (i : Fin N) :
    basisDecode B (fun j => if j = i then 1 else 0) = B i := by
  classical
  simp [basisDecode]

/-- Finite basis coordinates are a linear equivalence with ordinary channel
coordinates. -/
noncomputable def basisCoordinateEquiv
    (B : Basis (Fin N) ℚ V) : V ≃ₗ[ℚ] (Fin N → ℚ) where
  toLinearMap := basisCoordinates B
  invFun := basisDecode B
  left_inv := basisDecode_basisCoordinates B
  right_inv := basisCoordinates_basisDecode B

/-- Adapter crown. -/
theorem finite_basis_adapter_crown
    (B : Basis (Fin N) ℚ V) :
    Function.Bijective (basisCoordinates B)
      ∧ Function.Bijective (basisDecode B) := by
  exact ⟨(basisCoordinateEquiv B).bijective,
    (basisCoordinateEquiv B).symm.bijective⟩

#check basisCoordinates
#check basisDecode
#check basisDecode_basisCoordinates
#check basisDecode_surjective
#check basisCoordinates_basisDecode
#check basisDecode_kronecker
#check basisCoordinateEquiv
#check finite_basis_adapter_crown

#print axioms basisDecode_basisCoordinates
#print axioms basisCoordinates_basisDecode
#print axioms basisDecode_kronecker
#print axioms finite_basis_adapter_crown

end GSTMathlibFiniteBasis
