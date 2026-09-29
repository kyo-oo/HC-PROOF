import GSTClassicalHodgeFirstFailureCokernelRigidity
import GSTClassicalHodgePrimitiveAtomicDefectReduction

/-!
# GST CLASSICAL HODGE — FIRST-FAILURE PRIMITIVE IMAGE

The one-step primitive reduction previously proved an elementwise statement:
if weight `p` has zero Hodge defect, then every defect of a Hodge class at
weight `p+1` is represented by the primitive remainder in a Lefschetz
decomposition.

This file upgrades that statement to equality of submodules inside the atomic
defect quotient.

Define

  D_Hdg(p)  = range(atomicDefectLinearMap p)
  D_prim(p) = range(primitiveDefectMap p).

Then `D_prim(p) <= D_Hdg(p)` always.  If the preceding weight is defect-free,

  D_prim(p+1) = D_Hdg(p+1).

Hence at the globally least bad weight the *entire* realized Hodge-defect
sector is primitive.  No nonprimitive/projective-cut contribution survives in
the quotient.  This is stronger than merely producing one primitive witness:
it identifies the whole residual representation.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeFirstFailurePrimitiveImage

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeAtomicDefectDuality
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgePrimitiveAtomicDefectReduction
open GSTClassicalHodgeHodgeDefectImageFunctoriality
open GSTClassicalHodgeFirstPrimitiveProjectiveFailure

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {G : GeometricCycleClassSpine V H}
variable {D : LefschetzPrimitiveDecomposition G}
variable {p : Nat}

/-- Atomic defects represented by primitive Hodge vectors. -/
noncomputable def PrimitiveDefectImage
    (D : LefschetzPrimitiveDecomposition G)
    (p : Nat) : Submodule ℚ (AtomicDefectSpace V H p) :=
  LinearMap.range (D.primitiveDefectMap p)

/-- Primitive realized defects are always genuine realized Hodge defects. -/
theorem PrimitiveDefectImage_le_HodgeDefectImage
    (D : LefschetzPrimitiveDecomposition G)
    (p : Nat) :
    PrimitiveDefectImage D p ≤ HodgeDefectImage V H p := by
  intro z hz
  rcases hz with ⟨gamma, hgamma⟩
  refine ⟨gamma.1, ?_⟩
  simpa [LefschetzPrimitiveDecomposition.primitiveDefectMap_apply] using hgamma

/-- **SOURCE-ZERO PRIMITIVE IMAGE SATURATION.**
Once the previous weight has zero Hodge defect, every realized defect in the
next weight is represented by a primitive Hodge vector. -/
theorem PrimitiveDefectImage_eq_HodgeDefectImage_of_source_zero
    (D : LefschetzPrimitiveDecomposition G)
    (p : Nat)
    (hsource : atomicDefectLinearMap V H p = 0) :
    PrimitiveDefectImage D (p + 1) = HodgeDefectImage V H (p + 1) := by
  apply le_antisymm
  · exact PrimitiveDefectImage_le_HodgeDefectImage D (p + 1)
  · intro z hz
    rcases hz with ⟨alpha, halpha⟩
    rcases D.atomicDefect_eq_primitive_of_source_zero p hsource alpha with
      ⟨gamma, hgamma⟩
    refine ⟨gamma, ?_⟩
    rw [← hgamma]
    exact halpha

/-- At a first bad successor weight, the entire realized Hodge-defect sector is
primitive. -/
theorem firstFailure_PrimitiveDefectImage_eq_HodgeDefectImage
    (F : FirstAtomicDefectWeight V H)
    {p : Nat}
    (hp : F.weight = p + 1)
    (D : LefschetzPrimitiveDecomposition G) :
    PrimitiveDefectImage D (p + 1) = HodgeDefectImage V H (p + 1) := by
  exact PrimitiveDefectImage_eq_HodgeDefectImage_of_source_zero
    D p (firstAtomicDefect_predecessor_zero F hp)

/-- Therefore the primitive defect image is nonzero at the first failure. -/
theorem firstFailure_PrimitiveDefectImage_ne_bot
    (F : FirstAtomicDefectWeight V H)
    {p : Nat}
    (hp : F.weight = p + 1)
    (D : LefschetzPrimitiveDecomposition G) :
    PrimitiveDefectImage D (p + 1) ≠ ⊥ := by
  rw [firstFailure_PrimitiveDefectImage_eq_HodgeDefectImage F hp D]
  have hweight : HodgeDefectImage V H (p + 1) ≠ ⊥ := by
    rw [← hp]
    exact firstAtomicDefect_HodgeDefectImage_ne_bot F
  exact hweight

/-- The principal-cut contribution to the first realized defect sector is zero:
all of the surviving sector is carried by the primitive image. -/
theorem firstFailure_principalCut_defectImage_is_zero
    (F : FirstAtomicDefectWeight V H)
    {p : Nat}
    (hp : F.weight = p + 1)
    (G : GeometricCycleClassSpine V H) :
    principalCutOnHodgeDefectImage G p = 0 := by
  apply LinearMap.ext
  intro z
  have hbot : HodgeDefectImage V H p = ⊥ := by
    apply firstAtomicDefect_lower_HodgeDefectImage_eq_bot F p
    omega
  have hz : z = 0 := by
    apply Subtype.ext
    have hzbot : z.1 ∈ (⊥ : Submodule ℚ (AtomicDefectSpace V H p)) := by
      rw [← hbot]
      exact z.2
    simpa using hzbot
  rw [hz]
  exact map_zero _

/-- Submodule-level residual normal form: at the first bad successor, the
realized defect is nonzero, completely primitive, and receives zero realized
defect from the genuine previous-weight principal cut. -/
theorem firstFailure_primitive_cokernel_normal_form
    (F : FirstAtomicDefectWeight V H)
    {p : Nat}
    (hp : F.weight = p + 1)
    (D : LefschetzPrimitiveDecomposition G) :
    PrimitiveDefectImage D (p + 1) = HodgeDefectImage V H (p + 1)
      ∧ PrimitiveDefectImage D (p + 1) ≠ ⊥
      ∧ principalCutOnHodgeDefectImage G p = 0 := by
  refine ⟨
    firstFailure_PrimitiveDefectImage_eq_HodgeDefectImage F hp D,
    firstFailure_PrimitiveDefectImage_ne_bot F hp D,
    ?_⟩
  exact firstFailure_principalCut_defectImage_is_zero F hp G

#check PrimitiveDefectImage
#check PrimitiveDefectImage_le_HodgeDefectImage
#check PrimitiveDefectImage_eq_HodgeDefectImage_of_source_zero
#check firstFailure_PrimitiveDefectImage_eq_HodgeDefectImage
#check firstFailure_PrimitiveDefectImage_ne_bot
#check firstFailure_principalCut_defectImage_is_zero
#check firstFailure_primitive_cokernel_normal_form

#print axioms PrimitiveDefectImage_eq_HodgeDefectImage_of_source_zero
#print axioms firstFailure_PrimitiveDefectImage_eq_HodgeDefectImage
#print axioms firstFailure_principalCut_defectImage_is_zero
#print axioms firstFailure_primitive_cokernel_normal_form

end GSTClassicalHodgeFirstFailurePrimitiveImage
