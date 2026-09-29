import GSTClassicalHodgeCrossWeightAtomicDefectDescent
import GSTClassicalHodgeAtomicDefectDuality

/-!
# GST CLASSICAL HODGE — PRIMITIVE ATOMIC-DEFECT REDUCTION

Complementary transport does not solve the primitive Hodge problem.  This file
makes that residual exact and basis-free.

The genuine projective principal cut gives a Hodge-preserving map

  L_p : Hodge_p -> Hodge_(p+1)

whose atomic-defect class is functorial.  Supply only the ordinary
cohomological Lefschetz-decomposition datum that every Hodge vector at weight
p+1 is a sum

  L_p beta + gamma

with gamma in a designated primitive Hodge subspace.  No algebraicity of gamma
is assumed.

Then:

* if the source weight has zero Hodge defect, every defect at p+1 is represented
  by the primitive summand;
* if the primitive defect also vanishes, the whole p+1 defect vanishes;
* by induction, weight-zero defect extinction plus primitive defect extinction
  at every positive weight proves the full Stage-2G Hodge statement.

So the unresolved same-weight problem is localized exactly to the primitive
atomic defect.  The transport part and the primitive part are no longer mixed.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgePrimitiveAtomicDefectReduction

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicDefectDuality
open GSTClassicalHodgeCrossWeightNativePropagation
open GSTClassicalHodgeCrossWeightAtomicDefectDescent
open GSTClassicalHodgeGeometricCycleClassSpine

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Genuine one-step projective principal cut restricted to the Hodge fibers. -/
noncomputable def principalCutHodgeMap
    (G : GeometricCycleClassSpine V H)
    (p : Nat) :
    ClassicalHodgeFiber V H p →ₗ[ℚ]
      ClassicalHodgeFiber V H (p + 1) where
  toFun alpha :=
    ⟨(G.principalCutPair p).cohomologyOperator alpha.1,
      G.principalCut_hodge p alpha.1 alpha.2⟩
  map_add' := by
    intro a b
    apply Subtype.ext
    simp
  map_smul' := by
    intro c a
    apply Subtype.ext
    simp

@[simp]
theorem principalCutHodgeMap_coe
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (alpha : ClassicalHodgeFiber V H p) :
    (principalCutHodgeMap G p alpha).1 =
      (G.principalCutPair p).cohomologyOperator alpha.1 :=
  rfl

/-- Atomic defect commutes exactly with the genuine Hodge principal cut. -/
theorem atomicDefect_principalCutHodgeMap
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (alpha : ClassicalHodgeFiber V H p) :
    atomicDefectLinearMap V H (p + 1)
        (principalCutHodgeMap G p alpha) =
      (G.principalCutPair p).defectOperator
        (atomicDefectLinearMap V H p alpha) := by
  exact ((G.principalCutPair p).defect_equivariant alpha
    (G.principalCut_hodge p alpha.1 alpha.2)).symm

/-- Purely cohomological primitive decomposition data.  The primitive subspace
is not assumed algebraic. -/
structure LefschetzPrimitiveDecomposition
    (G : GeometricCycleClassSpine V H) where
  primitive : ∀ p : Nat, Submodule ℚ (ClassicalHodgeFiber V H p)
  decompose_successor :
    ∀ p : Nat, ∀ alpha : ClassicalHodgeFiber V H (p + 1),
      ∃ beta : ClassicalHodgeFiber V H p,
      ∃ gamma : primitive (p + 1),
        alpha = principalCutHodgeMap G p beta + gamma.1

namespace LefschetzPrimitiveDecomposition

/-- Restriction of the atomic-defect map to the primitive Hodge subspace. -/
noncomputable def primitiveDefectMap
    (D : LefschetzPrimitiveDecomposition G)
    (p : Nat) :
    D.primitive p →ₗ[ℚ] AtomicDefectSpace V H p :=
  (atomicDefectLinearMap V H p).comp (D.primitive p).subtype

@[simp]
theorem primitiveDefectMap_apply
    (D : LefschetzPrimitiveDecomposition G)
    (p : Nat)
    (gamma : D.primitive p) :
    D.primitiveDefectMap p gamma =
      atomicDefectLinearMap V H p gamma.1 :=
  rfl

/-- If the lower weight is already algebraic, the defect of a decomposed Hodge
class is exactly the defect of its primitive remainder. -/
theorem atomicDefect_eq_primitive_of_source_zero
    (D : LefschetzPrimitiveDecomposition G)
    (p : Nat)
    (hsource : atomicDefectLinearMap V H p = 0)
    (alpha : ClassicalHodgeFiber V H (p + 1)) :
    ∃ gamma : D.primitive (p + 1),
      atomicDefectLinearMap V H (p + 1) alpha =
        D.primitiveDefectMap (p + 1) gamma := by
  rcases D.decompose_successor p alpha with ⟨beta, gamma, hdecomp⟩
  refine ⟨gamma, ?_⟩
  rw [hdecomp, map_add]
  have hbeta : atomicDefectLinearMap V H p beta = 0 := by
    rw [hsource]
    rfl
  have hcut :
      atomicDefectLinearMap V H (p + 1)
          (principalCutHodgeMap G p beta) = 0 := by
    rw [atomicDefect_principalCutHodgeMap G p beta, hbeta]
    exact map_zero _
  rw [hcut, zero_add]
  rfl

/-- **ONE-STEP PRIMITIVE REDUCTION.**
Source defect zero plus primitive defect zero implies target defect zero. -/
theorem targetDefect_zero_of_source_and_primitive
    (D : LefschetzPrimitiveDecomposition G)
    (p : Nat)
    (hsource : atomicDefectLinearMap V H p = 0)
    (hprimitive : D.primitiveDefectMap (p + 1) = 0) :
    atomicDefectLinearMap V H (p + 1) = 0 := by
  apply LinearMap.ext
  intro alpha
  rcases D.atomicDefect_eq_primitive_of_source_zero p hsource alpha with
    ⟨gamma, hgamma⟩
  rw [hgamma, hprimitive]
  rfl

/-- Contrapositive localization: if a new target defect survives while the
source weight is already zero-defect, then the primitive defect map is nonzero. -/
theorem primitiveDefect_ne_zero_of_target_ne_zero
    (D : LefschetzPrimitiveDecomposition G)
    (p : Nat)
    (hsource : atomicDefectLinearMap V H p = 0)
    (htarget : atomicDefectLinearMap V H (p + 1) ≠ 0) :
    D.primitiveDefectMap (p + 1) ≠ 0 := by
  intro hprimitive
  exact htarget (D.targetDefect_zero_of_source_and_primitive
    p hsource hprimitive)

/-- If weight zero and every positive primitive sector have zero atomic defect,
then every Hodge weight has zero atomic defect. -/
theorem all_atomicDefects_zero_of_zero_and_primitives
    (D : LefschetzPrimitiveDecomposition G)
    (hzero : atomicDefectLinearMap V H 0 = 0)
    (hprimitive : ∀ p : Nat, D.primitiveDefectMap (p + 1) = 0) :
    ∀ p : Nat, atomicDefectLinearMap V H p = 0 := by
  intro p
  induction p with
  | zero => exact hzero
  | succ p ih =>
      exact D.targetDefect_zero_of_source_and_primitive p ih (hprimitive p)

/-- **PRIMITIVE RESIDUAL CROWN.**
Ordinary Lefschetz decomposition reduces the full Hodge target exactly to
weight-zero defect extinction and primitive defect extinction. -/
theorem bigradedBettiHodge_of_zero_and_primitive_defect
    (D : LefschetzPrimitiveDecomposition G)
    (hzero : atomicDefectLinearMap V H 0 = 0)
    (hprimitive : ∀ p : Nat, D.primitiveDefectMap (p + 1) = 0) :
    BigradedBettiHodgeStatement V H := by
  exact (bigradedBettiHodgeStatement_iff_atomicDefect_zero V H).2
    (D.all_atomicDefects_zero_of_zero_and_primitives hzero hprimitive)

end LefschetzPrimitiveDecomposition

#check principalCutHodgeMap
#check atomicDefect_principalCutHodgeMap
#check LefschetzPrimitiveDecomposition
#check LefschetzPrimitiveDecomposition.primitiveDefectMap
#check LefschetzPrimitiveDecomposition.atomicDefect_eq_primitive_of_source_zero
#check LefschetzPrimitiveDecomposition.targetDefect_zero_of_source_and_primitive
#check LefschetzPrimitiveDecomposition.primitiveDefect_ne_zero_of_target_ne_zero
#check LefschetzPrimitiveDecomposition.all_atomicDefects_zero_of_zero_and_primitives
#check LefschetzPrimitiveDecomposition.bigradedBettiHodge_of_zero_and_primitive_defect

#print axioms atomicDefect_principalCutHodgeMap
#print axioms LefschetzPrimitiveDecomposition.atomicDefect_eq_primitive_of_source_zero
#print axioms LefschetzPrimitiveDecomposition.targetDefect_zero_of_source_and_primitive
#print axioms LefschetzPrimitiveDecomposition.primitiveDefect_ne_zero_of_target_ne_zero
#print axioms LefschetzPrimitiveDecomposition.bigradedBettiHodge_of_zero_and_primitive_defect

end GSTClassicalHodgePrimitiveAtomicDefectReduction
