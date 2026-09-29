import GSTClassicalHodgeFirstPrimitiveProjectiveFailure
import GSTClassicalHodgeCrossWeightAtomicDefectDescent

/-!
# GST CLASSICAL HODGE — HODGE-DEFECT IMAGE FUNCTORIALITY

The ambient atomic-defect quotient can be nonzero even when the Hodge
conjecture is true at a weight: Hodge only says that the actual `(p,p)` Hodge
fiber maps to zero in that quotient.  Therefore first-failure minimality should
not be applied to the whole quotient.

The correct object is the *realized Hodge-defect sector*

  D_Hdg(p) = range( atomicDefectLinearMap p ).

This submodule is bottom exactly when Hodge holds at weight `p`.  Every genuine
graded cycle-class operator whose cohomological action preserves the relevant
Hodge fibers acts canonically on these realized defect sectors by the already
proved quotient equivariance.

Consequently, at the least bad weight all lower realized defect sectors are
literally zero.  This is the precise categorical form needed by subsequent
cross-weight reciprocity arguments.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeHodgeDefectImageFunctoriality

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeAtomicDefectDuality
open GSTClassicalHodgeCrossWeightNativePropagation
open GSTClassicalHodgeCrossWeightAtomicDefectDescent
open GSTClassicalHodgeFirstPrimitiveProjectiveFailure

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p q r : Nat}

/-- The defect states which are actually represented by rational Hodge classes. -/
noncomputable def HodgeDefectImage
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) : Submodule ℚ (AtomicDefectSpace V H p) :=
  LinearMap.range (atomicDefectLinearMap V H p)

/-- Membership is exactly representability by a Hodge class. -/
theorem mem_HodgeDefectImage_iff
    (z : AtomicDefectSpace V H p) :
    z ∈ HodgeDefectImage V H p ↔
      ∃ alpha : ClassicalHodgeFiber V H p,
        atomicDefectLinearMap V H p alpha = z := by
  rfl

/-- The realized defect sector is bottom exactly when the Hodge defect map is
zero. -/
theorem HodgeDefectImage_eq_bot_iff :
    HodgeDefectImage V H p = ⊥ ↔ atomicDefectLinearMap V H p = 0 := by
  constructor
  · intro himage
    apply LinearMap.ext
    intro alpha
    have hmem :
        atomicDefectLinearMap V H p alpha ∈ HodgeDefectImage V H p :=
      ⟨alpha, rfl⟩
    rw [himage] at hmem
    simpa using hmem
  · intro hzero
    apply le_antisymm
    · intro z hz
      rcases hz with ⟨alpha, rfl⟩
      rw [hzero]
      exact Submodule.zero_mem _
    · exact bot_le

/-- Equivalently, a nonzero Hodge defect map gives a nontrivial realized defect
sector. -/
theorem HodgeDefectImage_ne_bot_iff :
    HodgeDefectImage V H p ≠ ⊥ ↔ atomicDefectLinearMap V H p ≠ 0 := by
  exact not_congr HodgeDefectImage_eq_bot_iff

/-- A genuine graded cycle-class operator together with its actual Hodge-fiber
preservation law. -/
structure HodgeStableGradedOperator
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p q : Nat) where
  pair : GradedCycleClassOperatorPair V H p q
  hodge :
    ∀ alpha : CohAt H p,
      alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p) →
        pair.cohomologyOperator alpha ∈
          rationalHodgeSubspace (H.hodgeBigrading q)

namespace HodgeStableGradedOperator

/-- Restriction of a Hodge-stable graded operator to the actual Hodge fibers. -/
noncomputable def onHodge
    (T : HodgeStableGradedOperator V H p q) :
    ClassicalHodgeFiber V H p →ₗ[ℚ] ClassicalHodgeFiber V H q where
  toFun alpha := ⟨T.pair.cohomologyOperator alpha.1,
    T.hodge alpha.1 alpha.2⟩
  map_add' := by
    intro a b
    apply Subtype.ext
    simp
  map_smul' := by
    intro c a
    apply Subtype.ext
    simp

@[simp]
theorem onHodge_coe
    (T : HodgeStableGradedOperator V H p q)
    (alpha : ClassicalHodgeFiber V H p) :
    (T.onHodge alpha).1 = T.pair.cohomologyOperator alpha.1 := by
  rfl

/-- Exact equivariance of the Hodge defect map under a Hodge-stable genuine
graded operator. -/
theorem defect_equivariant
    (T : HodgeStableGradedOperator V H p q)
    (alpha : ClassicalHodgeFiber V H p) :
    atomicDefectLinearMap V H q (T.onHodge alpha) =
      T.pair.defectOperator (atomicDefectLinearMap V H p alpha) := by
  exact T.pair.defect_equivariant alpha (T.hodge alpha.1 alpha.2)

/-- The induced map on *realized Hodge-defect image sectors*. -/
noncomputable def onHodgeDefectImage
    (T : HodgeStableGradedOperator V H p q) :
    HodgeDefectImage V H p →ₗ[ℚ] HodgeDefectImage V H q where
  toFun z := by
    refine ⟨T.pair.defectOperator z.1, ?_⟩
    rcases z.2 with ⟨alpha, halpha⟩
    refine ⟨T.onHodge alpha, ?_⟩
    rw [T.defect_equivariant alpha, halpha]
  map_add' := by
    intro a b
    apply Subtype.ext
    exact map_add _ _ _
  map_smul' := by
    intro c a
    apply Subtype.ext
    exact map_smul _ _ _

@[simp]
theorem onHodgeDefectImage_coe
    (T : HodgeStableGradedOperator V H p q)
    (z : HodgeDefectImage V H p) :
    (T.onHodgeDefectImage z).1 = T.pair.defectOperator z.1 := by
  rfl

/-- Composition in genuine graded geometry descends to composition on realized
Hodge-defect sectors. -/
noncomputable def comp
    (T : HodgeStableGradedOperator V H q r)
    (U : HodgeStableGradedOperator V H p q) :
    HodgeStableGradedOperator V H p r where
  pair := T.pair.comp U.pair
  hodge := by
    intro alpha halpha
    exact T.hodge (U.pair.cohomologyOperator alpha) (U.hodge alpha halpha)

/-- The realized defect action respects graded composition exactly. -/
theorem onHodgeDefectImage_comp
    (T : HodgeStableGradedOperator V H q r)
    (U : HodgeStableGradedOperator V H p q) :
    (T.comp U).onHodgeDefectImage =
      T.onHodgeDefectImage.comp U.onHodgeDefectImage := by
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  change (T.pair.comp U.pair).defectOperator z.1 =
    T.pair.defectOperator (U.pair.defectOperator z.1)
  rw [GradedCycleClassOperatorPair.defectOperator_comp]
  rfl

end HodgeStableGradedOperator

/-- The genuine principal cut is a Hodge-stable graded operator. -/
noncomputable def principalCutHodgeStable
    (G : GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (p : Nat) : HodgeStableGradedOperator V H p (p + 1) where
  pair := G.principalCutPair p
  hodge := G.principalCut_hodge p

/-- Hence the real principal-cut geometry acts on the realized Hodge-defect
sectors, not merely on the ambient quotient. -/
noncomputable def principalCutOnHodgeDefectImage
    (G : GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (p : Nat) :
    HodgeDefectImage V H p →ₗ[ℚ] HodgeDefectImage V H (p + 1) :=
  (principalCutHodgeStable G p).onHodgeDefectImage

/-- At the least bad weight, every strictly lower realized Hodge-defect sector
is literally zero. -/
theorem firstAtomicDefect_lower_HodgeDefectImage_eq_bot
    (F : FirstAtomicDefectWeight V H)
    (q : Nat)
    (hq : q < F.weight) :
    HodgeDefectImage V H q = ⊥ :=
  HodgeDefectImage_eq_bot_iff.mpr (F.lower_zero q hq)

/-- The least bad weight itself has a nontrivial realized defect sector. -/
theorem firstAtomicDefect_HodgeDefectImage_ne_bot
    (F : FirstAtomicDefectWeight V H) :
    HodgeDefectImage V H F.weight ≠ ⊥ :=
  HodgeDefectImage_ne_bot_iff.mpr F.defect_ne_zero

#check HodgeDefectImage
#check HodgeDefectImage_eq_bot_iff
#check HodgeDefectImage_ne_bot_iff
#check HodgeStableGradedOperator
#check HodgeStableGradedOperator.onHodge
#check HodgeStableGradedOperator.defect_equivariant
#check HodgeStableGradedOperator.onHodgeDefectImage
#check HodgeStableGradedOperator.onHodgeDefectImage_comp
#check principalCutHodgeStable
#check principalCutOnHodgeDefectImage
#check firstAtomicDefect_lower_HodgeDefectImage_eq_bot
#check firstAtomicDefect_HodgeDefectImage_ne_bot

#print axioms HodgeDefectImage_eq_bot_iff
#print axioms HodgeStableGradedOperator.defect_equivariant
#print axioms HodgeStableGradedOperator.onHodgeDefectImage
#print axioms firstAtomicDefect_lower_HodgeDefectImage_eq_bot
#print axioms firstAtomicDefect_HodgeDefectImage_ne_bot

end GSTClassicalHodgeHodgeDefectImageFunctoriality
