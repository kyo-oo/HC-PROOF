import GSTClassicalHodgeFirstPrimitiveSectorRetraction
import GSTClassicalHodgeGradedFiniteClosedCorrespondence

/-!
# GST CLASSICAL HODGE — FIRST GHOST CORRESPONDENCE COLLISION

The first-failure extinction target can be made completely concrete.

At a local first bad successor `p+1`, take the distinguished trace-zero
primitive tomography ghost `E`.  Use:

* one actual finite closed correspondence `K ⊂ X × X` as a downward native
  transport from codimension `p+1` to codimension `p`;
* its point-generator cycle-class naturality, already promoted by the graded
  correspondence machinery to a genuine quotient map;
* the existing geometric principal-cut operator as the upward transport.

Only two statements are required about the single ghost state:

1. the downward cohomological image of `E.traceZeroClass` is a rational Hodge
   class at weight `p`;
2. cutting it back up recovers a nonzero scalar multiple of the original ghost
   modulo the genuine atomic cycle-class span.

No law is requested on any other Hodge vector.

Because the predecessor weight has zero Hodge defect, the downward ghost defect
is zero.  The upward principal cut therefore still has zero defect, while the
single-state round-trip law says it is a nonzero scalar multiple of the
nonzero ghost defect — contradiction.

This is the narrowest concrete geometric closure target in the current route.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeFirstGhostCorrespondenceCollision

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeAtomicDefectDuality
open GSTClassicalHodgeCrossWeightNativePropagation
open GSTClassicalHodgeCrossWeightAtomicDefectDescent
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgePrimitiveAtomicDefectReduction
open GSTClassicalHodgeTraceZeroPrimitiveTomographyGhost
open GSTClassicalHodgePrimitiveProjectiveDefectModule
open GSTClassicalHodgeFiniteClosedCorrespondence
open GSTClassicalHodgeGradedFiniteClosedCorrespondence

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {G : GeometricCycleClassSpine V H}
variable {D : LefschetzPrimitiveDecomposition G}
variable {T : GSTClassicalHodgeProjectiveDegreeTrace.ProjectiveDegreeTraceSemantics V H}
variable {p : Nat}

/-- One actual finite correspondence realizing a down/up scaled return only on
one distinguished first-failure ghost. -/
structure FirstGhostCorrespondenceReturn
    (A : GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor G T (p + 1))
    (E : TraceZeroPrimitiveTomographyGhost A D)
    (K : FiniteClosedCorrespondence V) where
  naturality : GradedCorrespondencePointNaturality K H (p + 1) p
  ghost_down_hodge :
    naturality.cohomologyOperator E.traceZeroClass.1 ∈
      rationalHodgeSubspace (H.hodgeBigrading p)
  scalar : ℚ
  scalar_ne_zero : scalar ≠ 0
  ghost_roundtrip_mod_atomic :
    (G.principalCutPair p).cohomologyOperator
        (naturality.cohomologyOperator E.traceZeroClass.1) -
      scalar • E.traceZeroClass.1 ∈
        pointCycleClassSpan (p + 1) (H.cycleClass (p + 1))

namespace FirstGhostCorrespondenceReturn

/-- Downward correspondence pair on the actual atomic defect quotient. -/
noncomputable def downPair
    {A : GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor G T (p + 1)}
    {E : TraceZeroPrimitiveTomographyGhost A D}
    {K : FiniteClosedCorrespondence V}
    (R : FirstGhostCorrespondenceReturn A E K) :
    GradedCycleClassOperatorPair V H (p + 1) p :=
  R.naturality.toGradedCycleClassOperatorPair

/-- The correspondence defect image of the ghost is represented by its genuine
cohomological downward image. -/
theorem down_defect_equivariant
    {A : GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor G T (p + 1)}
    {E : TraceZeroPrimitiveTomographyGhost A D}
    {K : FiniteClosedCorrespondence V}
    (R : FirstGhostCorrespondenceReturn A E K) :
    atomicDefectLinearMap V H p
        (⟨R.naturality.cohomologyOperator E.traceZeroClass.1,
          R.ghost_down_hodge⟩ : ClassicalHodgeFiber V H p) =
      R.downPair.defectOperator E.defectState := by
  exact R.downPair.defect_equivariant E.traceZeroClass R.ghost_down_hodge

/-- The one-state modulo-atomic geometric equation becomes an exact scaled
round trip on the ghost defect quotient. -/
theorem ghost_defect_roundtrip
    {A : GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor G T (p + 1)}
    {E : TraceZeroPrimitiveTomographyGhost A D}
    {K : FiniteClosedCorrespondence V}
    (R : FirstGhostCorrespondenceReturn A E K) :
    principalCutDefectOperator G p
        (R.downPair.defectOperator E.defectState) =
      R.scalar • E.defectState := by
  change
    Submodule.Quotient.mk
        ((G.principalCutPair p).cohomologyOperator
          (R.naturality.cohomologyOperator E.traceZeroClass.1)) =
      R.scalar • Submodule.Quotient.mk E.traceZeroClass.1
  have hzero :
      Submodule.Quotient.mk
        ((G.principalCutPair p).cohomologyOperator
            (R.naturality.cohomologyOperator E.traceZeroClass.1) -
          R.scalar • E.traceZeroClass.1) =
        (0 : AtomicDefectSpace V H (p + 1)) :=
    (Submodule.Quotient.mk_eq_zero
      (pointCycleClassSpan (p + 1) (H.cycleClass (p + 1)))).2
      R.ghost_roundtrip_mod_atomic
  have hsub :
      Submodule.Quotient.mk
          ((G.principalCutPair p).cohomologyOperator
            (R.naturality.cohomologyOperator E.traceZeroClass.1)) -
        R.scalar • Submodule.Quotient.mk E.traceZeroClass.1 = 0 := by
    simpa using hzero
  exact sub_eq_zero.mp hsub

/-- **SINGLE-GHOST CORRESPONDENCE COLLISION.**
If the predecessor Hodge defect is zero, no actual finite correspondence can
satisfy the two one-state return laws above for a nonzero trace-zero primitive
ghost. -/
theorem impossible_of_predecessor_defect_zero
    {A : GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor G T (p + 1)}
    {E : TraceZeroPrimitiveTomographyGhost A D}
    {K : FiniteClosedCorrespondence V}
    (R : FirstGhostCorrespondenceReturn A E K)
    (hsource : atomicDefectLinearMap V H p = 0) : False := by
  let beta : ClassicalHodgeFiber V H p :=
    ⟨R.naturality.cohomologyOperator E.traceZeroClass.1,
      R.ghost_down_hodge⟩
  have hbeta : atomicDefectLinearMap V H p beta = 0 := by
    rw [hsource]
    rfl
  have hdown : R.downPair.defectOperator E.defectState = 0 := by
    rw [← R.down_defect_equivariant]
    exact hbeta
  have hup :
      principalCutDefectOperator G p
          (R.downPair.defectOperator E.defectState) = 0 := by
    rw [hdown]
    exact map_zero _
  rw [R.ghost_defect_roundtrip] at hup
  have hinv := congrArg (fun z => R.scalar⁻¹ • z) hup
  have hghost : E.defectState = 0 := by
    simpa [smul_smul, R.scalar_ne_zero] using hinv
  exact E.defectState_ne_zero hghost

/-- At a globally first bad successor weight, such a one-ghost correspondence
return is impossible automatically. -/
theorem firstFailure_forbids_ghost_correspondence_return
    (F : GSTClassicalHodgeFirstPrimitiveProjectiveFailure.FirstAtomicDefectWeight V H)
    (hp : F.weight = p + 1)
    {A : GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor G T (p + 1)}
    {E : TraceZeroPrimitiveTomographyGhost A D}
    {K : FiniteClosedCorrespondence V}
    (R : FirstGhostCorrespondenceReturn A E K) : False := by
  exact R.impossible_of_predecessor_defect_zero
    (GSTClassicalHodgeFirstPrimitiveProjectiveFailure.firstAtomicDefect_predecessor_zero
      F hp)

end FirstGhostCorrespondenceReturn

#check FirstGhostCorrespondenceReturn
#check FirstGhostCorrespondenceReturn.downPair
#check FirstGhostCorrespondenceReturn.down_defect_equivariant
#check FirstGhostCorrespondenceReturn.ghost_defect_roundtrip
#check FirstGhostCorrespondenceReturn.impossible_of_predecessor_defect_zero
#check FirstGhostCorrespondenceReturn.firstFailure_forbids_ghost_correspondence_return

#print axioms FirstGhostCorrespondenceReturn.down_defect_equivariant
#print axioms FirstGhostCorrespondenceReturn.ghost_defect_roundtrip
#print axioms FirstGhostCorrespondenceReturn.impossible_of_predecessor_defect_zero
#print axioms FirstGhostCorrespondenceReturn.firstFailure_forbids_ghost_correspondence_return

end GSTClassicalHodgeFirstGhostCorrespondenceCollision
