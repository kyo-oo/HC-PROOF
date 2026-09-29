import GSTClassicalHodgeFirstFailureBiFiniteTransposeTransversality

/-!
# GST CLASSICAL HODGE — PURE BI-FINITE TRANSPOSE TRANSVERSALITY

The previous bi-finite transversality criterion still compared the genuine
transpose with the principal-cut operator on one returned state.  That
comparison is unnecessary.

At the globally least bad successor weight `p+1`, every rational Hodge class at
weight `p` is already algebraic.  Hence if the forward half of an actual
bi-finite correspondence sends the obstructed basis sheet into the predecessor
Hodge fiber, that returned state is an actual cycle-class value.

But the ACTUAL factor-swap transpose is itself a graded cycle-class-natural
correspondence.  Therefore it sends that returned algebraic state back into the
actual cycle-class range at weight `p+1`.  Every atomic separator annihilates
that whole range.

Thus the first-failure contradiction needs only one genuinely geometric
nonvanishing statement:

    S( K^t K (e_i) ) != 0.

No principal-cut comparison survives.  No scalar, Poincare equality, adjoint
law, quotient inverse, matrix unit, or global operator identity survives.

This is the minimal actual-correspondence formulation reached by the current
GST first-failure cosmology.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeFirstFailureBiFiniteTransposePureTransversality

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeAtomicDefectDuality
open GSTClassicalHodgeAtomicAnnihilator
open GSTClassicalHodgeSingleSheetCrown
open GSTClassicalHodgeFiniteClosedCorrespondenceTranspose
open GSTClassicalHodgeFirstGhostTransposeAdjointGeometry
open GSTClassicalHodgeCrossWeightNativePropagation
open GSTClassicalHodgeFirstPrimitiveProjectiveFailure
open GSTClassicalHodgeFirstFailurePoincareReadCollision

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Minimal first-failure geometric packet.  The correspondence and its actual
transpose are both pointwise cycle-class natural.  The forward image of the
obstructed basis sheet only has to remain Hodge at the good predecessor
weight, while the full transpose round trip must be visible to the separator. -/
structure FirstFailureBiFiniteTransposePureTransverse
    (p : Nat)
    (i : ClassicalHodgeBasisIndex V H (p + 1))
    (S : BasisAtomicSeparator V H (p + 1) i)
    (K : BiFiniteClosedCorrespondence V) where
  naturality : BiFiniteTransposeNaturality K (p + 1) p
  return_hodge :
    naturality.forward.cohomologyOperator
        (classicalHodgeBasis V H (p + 1) i).1 ∈
      rationalHodgeSubspace (H.hodgeBigrading p)
  separator_transverse :
    S.detector
      (naturality.transpose.cohomologyOperator
        (naturality.forward.cohomologyOperator
          (classicalHodgeBasis V H (p + 1) i).1)) ≠ 0

namespace FirstFailureBiFiniteTransposePureTransverse

/-- The forward image, bundled as a predecessor Hodge class. -/
noncomputable def returnedHodgeClass
    {i : ClassicalHodgeBasisIndex V H (p + 1)}
    {S : BasisAtomicSeparator V H (p + 1) i}
    {K : BiFiniteClosedCorrespondence V}
    (R : FirstFailureBiFiniteTransposePureTransverse
      (V := V) (H := H) p i S K) :
    ClassicalHodgeFiber V H p :=
  ⟨R.naturality.forward.cohomologyOperator
      (classicalHodgeBasis V H (p + 1) i).1,
    R.return_hodge⟩

/-- If the predecessor defect map vanishes, the returned Hodge state belongs to
its complete atomic cycle-class span. -/
theorem returned_atomic
    {i : ClassicalHodgeBasisIndex V H (p + 1)}
    {S : BasisAtomicSeparator V H (p + 1) i}
    {K : BiFiniteClosedCorrespondence V}
    (R : FirstFailureBiFiniteTransposePureTransverse
      (V := V) (H := H) p i S K)
    (hsource : atomicDefectLinearMap V H p = 0) :
    R.returnedHodgeClass.1 ∈
      pointCycleClassSpan p (H.cycleClass p) := by
  have hz : atomicDefectLinearMap V H p R.returnedHodgeClass = 0 := by
    rw [hsource]
    rfl
  rw [atomicDefectLinearMap_apply] at hz
  exact (Submodule.Quotient.mk_eq_zero
    (pointCycleClassSpan p (H.cycleClass p))).1 hz

/-- The genuine transpose automatically sends the returned algebraic class
back into the successor cycle-class range; no comparison with principal cut is
required. -/
theorem transpose_roundtrip_atomic
    {i : ClassicalHodgeBasisIndex V H (p + 1)}
    {S : BasisAtomicSeparator V H (p + 1) i}
    {K : BiFiniteClosedCorrespondence V}
    (R : FirstFailureBiFiniteTransposePureTransverse
      (V := V) (H := H) p i S K)
    (hsource : atomicDefectLinearMap V H p = 0) :
    R.naturality.transpose.cohomologyOperator R.returnedHodgeClass.1 ∈
      pointCycleClassSpan (p + 1) (H.cycleClass (p + 1)) := by
  have hreturnedRange : R.returnedHodgeClass.1 ∈
      LinearMap.range (H.cycleClass p) := by
    rw [smoothProjective_cycleClass_range_eq_atomic_span V H p]
    exact R.returned_atomic hsource
  rcases hreturnedRange with ⟨Z, hZ⟩
  have htargetRange :
      R.naturality.transpose.cohomologyOperator R.returnedHodgeClass.1 ∈
        LinearMap.range (H.cycleClass (p + 1)) := by
    refine ⟨R.naturality.transpose.toGradedCycleClassOperatorPair.cycleOperator Z, ?_⟩
    rw [R.naturality.transpose.toGradedCycleClassOperatorPair.cycleClass_natural]
    exact congrArg R.naturality.transpose.cohomologyOperator hZ
  rw [smoothProjective_cycleClass_range_eq_atomic_span V H (p + 1)] at htargetRange
  exact htargetRange

/-- Every atomic separator therefore reads the genuine transpose round trip as
zero at a good predecessor. -/
theorem transpose_roundtrip_read_eq_zero
    {i : ClassicalHodgeBasisIndex V H (p + 1)}
    {S : BasisAtomicSeparator V H (p + 1) i}
    {K : BiFiniteClosedCorrespondence V}
    (R : FirstFailureBiFiniteTransposePureTransverse
      (V := V) (H := H) p i S K)
    (hsource : atomicDefectLinearMap V H p = 0) :
    S.detector
      (R.naturality.transpose.cohomologyOperator
        (R.naturality.forward.cohomologyOperator
          (classicalHodgeBasis V H (p + 1) i).1)) = 0 := by
  have hker :
      pointCycleClassSpan (p + 1) (H.cycleClass (p + 1)) ≤
        LinearMap.ker S.detector :=
    (annihilatesPointCycles_iff_atomicSpan_le_ker
      (p + 1) (H.cycleClass (p + 1)) S.detector).mp S.annihilates_atoms
  change S.detector
      (R.naturality.transpose.cohomologyOperator R.returnedHodgeClass.1) = 0
  exact hker (R.transpose_roundtrip_atomic hsource)

/-- **PURE TRANSPOSE COLLISION.**  At a good predecessor the actual transpose
round trip is forced to be separator-invisible, contradicting the one genuine
transversality condition. -/
theorem impossible_of_predecessor_defect_zero
    {i : ClassicalHodgeBasisIndex V H (p + 1)}
    {S : BasisAtomicSeparator V H (p + 1) i}
    {K : BiFiniteClosedCorrespondence V}
    (R : FirstFailureBiFiniteTransposePureTransverse
      (V := V) (H := H) p i S K)
    (hsource : atomicDefectLinearMap V H p = 0) : False := by
  exact R.separator_transverse (R.transpose_roundtrip_read_eq_zero hsource)

/-- At the least bad successor weight such a pure-transverse bi-finite packet
is impossible. -/
theorem firstFailure_forbids_biFiniteTransposePureTransverse
    (F : FirstAtomicDefectWeight V H)
    (hp : F.weight = p + 1)
    {i : ClassicalHodgeBasisIndex V H (p + 1)}
    {S : BasisAtomicSeparator V H (p + 1) i}
    {K : BiFiniteClosedCorrespondence V}
    (R : FirstFailureBiFiniteTransposePureTransverse
      (V := V) (H := H) p i S K) : False :=
  R.impossible_of_predecessor_defect_zero
    (firstAtomicDefect_predecessor_zero F hp)

end FirstFailureBiFiniteTransposePureTransverse

/-- The previous stronger principal-cut-matching packet forgets immediately to
the pure-transversality packet. -/
noncomputable def
    GSTClassicalHodgeFirstFailureBiFiniteTransposeTransversality.FirstFailureBiFiniteTransposeTransverse.toPureTransverse
    {G : GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H}
    {i : ClassicalHodgeBasisIndex V H (p + 1)}
    {S : BasisAtomicSeparator V H (p + 1) i}
    {K : BiFiniteClosedCorrespondence V}
    (R : GSTClassicalHodgeFirstFailureBiFiniteTransposeTransversality.FirstFailureBiFiniteTransposeTransverse
      G p i S K) :
    FirstFailureBiFiniteTransposePureTransverse
      (V := V) (H := H) p i S K where
  naturality := R.naturality
  return_hodge := R.return_hodge
  separator_transverse := R.separator_transverse

/-- **PURE BI-FINITE TRANSVERSALITY HODGE CROWN.**
The full Stage-2G Hodge statement follows if every microscopic successor
separator admits one actual bi-finite correspondence whose forward action is
Hodge at the predecessor and whose genuine transpose round trip is visible to
that separator. -/
theorem bigradedBettiHodge_of_biFiniteTransposePureTransverseFamily
    (hzero : atomicDefectLinearMap V H 0 = 0)
    (R : ∀ p : Nat,
      ∀ i : ClassicalHodgeBasisIndex V H (p + 1),
      ∀ S : BasisAtomicSeparator V H (p + 1) i,
        ∃ K : BiFiniteClosedCorrespondence V,
          Nonempty (FirstFailureBiFiniteTransposePureTransverse
            (V := V) (H := H) p i S K)) :
    BigradedBettiHodgeStatement V H := by
  by_contra hnot
  let F := firstAtomicDefectWeightOfFailure
    (V := V) (H := H) hzero hnot
  obtain ⟨q, hq⟩ := firstAtomicDefectWeight_eq_succ F
  have hbad : atomicDefectLinearMap V H (q + 1) ≠ 0 := by
    simpa [hq] using F.defect_ne_zero
  obtain ⟨i, hi⟩ :=
    exists_basisDefect_ne_zero (V := V) (H := H) hbad
  let S : BasisAtomicSeparator V H (q + 1) i :=
    basisSeparatorOfDefectNeZero i hi
  rcases R q i S with ⟨K, hK⟩
  rcases hK with ⟨RK⟩
  exact RK.firstFailure_forbids_biFiniteTransposePureTransverse F hq

#check FirstFailureBiFiniteTransposePureTransverse
#check FirstFailureBiFiniteTransposePureTransverse.returned_atomic
#check FirstFailureBiFiniteTransposePureTransverse.transpose_roundtrip_atomic
#check FirstFailureBiFiniteTransposePureTransverse.transpose_roundtrip_read_eq_zero
#check FirstFailureBiFiniteTransposePureTransverse.impossible_of_predecessor_defect_zero
#check GSTClassicalHodgeFirstFailureBiFiniteTransposeTransversality.FirstFailureBiFiniteTransposeTransverse.toPureTransverse
#check bigradedBettiHodge_of_biFiniteTransposePureTransverseFamily

#print axioms FirstFailureBiFiniteTransposePureTransverse.transpose_roundtrip_atomic
#print axioms FirstFailureBiFiniteTransposePureTransverse.impossible_of_predecessor_defect_zero
#print axioms bigradedBettiHodge_of_biFiniteTransposePureTransverseFamily

end GSTClassicalHodgeFirstFailureBiFiniteTransposePureTransversality
