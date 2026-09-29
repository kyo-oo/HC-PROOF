import GSTClassicalHodgeFirstFailureBiFinitePoincareTranspose

/-!
# GST CLASSICAL HODGE — FIRST-FAILURE BI-FINITE TRANSPOSE TRANSVERSALITY

The exact finite-GST Poincare projection formula is stronger than the
first-failure contradiction actually needs.

At a least bad successor weight, let `S` be the microscopic atomic separator
of one genuinely defective basis sheet.  Suppose an actual bi-finite closed
correspondence `K` provides a Hodge-preserving return to the predecessor, and
its genuine factor-swap transpose agrees with the principal-cut forward map on
that returned one state.

The predecessor is already algebraic.  Therefore the principal-cut image of
the returned state is algebraic at the successor weight, and `S` must read it
as zero.

Hence the contradiction requires only that the actual transpose round trip be
TRANSVERSE to the same separator:

    S( K^t K (e_i) ) != 0.

No exact value, normalization scalar, Poincare equality, global adjoint law,
coisometry, quotient inverse, or matrix-unit realization is required.  The
finite-GST Poincare theorem remains the canonical mechanism expected to prove
this transversality, but the closure theorem itself consumes only nonvanishing.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeFirstFailureBiFiniteTransposeTransversality

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeSingleSheetCrown
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeFiniteClosedCorrespondenceTranspose
open GSTClassicalHodgeFirstGhostTransposeAdjointGeometry
open GSTClassicalHodgeFirstFailurePoincareReadCollision
open GSTClassicalHodgeFirstPrimitiveProjectiveFailure

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Minimal actual-correspondence packet: one Hodge-preserving forward return,
one one-state transpose/principal-cut identification, and one nonzero separator
read of the genuine transpose round trip. -/
structure FirstFailureBiFiniteTransposeTransverse
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (i : ClassicalHodgeBasisIndex V H (p + 1))
    (S : BasisAtomicSeparator V H (p + 1) i)
    (K : BiFiniteClosedCorrespondence V) where
  naturality : BiFiniteTransposeNaturality K (p + 1) p
  return_hodge :
    naturality.forward.cohomologyOperator
        (classicalHodgeBasis V H (p + 1) i).1 ∈
      rationalHodgeSubspace (H.hodgeBigrading p)
  transpose_matches_principalCut :
    naturality.transpose.cohomologyOperator
        (naturality.forward.cohomologyOperator
          (classicalHodgeBasis V H (p + 1) i).1) =
      (G.principalCutPair p).cohomologyOperator
        (naturality.forward.cohomologyOperator
          (classicalHodgeBasis V H (p + 1) i).1)
  separator_transverse :
    S.detector
      (naturality.transpose.cohomologyOperator
        (naturality.forward.cohomologyOperator
          (classicalHodgeBasis V H (p + 1) i).1)) ≠ 0

namespace FirstFailureBiFiniteTransposeTransverse

/-- Package the actual forward correspondence as the one-state return consumed
by the first-failure algebraicity argument. -/
noncomputable def returnedHodgeClass
    {G : GeometricCycleClassSpine V H}
    {i : ClassicalHodgeBasisIndex V H (p + 1)}
    {S : BasisAtomicSeparator V H (p + 1) i}
    {K : BiFiniteClosedCorrespondence V}
    (R : FirstFailureBiFiniteTransposeTransverse G p i S K) :
    ClassicalHodgeFiber V H p :=
  ⟨R.naturality.forward.cohomologyOperator
      (classicalHodgeBasis V H (p + 1) i).1,
    R.return_hodge⟩

/-- If the predecessor defect map vanishes, the returned Hodge state is in the
complete predecessor atomic cycle-class span. -/
theorem returned_atomic
    {G : GeometricCycleClassSpine V H}
    {i : ClassicalHodgeBasisIndex V H (p + 1)}
    {S : BasisAtomicSeparator V H (p + 1) i}
    {K : BiFiniteClosedCorrespondence V}
    (R : FirstFailureBiFiniteTransposeTransverse G p i S K)
    (hsource : GSTClassicalHodgeAtomicDefectDuality.atomicDefectLinearMap V H p = 0) :
    R.returnedHodgeClass.1 ∈
      GSTClassicalHodgeAtomicSpan.pointCycleClassSpan p (H.cycleClass p) := by
  have hz :
      GSTClassicalHodgeAtomicDefectDuality.atomicDefectLinearMap V H p
        R.returnedHodgeClass = 0 := by
    rw [hsource]
    rfl
  rw [GSTClassicalHodgeAtomicDefectDuality.atomicDefectLinearMap_apply] at hz
  exact (Submodule.Quotient.mk_eq_zero
    (GSTClassicalHodgeAtomicSpan.pointCycleClassSpan p (H.cycleClass p))).1 hz

/-- Principal-cut cycle naturality carries the returned algebraic predecessor
state back into the successor atomic span. -/
theorem principalCut_roundtrip_atomic
    {G : GeometricCycleClassSpine V H}
    {i : ClassicalHodgeBasisIndex V H (p + 1)}
    {S : BasisAtomicSeparator V H (p + 1) i}
    {K : BiFiniteClosedCorrespondence V}
    (R : FirstFailureBiFiniteTransposeTransverse G p i S K)
    (hsource : GSTClassicalHodgeAtomicDefectDuality.atomicDefectLinearMap V H p = 0) :
    (G.principalCutPair p).cohomologyOperator R.returnedHodgeClass.1 ∈
      GSTClassicalHodgeAtomicSpan.pointCycleClassSpan (p + 1)
        (H.cycleClass (p + 1)) := by
  exact (G.principalCutPair p).atomicSpanStable
    R.returnedHodgeClass.1 (R.returned_atomic hsource)

/-- Therefore the separator reads the actual transpose round trip as zero once
the transpose is identified with principal cut on that single returned state. -/
theorem transpose_roundtrip_read_eq_zero
    {G : GeometricCycleClassSpine V H}
    {i : ClassicalHodgeBasisIndex V H (p + 1)}
    {S : BasisAtomicSeparator V H (p + 1) i}
    {K : BiFiniteClosedCorrespondence V}
    (R : FirstFailureBiFiniteTransposeTransverse G p i S K)
    (hsource : GSTClassicalHodgeAtomicDefectDuality.atomicDefectLinearMap V H p = 0) :
    S.detector
      (R.naturality.transpose.cohomologyOperator
        (R.naturality.forward.cohomologyOperator
          (classicalHodgeBasis V H (p + 1) i).1)) = 0 := by
  rw [R.transpose_matches_principalCut]
  have hker :
      GSTClassicalHodgeAtomicSpan.pointCycleClassSpan (p + 1)
          (H.cycleClass (p + 1)) ≤ LinearMap.ker S.detector :=
    (GSTClassicalHodgeAtomicAnnihilator.annihilatesPointCycles_iff_atomicSpan_le_ker
      (p + 1) (H.cycleClass (p + 1)) S.detector).mp S.annihilates_atoms
  exact hker (R.principalCut_roundtrip_atomic hsource)

/-- **TRANSVERSALITY COLLISION.**  At a good predecessor the transpose round
trip is forced to be separator-invisible, contradicting the supplied nonzero
actual-correspondence transverse read. -/
theorem impossible_of_predecessor_defect_zero
    {G : GeometricCycleClassSpine V H}
    {i : ClassicalHodgeBasisIndex V H (p + 1)}
    {S : BasisAtomicSeparator V H (p + 1) i}
    {K : BiFiniteClosedCorrespondence V}
    (R : FirstFailureBiFiniteTransposeTransverse G p i S K)
    (hsource : GSTClassicalHodgeAtomicDefectDuality.atomicDefectLinearMap V H p = 0) : False := by
  exact R.separator_transverse (R.transpose_roundtrip_read_eq_zero hsource)

/-- At the globally least bad successor weight this minimal bi-finite
transversality packet cannot exist. -/
theorem firstFailure_forbids_biFiniteTransposeTransverse
    {G : GeometricCycleClassSpine V H}
    (F : FirstAtomicDefectWeight V H)
    (hp : F.weight = p + 1)
    {i : ClassicalHodgeBasisIndex V H (p + 1)}
    {S : BasisAtomicSeparator V H (p + 1) i}
    {K : BiFiniteClosedCorrespondence V}
    (R : FirstFailureBiFiniteTransposeTransverse G p i S K) : False :=
  R.impossible_of_predecessor_defect_zero
    (firstAtomicDefect_predecessor_zero F hp)

end FirstFailureBiFiniteTransposeTransverse

/-- Exact Poincare-read packets automatically give the weaker transversality
packet because the finite GST separator observable is already nonzero. -/
noncomputable def
    GSTClassicalHodgeFirstFailureBiFinitePoincareTranspose.FirstFailureBiFinitePoincareTranspose.toTransverse
    {G : GeometricCycleClassSpine V H}
    {i : ClassicalHodgeBasisIndex V H (p + 1)}
    {S : BasisAtomicSeparator V H (p + 1) i}
    {K : BiFiniteClosedCorrespondence V}
    (R : GSTClassicalHodgeFirstFailureBiFinitePoincareTranspose.FirstFailureBiFinitePoincareTranspose
      G p i S K) :
    FirstFailureBiFiniteTransposeTransverse G p i S K where
  naturality := R.naturality
  return_hodge := R.return_hodge
  transpose_matches_principalCut := R.transpose_matches_principalCut
  separator_transverse := by
    rw [R.separator_poincare_projection]
    exact GSTClassicalHodgeSeparatorFiniteGSTPoincare.basisSeparator_finiteGSTPoincare_ne_zero S

/-- **MINIMAL BI-FINITE TRANSVERSALITY HODGE CROWN.**
Hodge follows if every microscopic successor separator admits one actual
bi-finite correspondence whose one-state transpose round trip is nonzero to
that separator and agrees with principal cut on the returned state. -/
theorem bigradedBettiHodge_of_biFiniteTransposeTransverseFamily
    (G : GeometricCycleClassSpine V H)
    (hzero : GSTClassicalHodgeAtomicDefectDuality.atomicDefectLinearMap V H 0 = 0)
    (R : ∀ p : Nat,
      ∀ i : ClassicalHodgeBasisIndex V H (p + 1),
      ∀ S : BasisAtomicSeparator V H (p + 1) i,
        ∃ K : BiFiniteClosedCorrespondence V,
          Nonempty (FirstFailureBiFiniteTransposeTransverse G p i S K)) :
    BigradedBettiHodgeStatement V H := by
  by_contra hnot
  let F := firstAtomicDefectWeightOfFailure
    (V := V) (H := H) hzero hnot
  obtain ⟨q, hq⟩ := firstAtomicDefectWeight_eq_succ F
  have hbad :
      GSTClassicalHodgeAtomicDefectDuality.atomicDefectLinearMap V H (q + 1) ≠ 0 := by
    simpa [hq] using F.defect_ne_zero
  obtain ⟨i, hi⟩ :=
    GSTClassicalHodgeFirstFailurePoincareReadCollision.exists_basisDefect_ne_zero
      (V := V) (H := H) hbad
  let S : BasisAtomicSeparator V H (q + 1) i :=
    GSTClassicalHodgeFirstFailurePoincareReadCollision.basisSeparatorOfDefectNeZero i hi
  rcases R q i S with ⟨K, hK⟩
  rcases hK with ⟨RK⟩
  exact RK.firstFailure_forbids_biFiniteTransposeTransverse F hq

#check FirstFailureBiFiniteTransposeTransverse
#check FirstFailureBiFiniteTransposeTransverse.transpose_roundtrip_read_eq_zero
#check FirstFailureBiFiniteTransposeTransverse.impossible_of_predecessor_defect_zero
#check GSTClassicalHodgeFirstFailureBiFinitePoincareTranspose.FirstFailureBiFinitePoincareTranspose.toTransverse
#check bigradedBettiHodge_of_biFiniteTransposeTransverseFamily

#print axioms FirstFailureBiFiniteTransposeTransverse.transpose_roundtrip_read_eq_zero
#print axioms FirstFailureBiFiniteTransposeTransverse.impossible_of_predecessor_defect_zero
#print axioms bigradedBettiHodge_of_biFiniteTransposeTransverseFamily

end GSTClassicalHodgeFirstFailureBiFiniteTransposeTransversality
