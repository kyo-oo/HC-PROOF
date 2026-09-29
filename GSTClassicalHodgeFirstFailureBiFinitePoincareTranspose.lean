import GSTClassicalHodgeFirstFailurePoincareReadCollision
import GSTClassicalHodgeFirstGhostTransposeAdjointGeometry

/-!
# GST CLASSICAL HODGE — FIRST-FAILURE BI-FINITE POINCARE TRANSPOSE

The one-read first-failure collision is now bound to actual correspondence
geometry.

Let `K` be a genuine bi-finite closed correspondence on `X x_C X`.  The repo
already constructs its algebraic transpose `K^t` by the actual factor-swap and
packages pointwise cycle-class naturality for both directions.

For one obstructed basis sheet at the least bad weight we require only two
one-state geometric identities:

1. `K^t` on the returned basis state agrees with the already-genuine principal
   cut on that state;
2. the atomic separator read of `K^t K` on that basis state equals the finite
   GST Poincare top pairing which represents the same separator observable.

The second identity is a one-observable projection formula, not a global
adjoint law.  Combining the two identities manufactures the exact
`FirstFailurePoincareReadReturn` packet.  The preceding collision then rules out
the first failure.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeFirstFailureBiFinitePoincareTranspose

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeSingleSheetCrown
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeFiniteClosedCorrespondenceTranspose
open GSTClassicalHodgeFirstGhostTransposeAdjointGeometry
open GSTClassicalHodgeFirstFailurePoincareReadCollision
open GSTClassicalHodgeLimitlessSeparatorGhost
open GSTClassicalHodgeFiniteSupportChart

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Genuine bi-finite transpose geometry for one obstructed basis sheet,
requiring only a one-state principal-cut identification and one separator-level
Poincare projection formula. -/
structure FirstFailureBiFinitePoincareTranspose
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
  separator_poincare_projection :
    S.detector
        (naturality.transpose.cohomologyOperator
          (naturality.forward.cohomologyOperator
            (classicalHodgeBasis V H (p + 1) i).1)) =
      rationalWorldTopPairing
        (fiberedSupportWorld
          (fiberedWeightCoordinates V H (p + 1)
            (classicalHodgeBasis V H (p + 1) i)))
        (dualizedSupportProbe
          (fiberedWeightCoordinates V H (p + 1)
            (classicalHodgeBasis V H (p + 1) i))
          (separatorFiberedProbe
            (V := V) (H := H) (p + 1) S.detector))

namespace FirstFailureBiFinitePoincareTranspose

/-- The actual forward correspondence furnishes the genuine graded return pair
used by the one-read collision. -/
noncomputable def toPoincareReadReturn
    {G : GeometricCycleClassSpine V H}
    {i : ClassicalHodgeBasisIndex V H (p + 1)}
    {S : BasisAtomicSeparator V H (p + 1) i}
    {K : BiFiniteClosedCorrespondence V}
    (R : FirstFailureBiFinitePoincareTranspose G p i S K) :
    FirstFailurePoincareReadReturn G p i S where
  returnPair := R.naturality.forward.toGradedCycleClassOperatorPair
  return_hodge := R.return_hodge
  poincare_read_reciprocity := by
    rw [← R.transpose_matches_principalCut]
    exact R.separator_poincare_projection

/-- First-failure contradiction for one actual bi-finite correspondence and its
genuine transpose. -/
theorem firstFailure_forbids_biFinitePoincareTranspose
    {G : GeometricCycleClassSpine V H}
    (F : GSTClassicalHodgeFirstPrimitiveProjectiveFailure.FirstAtomicDefectWeight V H)
    (hp : F.weight = p + 1)
    {i : ClassicalHodgeBasisIndex V H (p + 1)}
    {S : BasisAtomicSeparator V H (p + 1) i}
    {K : BiFiniteClosedCorrespondence V}
    (R : FirstFailureBiFinitePoincareTranspose G p i S K) : False :=
  R.toPoincareReadReturn.firstFailure_forbids_poincareReadReturn F hp

end FirstFailureBiFinitePoincareTranspose

/-- **BI-FINITE POINCARE-TRANSPOSE HODGE CROWN.**
If every possible microscopic successor separator admits one actual bi-finite
correspondence whose genuine transpose satisfies the two one-state Poincare
identities above, the full Stage-2G Hodge statement follows. -/
theorem bigradedBettiHodge_of_biFinitePoincareTransposeFamily
    (G : GeometricCycleClassSpine V H)
    (hzero : GSTClassicalHodgeAtomicDefectDuality.atomicDefectLinearMap V H 0 = 0)
    (R : ∀ p : Nat,
      ∀ i : ClassicalHodgeBasisIndex V H (p + 1),
      ∀ S : BasisAtomicSeparator V H (p + 1) i,
        ∃ K : BiFiniteClosedCorrespondence V,
          Nonempty (FirstFailureBiFinitePoincareTranspose G p i S K)) :
    BigradedBettiHodgeStatement V H := by
  apply bigradedBettiHodge_of_poincareReadReturnFamily G hzero
  intro q i S
  rcases R q i S with ⟨K, hK⟩
  rcases hK with ⟨RK⟩
  exact ⟨RK.toPoincareReadReturn⟩

#check FirstFailureBiFinitePoincareTranspose
#check FirstFailureBiFinitePoincareTranspose.toPoincareReadReturn
#check FirstFailureBiFinitePoincareTranspose.firstFailure_forbids_biFinitePoincareTranspose
#check bigradedBettiHodge_of_biFinitePoincareTransposeFamily

#print axioms FirstFailureBiFinitePoincareTranspose.toPoincareReadReturn
#print axioms FirstFailureBiFinitePoincareTranspose.firstFailure_forbids_biFinitePoincareTranspose
#print axioms bigradedBettiHodge_of_biFinitePoincareTransposeFamily

end GSTClassicalHodgeFirstFailureBiFinitePoincareTranspose
