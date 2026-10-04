import GSTClassicalHodgePrincipalCutFlagCorrespondenceDescent
import GSTClassicalHodgeSeparatorFiniteGSTPoincare
import GSTClassicalHodgeUniversalFirstFailurePureTransposeClosure

/-!
# GST CLASSICAL HODGE — PRINCIPAL-CUT FIRST-FAILURE INCIDENCE BRIDGE

This file binds the current first-failure pure-transpose frontier to the actual
principal-cut incidence geometry already constructed in the repository.

The key point is orientation.  A principal-cut flag realization carries an
actual bi-finite correspondence whose forward native action goes from weight
`p` to weight `p+1`.  Its genuine algebraic transpose is therefore the exact
kind of correspondence needed by the first-failure route: it goes from the
obstructed successor weight `p+1` down to the already-good predecessor `p`.

All purely internal pieces are already present:

* the reverse native flag is literally the graded native operator of the
  genuine algebraic transpose;
* the atomic separator read of the obstructed basis state is literally a
  nonzero finite-GST Poincare top pairing;
* once one genuine transpose round trip has that same scalar read, the existing
  pure-transversality theorem kills the first failure.

Accordingly the bridge below does not introduce matrix-unit reachability,
Hodge surjectivity, a global inverse, a principal-cut comparison, or an
arbitrary native operator.  It isolates one scalar cross-cosmology identity
for the *actual principal-cut incidence transpose*.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgePrincipalCutFirstFailureIncidenceBridge

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicDefectDuality
open GSTClassicalHodgeSingleSheetCrown
open GSTClassicalHodgeFiniteClosedCorrespondenceTranspose
open GSTClassicalHodgeFirstGhostTransposeAdjointGeometry
open GSTClassicalHodgeFirstFailurePoincareReadCollision
open GSTClassicalHodgeFirstFailureBiFiniteTransposePureTransversality
open GSTClassicalHodgeUniversalFirstFailurePureTransposeClosure
open GSTClassicalHodgePrincipalCutIncidenceTransposeCosmology
open GSTClassicalHodgePrincipalCutFlagCorrespondenceDescent
open GSTClassicalHodgeSeparatorFiniteGSTPoincare
open GSTClassicalHodgeLimitlessSeparatorGhost
open GSTClassicalHodgeFiniteSupportChart

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/--
The concrete remaining coupling on one first-failure sheet.

`R` is not an arbitrary correspondence: it is an actual principal-cut flag
bi-finite realization.  The correspondence sent into the first-failure engine
is its genuine factor-swap transpose `R.correspondence.transposeBiFinite`.

Besides the ordinary graded Betti naturality and the requirement that the
returned state is Hodge at the predecessor, the sole new mathematical field is
`roundtrip_read_eq_finiteGSTPoincare`: the separator read of the genuine
transpose round trip is the already-canonical finite-GST Poincare observable of
the obstructed sheet.
-/
structure PrincipalCutFirstFailureIncidenceCoupling
    (p : Nat)
    (i : ClassicalHodgeBasisIndex V H (p + 1))
    (S : BasisAtomicSeparator V H (p + 1) i)
    (sigma : Finset (CodimensionPoint V.X p))
    (R : PrincipalCutFlagBiFiniteRealization V p sigma) where
  naturality :
    BiFiniteTransposeNaturality
      R.correspondence.transposeBiFinite (p + 1) p
  return_hodge :
    naturality.forward.cohomologyOperator
        (classicalHodgeBasis V H (p + 1) i).1 ∈
      rationalHodgeSubspace (H.hodgeBigrading p)
  roundtrip_read_eq_finiteGSTPoincare :
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

namespace PrincipalCutFirstFailureIncidenceCoupling

/-- The forward native operator of the first-failure correspondence is exactly
the finite reverse principal-cut flag.  This is the geometric anchor that
prevents the bridge from silently using an arbitrary native operator. -/
theorem forward_native_eq_localTranspose
    {i : ClassicalHodgeBasisIndex V H (p + 1)}
    {S : BasisAtomicSeparator V H (p + 1) i}
    {sigma : Finset (CodimensionPoint V.X p)}
    {R : PrincipalCutFlagBiFiniteRealization V p sigma}
    (C : PrincipalCutFirstFailureIncidenceCoupling p i S sigma R) :
    R.correspondence.transposeBiFinite.toFiniteClosedCorrespondence
        |>.gradedNativeCycleOperator (p + 1) p =
      localTransposeNativeOperator V p sigma := by
  exact R.transpose_cycleOperator_eq_localTranspose

/-- The one scalar GST/Poincare coupling immediately supplies the nonzero
separator read required by the minimal genuine-correspondence frontier. -/
theorem separator_transverse
    {i : ClassicalHodgeBasisIndex V H (p + 1)}
    {S : BasisAtomicSeparator V H (p + 1) i}
    {sigma : Finset (CodimensionPoint V.X p)}
    {R : PrincipalCutFlagBiFiniteRealization V p sigma}
    (C : PrincipalCutFirstFailureIncidenceCoupling p i S sigma R) :
    S.detector
      (C.naturality.transpose.cohomologyOperator
        (C.naturality.forward.cohomologyOperator
          (classicalHodgeBasis V H (p + 1) i).1)) ≠ 0 := by
  rw [C.roundtrip_read_eq_finiteGSTPoincare]
  exact basisSeparator_finiteGSTPoincare_ne_zero S

/-- Forget only the principal-cut anchoring after it has done its job.  The
result is exactly the repository's minimal first-failure pure-transverse packet
for the genuine algebraic transpose of the principal-cut incidence
correspondence. -/
noncomputable def toPureTranspose
    {i : ClassicalHodgeBasisIndex V H (p + 1)}
    {S : BasisAtomicSeparator V H (p + 1) i}
    {sigma : Finset (CodimensionPoint V.X p)}
    {R : PrincipalCutFlagBiFiniteRealization V p sigma}
    (C : PrincipalCutFirstFailureIncidenceCoupling p i S sigma R) :
    FirstFailureBiFiniteTransposePureTransverse
      (V := V) (H := H) p i S R.correspondence.transposeBiFinite where
  naturality := C.naturality
  return_hodge := C.return_hodge
  separator_transverse := C.separator_transverse

/-- At an actual least bad successor, the principal-cut incidence coupling is
impossible.  This is the local collision in its most concrete current form. -/
theorem firstFailure_forbids_principalCutIncidenceCoupling
    (F : GSTClassicalHodgeFirstPrimitiveProjectiveFailure.FirstAtomicDefectWeight V H)
    (hp : F.weight = p + 1)
    {i : ClassicalHodgeBasisIndex V H (p + 1)}
    {S : BasisAtomicSeparator V H (p + 1) i}
    {sigma : Finset (CodimensionPoint V.X p)}
    {R : PrincipalCutFlagBiFiniteRealization V p sigma}
    (C : PrincipalCutFirstFailureIncidenceCoupling p i S sigma R) : False :=
  C.toPureTranspose.firstFailure_forbids_biFiniteTransposePureTransverse F hp

end PrincipalCutFirstFailureIncidenceCoupling

/-- A first-failure witness whose correspondence is not arbitrary but comes
from one actual principal-cut incidence flag. -/
def FirstFailurePrincipalCutIncidenceWitness
    (F : GSTClassicalHodgeFirstPrimitiveProjectiveFailure.FirstAtomicDefectWeight V H) : Prop :=
  ∃ p : Nat,
  ∃ hp : F.weight = p + 1,
  ∃ i : ClassicalHodgeBasisIndex V H (p + 1),
  ∃ hi : atomicDefectLinearMap V H (p + 1)
      (classicalHodgeBasis V H (p + 1) i) ≠ 0,
  ∃ sigma : Finset (CodimensionPoint V.X p),
  ∃ R : PrincipalCutFlagBiFiniteRealization V p sigma,
    Nonempty
      (PrincipalCutFirstFailureIncidenceCoupling
        (V := V) (H := H) p i
        (basisSeparatorOfDefectNeZero i hi) sigma R)

/-- The concrete principal-cut incidence witness manufactures the exact minimal
pure-transpose witness already known to close the first-failure route. -/
theorem firstFailurePrincipalCutIncidenceWitness_to_pureTranspose
    (F : GSTClassicalHodgeFirstPrimitiveProjectiveFailure.FirstAtomicDefectWeight V H)
    (hF : FirstFailurePrincipalCutIncidenceWitness (V := V) (H := H) F) :
    FirstFailurePureTransposeWitness F := by
  rcases hF with ⟨p, hp, i, hi, sigma, R, hC⟩
  rcases hC with ⟨C⟩
  exact ⟨p, hp, i, hi, R.correspondence.transposeBiFinite, ⟨C.toPureTranspose⟩⟩

/-- **PRINCIPAL-CUT FIRST-FAILURE FINALE.**
If weight zero is defect-free and the independently geometric principal-cut
incidence construction supplies the above one-observable coupling for every
putative first failure, then the complete Stage-2G Hodge statement follows.

All contradiction machinery is discharged by the existing pure-transpose
closure; the only genuinely new mathematical burden is the scalar
cross-cosmology identity stored in the incidence coupling. -/
theorem bigradedBettiHodge_of_firstFailurePrincipalCutIncidenceWitness
    (hzero : atomicDefectLinearMap V H 0 = 0)
    (returns :
      ∀ F : GSTClassicalHodgeFirstPrimitiveProjectiveFailure.FirstAtomicDefectWeight V H,
        FirstFailurePrincipalCutIncidenceWitness (V := V) (H := H) F) :
    BigradedBettiHodgeStatement V H := by
  apply bigradedBettiHodge_of_firstFailurePureTransposeWitness hzero
  intro F
  exact firstFailurePrincipalCutIncidenceWitness_to_pureTranspose F (returns F)

#check PrincipalCutFirstFailureIncidenceCoupling
#check PrincipalCutFirstFailureIncidenceCoupling.forward_native_eq_localTranspose
#check PrincipalCutFirstFailureIncidenceCoupling.separator_transverse
#check PrincipalCutFirstFailureIncidenceCoupling.toPureTranspose
#check PrincipalCutFirstFailureIncidenceCoupling.firstFailure_forbids_principalCutIncidenceCoupling
#check FirstFailurePrincipalCutIncidenceWitness
#check firstFailurePrincipalCutIncidenceWitness_to_pureTranspose
#check bigradedBettiHodge_of_firstFailurePrincipalCutIncidenceWitness

#print axioms PrincipalCutFirstFailureIncidenceCoupling.separator_transverse
#print axioms PrincipalCutFirstFailureIncidenceCoupling.toPureTranspose
#print axioms PrincipalCutFirstFailureIncidenceCoupling.firstFailure_forbids_principalCutIncidenceCoupling
#print axioms firstFailurePrincipalCutIncidenceWitness_to_pureTranspose
#print axioms bigradedBettiHodge_of_firstFailurePrincipalCutIncidenceWitness

end GSTClassicalHodgePrincipalCutFirstFailureIncidenceBridge
