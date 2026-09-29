import GSTClassicalHodgeSeparatorFiniteGSTPoincare
import GSTClassicalHodgeFirstPrimitiveProjectiveFailure
import GSTClassicalHodgeCrossWeightAtomicDefectDescent

/-!
# GST CLASSICAL HODGE — FIRST-FAILURE POINCARE-READ COLLISION

This file removes the Hamel detector and the arbitrary reciprocity scalar from
the first-failure route entirely.

At the least bad successor weight `p+1`, nonvanishing of the atomic-defect map
already forces one chosen Hodge basis sheet to have nonzero defect.  Linear
separation supplies its genuine `BasisAtomicSeparator`.

By `GSTClassicalHodgeSeparatorFiniteGSTPoincare`, the separator read of that
basis sheet is *literally* a nonzero finite GST Poincare top pairing.

Now take only one genuine graded return `p+1 -> p` which sends that basis sheet
into the predecessor Hodge fiber.  Since `p` is below the first failure, the
returned Hodge class is algebraic.  The genuine principal-cut pair preserves
the atomic span, so its return to weight `p+1` is algebraic as well.  Hence the
separator reads the geometric round trip as zero.

Therefore it is enough for the new coupled cosmology to prove ONE observable
identity:

    separator( L (R basis_i) )
      = finiteGSTPoincare(basis_i, separatorProbe).

The left side is forced to zero at first failure; the right side is already
proved nonzero by the internal GST Poincare cosmology.  No scalar, no full
operator equality, no matrix unit, no global adjointness and no Hodge inverse
is requested.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeFirstFailurePoincareReadCollision

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeAtomicDefectDuality
open GSTClassicalHodgeAtomicAnnihilator
open GSTClassicalHodgeSingleSheetCrown
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeCrossWeightNativePropagation
open GSTClassicalHodgeCrossWeightAtomicDefectDescent
open GSTClassicalHodgeFirstPrimitiveProjectiveFailure
open GSTClassicalHodgeLimitlessSeparatorGhost
open GSTClassicalHodgeFiniteSupportChart
open GSTClassicalHodgeSeparatorFiniteGSTPoincare

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- A nonzero atomic defect on one chosen Hodge basis sheet canonically yields
a microscopic atomic separator for that same sheet. -/
noncomputable def basisSeparatorOfDefectNeZero
    (i : ClassicalHodgeBasisIndex V H p)
    (hi : atomicDefectLinearMap V H p
      (classicalHodgeBasis V H p i) ≠ 0) :
    BasisAtomicSeparator V H p i := by
  have hnotmem :
      (classicalHodgeBasis V H p i).1 ∉
        pointCycleClassSpan p (H.cycleClass p) := by
    intro hmem
    apply hi
    rw [atomicDefectLinearMap_apply]
    exact (Submodule.Quotient.mk_eq_zero
      (pointCycleClassSpan p (H.cycleClass p))).2 hmem
  obtain ⟨ell, hellSpan, hellBasis⟩ :=
    exists_linearFunctional_separating_submodule
      (pointCycleClassSpan p (H.cycleClass p))
      (classicalHodgeBasis V H p i).1 hnotmem
  refine {
    detector := ell
    annihilates_atoms := ?_
    detects_basis := hellBasis
  }
  intro x
  apply hellSpan
  exact Submodule.subset_span ⟨x, rfl⟩

/-- Any nonzero weight-p atomic defect map has at least one genuinely defective
basis sheet. -/
theorem exists_basisDefect_ne_zero
    (hbad : atomicDefectLinearMap V H p ≠ 0) :
    ∃ i : ClassicalHodgeBasisIndex V H p,
      atomicDefectLinearMap V H p
        (classicalHodgeBasis V H p i) ≠ 0 := by
  by_contra hnone
  push_neg at hnone
  apply hbad
  exact (atomicDefect_zero_iff_basis_zero V H p).2 hnone

/-- The one observable compatibility requested from a genuine return: its
principal-cut roundtrip has the same separator read as the already-canonical
finite GST Poincare observable of the obstructed basis sheet. -/
structure FirstFailurePoincareReadReturn
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (i : ClassicalHodgeBasisIndex V H (p + 1))
    (S : BasisAtomicSeparator V H (p + 1) i) where
  returnPair : GradedCycleClassOperatorPair V H (p + 1) p
  return_hodge :
    returnPair.cohomologyOperator
        (classicalHodgeBasis V H (p + 1) i).1 ∈
      rationalHodgeSubspace (H.hodgeBigrading p)
  poincare_read_reciprocity :
    S.detector
        ((G.principalCutPair p).cohomologyOperator
          (returnPair.cohomologyOperator
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

namespace FirstFailurePoincareReadReturn

/-- The returned predecessor Hodge state. -/
noncomputable def returnedHodgeClass
    {G : GeometricCycleClassSpine V H}
    {i : ClassicalHodgeBasisIndex V H (p + 1)}
    {S : BasisAtomicSeparator V H (p + 1) i}
    (R : FirstFailurePoincareReadReturn G p i S) :
    ClassicalHodgeFiber V H p :=
  ⟨R.returnPair.cohomologyOperator
      (classicalHodgeBasis V H (p + 1) i).1,
    R.return_hodge⟩

/-- If the predecessor Hodge defect is zero, the returned state lies in the
complete predecessor atomic cycle-class span. -/
theorem returnedHodgeClass_atomic
    {G : GeometricCycleClassSpine V H}
    {i : ClassicalHodgeBasisIndex V H (p + 1)}
    {S : BasisAtomicSeparator V H (p + 1) i}
    (R : FirstFailurePoincareReadReturn G p i S)
    (hsource : atomicDefectLinearMap V H p = 0) :
    R.returnedHodgeClass.1 ∈ pointCycleClassSpan p (H.cycleClass p) := by
  have hz : atomicDefectLinearMap V H p R.returnedHodgeClass = 0 := by
    rw [hsource]
    rfl
  rw [atomicDefectLinearMap_apply] at hz
  exact (Submodule.Quotient.mk_eq_zero
    (pointCycleClassSpan p (H.cycleClass p))).1 hz

/-- Genuine principal-cut naturality carries that algebraic predecessor state
back into the successor atomic span. -/
theorem roundtrip_atomic
    {G : GeometricCycleClassSpine V H}
    {i : ClassicalHodgeBasisIndex V H (p + 1)}
    {S : BasisAtomicSeparator V H (p + 1) i}
    (R : FirstFailurePoincareReadReturn G p i S)
    (hsource : atomicDefectLinearMap V H p = 0) :
    (G.principalCutPair p).cohomologyOperator R.returnedHodgeClass.1 ∈
      pointCycleClassSpan (p + 1) (H.cycleClass (p + 1)) := by
  exact (G.principalCutPair p).atomicSpanStable
    R.returnedHodgeClass.1 (R.returnedHodgeClass_atomic hsource)

/-- Consequently the actual atomic separator reads the geometric round trip as
zero. -/
theorem roundtrip_separator_read_eq_zero
    {G : GeometricCycleClassSpine V H}
    {i : ClassicalHodgeBasisIndex V H (p + 1)}
    {S : BasisAtomicSeparator V H (p + 1) i}
    (R : FirstFailurePoincareReadReturn G p i S)
    (hsource : atomicDefectLinearMap V H p = 0) :
    S.detector
      ((G.principalCutPair p).cohomologyOperator
        (R.returnPair.cohomologyOperator
          (classicalHodgeBasis V H (p + 1) i).1)) = 0 := by
  have hker :
      pointCycleClassSpan (p + 1) (H.cycleClass (p + 1)) ≤
        LinearMap.ker S.detector :=
    (annihilatesPointCycles_iff_atomicSpan_le_ker
      (p + 1) (H.cycleClass (p + 1)) S.detector).mp S.annihilates_atoms
  exact hker (R.roundtrip_atomic hsource)

/-- **ONE-POINCARE-READ FIRST-FAILURE COLLISION.**
The predecessor-goodness law forces the geometric read to zero, while the exact
separator/GST-Poincare identity makes the same read nonzero. -/
theorem impossible_of_predecessor_defect_zero
    {G : GeometricCycleClassSpine V H}
    {i : ClassicalHodgeBasisIndex V H (p + 1)}
    {S : BasisAtomicSeparator V H (p + 1) i}
    (R : FirstFailurePoincareReadReturn G p i S)
    (hsource : atomicDefectLinearMap V H p = 0) : False := by
  have hzero := R.roundtrip_separator_read_eq_zero hsource
  have hrec := R.poincare_read_reciprocity
  rw [hzero] at hrec
  have hnonzero := basisSeparator_finiteGSTPoincare_ne_zero S
  exact hnonzero hrec.symm

/-- At the globally least bad successor weight the one-read return packet is
therefore impossible. -/
theorem firstFailure_forbids_poincareReadReturn
    {G : GeometricCycleClassSpine V H}
    (F : FirstAtomicDefectWeight V H)
    (hp : F.weight = p + 1)
    {i : ClassicalHodgeBasisIndex V H (p + 1)}
    {S : BasisAtomicSeparator V H (p + 1) i}
    (R : FirstFailurePoincareReadReturn G p i S) : False :=
  R.impossible_of_predecessor_defect_zero
    (firstAtomicDefect_predecessor_zero F hp)

end FirstFailurePoincareReadReturn

/-- **FINITE-GST POINCARE RETURN HODGE CROWN.**
If every possible microscopic successor separator admits one genuine return
whose single roundtrip read agrees with its finite GST Poincare observable,
then a least Hodge failure cannot exist. -/
theorem bigradedBettiHodge_of_poincareReadReturnFamily
    (G : GeometricCycleClassSpine V H)
    (hzero : atomicDefectLinearMap V H 0 = 0)
    (R : ∀ p : Nat,
      ∀ i : ClassicalHodgeBasisIndex V H (p + 1),
      ∀ S : BasisAtomicSeparator V H (p + 1) i,
        Nonempty (FirstFailurePoincareReadReturn G p i S)) :
    BigradedBettiHodgeStatement V H := by
  by_contra hnot
  let F := firstAtomicDefectWeightOfFailure
    (V := V) (H := H) hzero hnot
  obtain ⟨p, hp⟩ := firstAtomicDefectWeight_eq_succ F
  have hbad : atomicDefectLinearMap V H (p + 1) ≠ 0 := by
    simpa [hp] using F.defect_ne_zero
  obtain ⟨i, hi⟩ := exists_basisDefect_ne_zero (V := V) (H := H) hbad
  let S : BasisAtomicSeparator V H (p + 1) i :=
    basisSeparatorOfDefectNeZero i hi
  rcases R p i S with ⟨RR⟩
  exact RR.firstFailure_forbids_poincareReadReturn F hp

#check basisSeparatorOfDefectNeZero
#check exists_basisDefect_ne_zero
#check FirstFailurePoincareReadReturn
#check FirstFailurePoincareReadReturn.returnedHodgeClass_atomic
#check FirstFailurePoincareReadReturn.roundtrip_atomic
#check FirstFailurePoincareReadReturn.roundtrip_separator_read_eq_zero
#check FirstFailurePoincareReadReturn.impossible_of_predecessor_defect_zero
#check FirstFailurePoincareReadReturn.firstFailure_forbids_poincareReadReturn
#check bigradedBettiHodge_of_poincareReadReturnFamily

#print axioms basisSeparatorOfDefectNeZero
#print axioms FirstFailurePoincareReadReturn.roundtrip_separator_read_eq_zero
#print axioms FirstFailurePoincareReadReturn.impossible_of_predecessor_defect_zero
#print axioms bigradedBettiHodge_of_poincareReadReturnFamily

end GSTClassicalHodgeFirstFailurePoincareReadCollision
