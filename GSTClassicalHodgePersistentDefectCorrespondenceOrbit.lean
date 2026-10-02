import GSTClassicalHodgePersistentVerticalDefect
import GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra

/-!
# GST CLASSICAL HODGE — PERSISTENT DEFECT / GENUINE CORRESPONDENCE ORBIT

This file fuses two previously separate mathematical lineages:

* a hypothetical Hodge failure produces one persistent vertical defect sheet,
  detected by a linear functional annihilating every genuine point-cycle
  class;
* finite rational words of genuinely realized closed correspondences preserve
  the complete atomic point-cycle span by an exact native/cohomology commuting
  square.

Therefore the failure detector annihilates the entire realized-correspondence
orbit of every native point.  Since it reads its selected Hodge basis sheet
nontrivially, that sheet cannot be reached from any point class by any finite
rational word of genuine realized closed correspondences, even up to nonzero
rational scaling.

This is a strictly geometric contradiction target.  No matrix-unit
reachability, Hodge surjectivity, visibility certificate, or arbitrary native
operator is assumed.  To close the Hodge target through this route it is enough
to prove genuine realized-correspondence orbit reachability of each Hodge basis
sheet from one actual codimension-p point.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgePersistentDefectCorrespondenceOrbit

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeAtomicAnnihilator
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgePersistentVerticalDefect
open GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- One Hodge basis sheet is hit from one genuine point class by a finite
rational word of genuinely realized closed correspondences, up to a nonzero
rational scalar. -/
def RealizedCorrespondenceOrbitHitsSheet
    (j : ClassicalHodgeBasisIndex V H p) : Prop :=
  ∃ x : CodimensionPoint V.X p,
  ∃ W : RealizedCorrespondenceWord V H p,
  ∃ c : ℚ,
    c ≠ 0 ∧
    (realizedWordPair W).cohomologyOperator
        (H.cycleClass p (codimensionPointCycle V.X p x)) =
      c • (classicalHodgeBasis V H p j).1

/-- A persistent failure detector kills every point after every finite rational
word of genuinely realized closed correspondences. -/
theorem PersistentVerticalDefect.detector_kills_realizedWord_point
    (D : PersistentVerticalDefect V H p)
    (W : RealizedCorrespondenceWord V H p)
    (x : CodimensionPoint V.X p) :
    D.detector
      ((realizedWordPair W).cohomologyOperator
        (H.cycleClass p (codimensionPointCycle V.X p x))) = 0 := by
  have hxAtomic :
      H.cycleClass p (codimensionPointCycle V.X p x) ∈
        pointCycleClassSpan p (H.cycleClass p) :=
    Submodule.subset_span ⟨x, rfl⟩
  have hImage :
      (realizedWordPair W).cohomologyOperator
          (H.cycleClass p (codimensionPointCycle V.X p x)) ∈
        pointCycleClassSpan p (H.cycleClass p) :=
    realizedWord_atomic_stable W _ hxAtomic
  have hker :
      pointCycleClassSpan p (H.cycleClass p) ≤ LinearMap.ker D.detector :=
    (annihilatesPointCycles_iff_atomicSpan_le_ker
      p (H.cycleClass p) D.detector).mp D.annihilates_atoms
  exact hker hImage

/-- **PERSISTENT DEFECT ORBIT NO-GO.**
The sheet selected by a persistent Hodge defect cannot lie in any nonzero
scaled realized-correspondence orbit of a genuine point class. -/
theorem PersistentVerticalDefect.no_realizedCorrespondenceOrbitHit
    (D : PersistentVerticalDefect V H p) :
    ¬ RealizedCorrespondenceOrbitHitsSheet (V := V) (H := H) D.sheet := by
  rintro ⟨x, W, c, hc, hEq⟩
  have hkill := D.detector_kills_realizedWord_point W x
  rw [hEq, LinearMap.map_smul] at hkill
  have hmul :
      c * D.detector (classicalHodgeBasis V H p D.sheet).1 = 0 := by
    simpa [smul_eq_mul] using hkill
  have hread :
      D.detector (classicalHodgeBasis V H p D.sheet).1 = 0 :=
    (mul_eq_zero.mp hmul).resolve_left hc
  exact D.sheet_read_ne_zero hread

/-- Every hypothetical Hodge failure therefore exhibits a concrete Hodge basis
sheet outside every genuine realized-correspondence orbit of every native
point. -/
theorem hodge_failure_yields_realizedCorrespondenceOrbitNoGo
    (hnot : ¬ BigradedBettiHodgeStatement V H) :
    ∃ q : Nat,
    ∃ D : PersistentVerticalDefect V H q,
      ¬ RealizedCorrespondenceOrbitHitsSheet (V := V) (H := H) D.sheet := by
  rcases not_hodge_yields_persistentVerticalDefect
      (V := V) (H := H) hnot with ⟨q, ⟨D⟩⟩
  exact ⟨q, D, D.no_realizedCorrespondenceOrbitHit⟩

/-- **GENUINE CORRESPONDENCE-ORBIT CROWN.**
If every genuine Hodge basis sheet is reachable from some actual point class by
a finite rational word of realized closed correspondences up to nonzero scale,
then the complete Stage-2G Hodge statement follows. -/
theorem bigradedBettiHodge_of_realizedCorrespondenceOrbitHits
    (hHit : ∀ q : Nat,
      ∀ j : ClassicalHodgeBasisIndex V H q,
        RealizedCorrespondenceOrbitHitsSheet (V := V) (H := H) j) :
    BigradedBettiHodgeStatement V H := by
  by_contra hnot
  rcases hodge_failure_yields_realizedCorrespondenceOrbitNoGo
      (V := V) (H := H) hnot with ⟨q, D, hNo⟩
  exact hNo (hHit q D.sheet)

/-- Exact contraposition: Hodge failure is witnessed by at least one basis
sheet for which genuine realized-correspondence orbit reachability fails. -/
theorem hodge_failure_implies_exists_unreachable_sheet :
    (¬ BigradedBettiHodgeStatement V H) →
      ∃ q : Nat,
      ∃ j : ClassicalHodgeBasisIndex V H q,
        ¬ RealizedCorrespondenceOrbitHitsSheet (V := V) (H := H) j := by
  intro hnot
  rcases hodge_failure_yields_realizedCorrespondenceOrbitNoGo
      (V := V) (H := H) hnot with ⟨q, D, hNo⟩
  exact ⟨q, D.sheet, hNo⟩

#check RealizedCorrespondenceOrbitHitsSheet
#check PersistentVerticalDefect.detector_kills_realizedWord_point
#check PersistentVerticalDefect.no_realizedCorrespondenceOrbitHit
#check hodge_failure_yields_realizedCorrespondenceOrbitNoGo
#check bigradedBettiHodge_of_realizedCorrespondenceOrbitHits
#check hodge_failure_implies_exists_unreachable_sheet

#print axioms PersistentVerticalDefect.detector_kills_realizedWord_point
#print axioms PersistentVerticalDefect.no_realizedCorrespondenceOrbitHit
#print axioms hodge_failure_yields_realizedCorrespondenceOrbitNoGo
#print axioms bigradedBettiHodge_of_realizedCorrespondenceOrbitHits

end GSTClassicalHodgePersistentDefectCorrespondenceOrbit
