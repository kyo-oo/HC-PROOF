import GSTClassicalHodgePersistentDefectCorrespondenceOrbit
import GSTClassicalHodgeAtomicDefectDuality

/-!
# GST CLASSICAL HODGE — CORRESPONDENCE ORBIT EXACTNESS

The realized-correspondence orbit criterion is often described as a geometric
route to a Hodge basis sheet.  This file records its exact logical strength.

Every finite rational word of realized closed correspondences preserves the
actual atomic cycle-class span.  Its source point class is already atomic.
Therefore a nonzero-scaled orbit hit on a Hodge basis sheet immediately puts
that basis sheet in the atomic span and kills its atomic defect.

Thus orbit reachability is NOT an earlier substitute for algebraicity.  It is a
strictly geometric strengthening of algebraicity.  The existing formalism does
not prove the converse: an arbitrary algebraic Hodge class is a finite rational
combination of point-cycle classes, but the correspondence algebra has not
constructed a single source point and one realized word producing that
combination.

This distinction prevents circular construction attempts.  Any proof of orbit
reachability for the selected failure sheet has already solved the relevant
Hodge basis direction, while potentially asking for more geometric
transitivity than Hodge itself.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeCorrespondenceOrbitExactness

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeAtomicDefectDuality
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra
open GSTClassicalHodgePersistentDefectCorrespondenceOrbit

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Every realized-correspondence orbit point starts and remains in the actual
atomic cycle-class span. -/
theorem realizedWord_point_mem_atomicSpan
    (W : RealizedCorrespondenceWord V H p)
    (x : CodimensionPoint V.X p) :
    (realizedWordPair W).cohomologyOperator
        (H.cycleClass p (codimensionPointCycle V.X p x)) ∈
      pointCycleClassSpan p (H.cycleClass p) := by
  have hx :
      H.cycleClass p (codimensionPointCycle V.X p x) ∈
        pointCycleClassSpan p (H.cycleClass p) :=
    Submodule.subset_span ⟨x, rfl⟩
  exact realizedWord_atomic_stable W _ hx

/-- **ORBIT HIT -> ALGEBRAIC BASIS SHEET.**
A nonzero-scaled realized correspondence hit already proves algebraicity of the
target Hodge basis direction. -/
theorem basis_mem_atomicSpan_of_orbitHit
    (j : ClassicalHodgeBasisIndex V H p)
    (hHit : RealizedCorrespondenceOrbitHitsSheet (V := V) (H := H) j) :
    (classicalHodgeBasis V H p j).1 ∈
      pointCycleClassSpan p (H.cycleClass p) := by
  rcases hHit with ⟨x, W, c, hc, hEq⟩
  have himage := realizedWord_point_mem_atomicSpan (V := V) (H := H) W x
  rw [hEq] at himage
  have hunscale :=
    (pointCycleClassSpan p (H.cycleClass p)).smul_mem c⁻¹ himage
  simpa [smul_smul, hc] using hunscale

/-- Defect-zero form of the same statement. -/
theorem basis_defect_zero_of_orbitHit
    (j : ClassicalHodgeBasisIndex V H p)
    (hHit : RealizedCorrespondenceOrbitHitsSheet (V := V) (H := H) j) :
    atomicDefectLinearMap V H p (classicalHodgeBasis V H p j) = 0 := by
  rw [atomicDefectLinearMap_apply]
  exact (Submodule.Quotient.mk_eq_zero
    (pointCycleClassSpan p (H.cycleClass p))).2
      (basis_mem_atomicSpan_of_orbitHit j hHit)

/-- Hence a basis sheet with nonzero atomic defect can never be obtained by
such an orbit hit. -/
theorem no_orbitHit_of_basis_defect_ne_zero
    (j : ClassicalHodgeBasisIndex V H p)
    (hdef : atomicDefectLinearMap V H p
      (classicalHodgeBasis V H p j) ≠ 0) :
    ¬ RealizedCorrespondenceOrbitHitsSheet (V := V) (H := H) j := by
  intro hHit
  exact hdef (basis_defect_zero_of_orbitHit j hHit)

/-- If every basis sheet is hit, then every basis defect vanishes directly. -/
theorem atomicDefect_zero_of_all_basis_orbitHits
    (hHit : ∀ j : ClassicalHodgeBasisIndex V H p,
      RealizedCorrespondenceOrbitHitsSheet (V := V) (H := H) j) :
    atomicDefectLinearMap V H p = 0 := by
  rw [atomicDefect_zero_iff_basis_zero]
  intro j
  exact basis_defect_zero_of_orbitHit j (hHit j)

#check realizedWord_point_mem_atomicSpan
#check basis_mem_atomicSpan_of_orbitHit
#check basis_defect_zero_of_orbitHit
#check no_orbitHit_of_basis_defect_ne_zero
#check atomicDefect_zero_of_all_basis_orbitHits

#print axioms basis_mem_atomicSpan_of_orbitHit
#print axioms basis_defect_zero_of_orbitHit
#print axioms no_orbitHit_of_basis_defect_ne_zero
#print axioms atomicDefect_zero_of_all_basis_orbitHits

end GSTClassicalHodgeCorrespondenceOrbitExactness
