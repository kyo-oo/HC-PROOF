import GSTClassicalHodgeNormalizedFiberedSpectralAtom
import GSTClassicalHodgeSynchronizedDefectOrbit
import GSTClassicalHodgeFiberedNativeRecoordination

/-!
# GST CLASSICAL HODGE — NORMALIZED FIBERED DEFECT BARRIER

The enriched fibered universe can isolate one classical multiplicity sheet and
one genuine native point simultaneously.  That fact is important, but by
itself it is not yet a cycle-class realization theorem.

This file makes the boundary exact.  From a normalized fibered spectral atom we
form the corresponding synchronized native/classical state:

* native face = the atom's genuine native cycle;
* classical face = the classical Hodge basis vector named by the isolated
  sheet.

The synchronized defect is therefore zero **iff** that concrete native point
cycle already has cycle class equal to the selected Hodge basis vector.
Consequently no argument may convert spectral isolation, recoordination, or
sheet bookkeeping into algebraicity merely by declaring the enriched atom to
be defect-free: that declaration is exactly the missing basis-cycle equality.

World recoordination does not evade this barrier because it preserves the
intrinsic live basis index exactly.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeNormalizedFiberedDefectBarrier

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeFiberedNativePullback
open GSTClassicalHodgeFiberedNativeRecoordination
open GSTClassicalHodgeNormalizedFiberedSpectralAtom
open GSTClassicalHodgeSynchronizedDefectOrbit
open GSTNativeCodimensionCyclePresentation
open GSTWorldRecoordinationGroupoid
open GSTClassicalHodgeFiniteSupportArsenalConjugation

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- The synchronized state canonically associated to a normalized fibered
spectral atom.  Its native face is taken from the fibered atom; its classical
face is the actual Hodge basis vector selected by that atom's live sheet. -/
noncomputable def normalizedSpectralSynchronizedState
    (alpha : ClassicalHodgeFiber V H p)
    (S : GSTWorldShape (liveRank alpha))
    (y : ShapeState S)
    (x : CodimensionPoint V.X p) :
    SynchronizedState (V := V) (H := H) (p := p) where
  native :=
    toNativeCycle V H p
      (normalizedSpectralAtom alpha S y x)
  classical :=
    (classicalHodgeBasis V H p
      (shapedLiveBasisIndex alpha S y)).1

/-- The synchronized state's native face is exactly the selected genuine point
cycle. -/
theorem normalizedSpectralSynchronizedState_native
    (alpha : ClassicalHodgeFiber V H p)
    (S : GSTWorldShape (liveRank alpha))
    (y : ShapeState S)
    (x : CodimensionPoint V.X p) :
    (normalizedSpectralSynchronizedState alpha S y x).native =
      codimensionPointCycle V.X p x := by
  exact normalized_nativeFace_exact alpha S y x

/-- The synchronized state's classical face is exactly the basis vector named
by the isolated live sheet. -/
theorem normalizedSpectralSynchronizedState_classical
    (alpha : ClassicalHodgeFiber V H p)
    (S : GSTWorldShape (liveRank alpha))
    (y : ShapeState S)
    (x : CodimensionPoint V.X p) :
    (normalizedSpectralSynchronizedState alpha S y x).classical =
      (classicalHodgeBasis V H p
        (shapedLiveBasisIndex alpha S y)).1 := rfl

/-- Exact defect formula for a normalized fibered spectral atom. -/
theorem normalizedSpectralSynchronizedState_defect
    (alpha : ClassicalHodgeFiber V H p)
    (S : GSTWorldShape (liveRank alpha))
    (y : ShapeState S)
    (x : CodimensionPoint V.X p) :
    synchronizedDefect
        (normalizedSpectralSynchronizedState alpha S y x) =
      H.cycleClass p (codimensionPointCycle V.X p x) -
        (classicalHodgeBasis V H p
          (shapedLiveBasisIndex alpha S y)).1 := by
  unfold synchronizedDefect
  rw [normalizedSpectralSynchronizedState_native]
  rfl

/--
**FIBERED DEFECT BARRIER.**  Zero synchronized defect for the normalized
spectral atom is exactly the statement that the concrete point cycle represents
the isolated Hodge basis vector.
-/
theorem normalizedSpectral_defect_zero_iff_point_represents_basis
    (alpha : ClassicalHodgeFiber V H p)
    (S : GSTWorldShape (liveRank alpha))
    (y : ShapeState S)
    (x : CodimensionPoint V.X p) :
    synchronizedDefect
        (normalizedSpectralSynchronizedState alpha S y x) = 0 ↔
      H.cycleClass p (codimensionPointCycle V.X p x) =
        (classicalHodgeBasis V H p
          (shapedLiveBasisIndex alpha S y)).1 := by
  rw [normalizedSpectralSynchronizedState_defect]
  exact sub_eq_zero

/-- A zero-defect normalized spectral atom therefore gives an explicit native
cycle representative for its isolated basis direction; it is not merely a
coordinate statement. -/
theorem basis_mem_cycleClass_range_of_normalizedSpectral_defect_zero
    (alpha : ClassicalHodgeFiber V H p)
    (S : GSTWorldShape (liveRank alpha))
    (y : ShapeState S)
    (x : CodimensionPoint V.X p)
    (hzero :
      synchronizedDefect
          (normalizedSpectralSynchronizedState alpha S y x) = 0) :
    (classicalHodgeBasis V H p
        (shapedLiveBasisIndex alpha S y)).1 ∈
      LinearMap.range (H.cycleClass p) := by
  refine ⟨codimensionPointCycle V.X p x, ?_⟩
  exact
    (normalizedSpectral_defect_zero_iff_point_represents_basis
      alpha S y x).1 hzero

/-- Recoordination cannot change the intrinsic basis direction selected by a
live slot; it only changes the finite observation chart. -/
theorem recoordination_preserves_defect_target_basis
    (alpha : ClassicalHodgeFiber V H p)
    (S T : GSTWorldShape (liveRank alpha))
    (y : ShapeState S) :
    classicalHodgeBasis V H p
        (shapedLiveBasisIndex alpha T (worldRecoordinate S T y)) =
      classicalHodgeBasis V H p
        (shapedLiveBasisIndex alpha S y) := by
  rw [shapedLiveBasisIndex_recoordinate]

/-- Chart recoordination therefore leaves the exact basis-cycle equality
required for zero defect unchanged. -/
theorem recoordination_defect_zero_iff
    (alpha : ClassicalHodgeFiber V H p)
    (S T : GSTWorldShape (liveRank alpha))
    (y : ShapeState S)
    (x : CodimensionPoint V.X p) :
    synchronizedDefect
        (normalizedSpectralSynchronizedState
          alpha T (worldRecoordinate S T y) x) = 0 ↔
      synchronizedDefect
        (normalizedSpectralSynchronizedState alpha S y x) = 0 := by
  rw [normalizedSpectral_defect_zero_iff_point_represents_basis]
  rw [normalizedSpectral_defect_zero_iff_point_represents_basis]
  rw [shapedLiveBasisIndex_recoordinate]

#check normalizedSpectralSynchronizedState
#check normalizedSpectralSynchronizedState_native
#check normalizedSpectralSynchronizedState_classical
#check normalizedSpectralSynchronizedState_defect
#check normalizedSpectral_defect_zero_iff_point_represents_basis
#check basis_mem_cycleClass_range_of_normalizedSpectral_defect_zero
#check recoordination_preserves_defect_target_basis
#check recoordination_defect_zero_iff

#print axioms normalizedSpectral_defect_zero_iff_point_represents_basis
#print axioms basis_mem_cycleClass_range_of_normalizedSpectral_defect_zero
#print axioms recoordination_defect_zero_iff

end GSTClassicalHodgeNormalizedFiberedDefectBarrier
