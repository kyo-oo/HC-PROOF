import GSTClassicalHodgeNativeChargeOrthogonalization

/-!
# Rank-two GST geometric frontier: atomic independent point witness

Previously the rank-two native geometry theorem required an abstract
codimension-p cycle Z whose Betti image escaped the projective-spine line.
Here the existing compact finite point presentation proves something sharper:

* A native cycle escapes that line IF AND ONLY IF one *genuine*
  codimension-p point cycle escapes it.
* In a two-dimensional rational Hodge fiber with a nonzero native spine,
  weightwise Hodge realization holds IF AND ONLY IF such a genuine point
  exists.

This is an exact, checkable geometric obstruction, NOT a proof that the
point exists on every variety. It identifies the remaining construction
without hiding it inside a supplied Hodge preimage or a determinant premise.
-/

set_option maxHeartbeats 11000000
set_option maxRecDepth 800000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeLimitlessSpinePropagation
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeNativeChargeOrthogonalization

namespace GSTClassicalHodgeAtomicIndependentPointFrontier

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- If EVERY genuine codimension-p point class is trapped on the native GST
spine line, then ALL actual finite native cycles are trapped there too.
This derives from the already-verified atomic point-cycle span theorem. -/
theorem all_native_classes_collinear_of_point_collinearity
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (hpoints : ∀ x : CodimensionPoint V.X p,
      ∃ c : ℚ,
        H.cycleClass p (codimensionPointCycle V.X p x) =
          c • (spineHodgeSeed G p).1)
    (Z : codimensionCycles V.X p) :
    ∃ c : ℚ,
      H.cycleClass p Z = c • (spineHodgeSeed G p).1 := by
  let S : Submodule ℚ
      (RationalSingularCohomology H.analytification (2 * p)) :=
    Submodule.span ℚ {(spineHodgeSeed G p).1}
  have hle : pointCycleClassSpan p (H.cycleClass p) ≤ S := by
    apply Submodule.span_le.mpr
    rintro y ⟨x, rfl⟩
    obtain ⟨c, hc⟩ := hpoints x
    rw [hc]
    exact S.smul_mem _ (Submodule.subset_span (Set.mem_singleton _))
  have hmem : H.cycleClass p Z ∈ S := by
    apply hle
    rw [← smoothProjective_cycleClass_range_eq_atomic_span V H p]
    exact ⟨Z, rfl⟩
  exact Submodule.mem_span_singleton.mp hmem

/-- An independent native class exists precisely when a SINGLE genuine
codimension-p point cycle provides an independent Betti direction.
No correspondence or coordinate basis is needed for this equivalence. -/
theorem native_outside_spine_iff_atomic_point_outside
    (G : GeometricCycleClassSpine V H)
    (p : Nat) :
    (∃ Z : codimensionCycles V.X p,
      ∀ c : ℚ,
        H.cycleClass p Z ≠ c • (spineHodgeSeed G p).1) ↔
    (∃ x : CodimensionPoint V.X p,
      ∀ c : ℚ,
        H.cycleClass p (codimensionPointCycle V.X p x) ≠
          c • (spineHodgeSeed G p).1) := by
  constructor
  · rintro ⟨Z, hZ⟩
    by_contra h
    push_neg at h
    obtain ⟨c, hc⟩ :=
      all_native_classes_collinear_of_point_collinearity G p h Z
    exact hZ c hc
  · rintro ⟨x, hx⟩
    exact ⟨codimensionPointCycle V.X p x, hx⟩

/-- A genuine projective point outside the native spine generates the
second geometric direction, giving all rank-two rational Hodge classes
actual native-cycle representatives. NO global conserved charge required. -/
theorem rank_two_hodge_from_independent_projective_point
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (hspine : spineHodgeSeed G p ≠ 0)
    (x : CodimensionPoint V.X p)
    (hx : ∀ c : ℚ,
      H.cycleClass p (codimensionPointCycle V.X p x) ≠
        c • (spineHodgeSeed G p).1)
    [FiniteDimensional ℚ (ClassicalHodgeFiber V H p)]
    (hrank : Module.finrank ℚ (ClassicalHodgeFiber V H p) = 2)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p)) :
    ∃ Z : codimensionCycles V.X p, H.cycleClass p Z = alpha :=
  rank_two_hodge_without_global_charge G p hspine
    (codimensionPointCycle V.X p x) hx hrank alpha halpha

/-- Exact RANK-TWO FRONTIER. For a fixed weight, Hodge realization of every
rational (p,p) class is mathematically equivalent to the existence of a
genuine codimension-p scheme point whose class is independent of GST's
native projective spine. The reverse direction follows from the finite
point-support normal form, not from circularly assuming a basis lift. -/
theorem rank_two_weightwise_hodge_iff_independent_point
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (hspine : spineHodgeSeed G p ≠ 0)
    [FiniteDimensional ℚ (ClassicalHodgeFiber V H p)]
    (hrank : Module.finrank ℚ (ClassicalHodgeFiber V H p) = 2) :
    (∀ alpha : RationalSingularCohomology H.analytification (2 * p),
      alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p) →
      ∃ Z : codimensionCycles V.X p, H.cycleClass p Z = alpha) ↔
    (∃ x : CodimensionPoint V.X p,
      ∀ c : ℚ,
        H.cycleClass p (codimensionPointCycle V.X p x) ≠
          c • (spineHodgeSeed G p).1) := by
  constructor
  · intro hweight
    by_contra h
    push_neg at h
    have hall : ∀ w : ClassicalHodgeFiber V H p,
        ∃ c : ℚ, c • spineHodgeSeed G p = w := by
      intro w
      obtain ⟨Z, hZ⟩ := hweight w.1 w.2
      obtain ⟨c, hc⟩ :=
        all_native_classes_collinear_of_point_collinearity G p h Z
      refine ⟨c, ?_⟩
      apply Subtype.ext
      exact hc.symm.trans hZ
    have hle : Module.finrank ℚ (ClassicalHodgeFiber V H p) ≤ 1 :=
      finrank_le_one (spineHodgeSeed G p) hall
    omega
  · rintro ⟨x, hx⟩ alpha halpha
    exact rank_two_hodge_from_independent_projective_point
      G p hspine x hx hrank alpha halpha

#check all_native_classes_collinear_of_point_collinearity
#check native_outside_spine_iff_atomic_point_outside
#check rank_two_hodge_from_independent_projective_point
#check rank_two_weightwise_hodge_iff_independent_point

#print axioms native_outside_spine_iff_atomic_point_outside
#print axioms rank_two_weightwise_hodge_iff_independent_point

end GSTClassicalHodgeAtomicIndependentPointFrontier
