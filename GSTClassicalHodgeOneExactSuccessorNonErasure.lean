import GSTClassicalHodgeRelativeSuccessorExactStratum

/-!
# GST CLASSICAL HODGE — ONE EXACT SUCCESSOR NON-ERASURE

The earlier exact-stratum crown asked that every relative height-one successor
of a codimension-p source land in ambient codimension p+1.  Native non-erasure
needs much less.

Every accepted successor atom enters the finite native presentation with
coefficient +1, while rejected atoms contribute zero.  Consequently one
single relative successor whose ambient coheight is exactly p+1 already forces
strictly positive successor mass and hence a nonzero native principal-cut
image of the source point atom.

This is the sharp form needed by the separator-successor construction: the
canonical separator prime only has to certify one exact ambient successor.
No global exact-stratum law is required.
-/

set_option maxHeartbeats 40000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgePointClosureRelativeCut
open GSTClassicalHodgePrincipalCutSuccessorOperator
open GSTClassicalHodgeNativeCycleCosmicShadow
open GSTClassicalHodgeRelativeSuccessorExactStratum

namespace GSTClassicalHodgeOneExactSuccessorNonErasure

/-- Every successor atom has nonnegative presentation mass: it is either the
unit atom of an exact ambient successor or the zero presentation. -/
theorem successorAtomPresentation_mass_nonnegative
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (y : {y : pointClosureScheme V x.1 // Order.coheight y = 1}) :
    0 <= presentationMass (successorAtomPresentation V p x y) := by
  unfold successorAtomPresentation
  split_ifs <;> simp

/-- One exact selected successor contributes mass exactly one. -/
theorem successorAtomPresentation_mass_eq_one_of_exact
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (y : {y : pointClosureScheme V x.1 // Order.coheight y = 1})
    (hExact : Order.coheight (ambientSuccessorPoint V x.1 y) = p + 1) :
    presentationMass (successorAtomPresentation V p x y) = 1 := by
  rw [successorAtomPresentation_eq_single V p x y hExact]
  simp

/-- **ONE-EXACT-SUCCESSOR MASS POSITIVITY.**
If even one member of the relative successor finset lands in the exact next
ambient stratum, the total canonical successor mass is strictly positive.
All other terms are nonnegative, so no cancellation argument is needed. -/
theorem successorMass_pos_of_one_exact
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (y : {y : pointClosureScheme V x.1 // Order.coheight y = 1})
    (hy : y ∈ relativeCodimensionOneFinset V x.1)
    (hExact : Order.coheight (ambientSuccessorPoint V x.1 y) = p + 1) :
    0 < successorMass V p x := by
  classical
  unfold successorMass successorPresentation
  rw [map_sum]
  have hnonneg :
      ∀ z ∈ relativeCodimensionOneFinset V x.1,
        0 <= presentationMass (successorAtomPresentation V p x z) := by
    intro z hz
    exact successorAtomPresentation_mass_nonnegative V p x z
  have hyone :
      presentationMass (successorAtomPresentation V p x y) = 1 :=
    successorAtomPresentation_mass_eq_one_of_exact V p x y hExact
  have hle :
      presentationMass (successorAtomPresentation V p x y) <=
        ∑ z ∈ relativeCodimensionOneFinset V x.1,
          presentationMass (successorAtomPresentation V p x z) := by
    exact Finset.single_le_sum
      (fun z hz => hnonneg z hz) hy
  rw [hyone] at hle
  exact lt_of_lt_of_le (by norm_num : (0 : ℚ) < 1) hle

/-- One exact selected successor already makes the native principal-cut image
of a point atom nonzero.  This strictly weakens the previous global
`RelativeSuccessorAmbientExact` hypothesis. -/
theorem successorNativeOperator_point_ne_zero_of_one_exact
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (y : {y : pointClosureScheme V x.1 // Order.coheight y = 1})
    (hy : y ∈ relativeCodimensionOneFinset V x.1)
    (hExact : Order.coheight (ambientSuccessorPoint V x.1 y) = p + 1) :
    successorNativeOperator V p (codimensionPointCycle V.X p x) ≠ 0 := by
  intro hzero
  have hmass := congrArg (nativeCycleMass V (p + 1)) hzero
  rw [nativeCycleMass_successor_point] at hmass
  simp only [LinearMap.map_zero] at hmass
  have hpos := successorMass_pos_of_one_exact V p x y hy hExact
  exact (ne_of_gt hpos) hmass

/-- Sharp non-erasure crown: the cutting engine needs only one exact member of
the finite relative successor set, not exact grading of the entire set. -/
theorem one_exact_successor_non_erasure_crown
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (y : {y : pointClosureScheme V x.1 // Order.coheight y = 1})
    (hy : y ∈ relativeCodimensionOneFinset V x.1)
    (hExact : Order.coheight (ambientSuccessorPoint V x.1 y) = p + 1) :
    0 < successorMass V p x
      ∧ successorNativeOperator V p
          (codimensionPointCycle V.X p x) ≠ 0 := by
  exact ⟨successorMass_pos_of_one_exact V p x y hy hExact,
    successorNativeOperator_point_ne_zero_of_one_exact V p x y hy hExact⟩

#check successorAtomPresentation_mass_nonnegative
#check successorAtomPresentation_mass_eq_one_of_exact
#check successorMass_pos_of_one_exact
#check successorNativeOperator_point_ne_zero_of_one_exact
#check one_exact_successor_non_erasure_crown

#print axioms successorMass_pos_of_one_exact
#print axioms successorNativeOperator_point_ne_zero_of_one_exact
#print axioms one_exact_successor_non_erasure_crown

end GSTClassicalHodgeOneExactSuccessorNonErasure
