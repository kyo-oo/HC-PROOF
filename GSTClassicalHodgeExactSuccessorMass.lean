import GSTClassicalHodgeIntrinsicSuccessorNormalization
import GSTClassicalHodgeRelativeSuccessorLowerBound

/-!
# GST CLASSICAL HODGE — EXACT SUCCESSOR MASS

The geometry-built principal-cut successor presentation is a finite sum of
unit codimension-(p+1) atoms, with every relative height-one candidate whose
ambient coheight is not exactly p+1 discarded as zero.

Therefore its canonical native mass is not extra semantic data: it is exactly
the rational cardinality of the surviving exact-stratum candidates.

This file isolates that fact and eliminates another opaque nonvanishing
condition.  In particular:

  successorMass V p x != 0

is equivalent to the existence of at least one relative height-one successor
whose ambient image has coheight p+1.

Combined with intrinsic successor normalization, one such genuine geometric
successor is enough to manufacture the canonical next-weight limitless state.
-/

set_option maxHeartbeats 50000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeExactSuccessorMass

open GSTProjectiveOverC
open GSTClassicalHodgePointClosureRelativeCut
open GSTClassicalHodgePrincipalCutSuccessorOperator
open GSTClassicalHodgeNativeCycleCosmicShadow
open GSTClassicalHodgeIntrinsicSuccessorNormalization

/-- Relative height-one candidates surviving the exact ambient codimension
filter. -/
noncomputable def exactSuccessorFinset
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p) :
    Finset {y : pointClosureScheme V x.1 // Order.coheight y = 1} := by
  classical
  exact (relativeCodimensionOneFinset V x.1).filter fun y =>
    Order.coheight (ambientSuccessorPoint V x.1 y) = p + 1

@[simp]
theorem mem_exactSuccessorFinset
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (y : {y : pointClosureScheme V x.1 // Order.coheight y = 1}) :
    y ∈ exactSuccessorFinset V p x ↔
      y ∈ relativeCodimensionOneFinset V x.1 ∧
      Order.coheight (ambientSuccessorPoint V x.1 y) = p + 1 := by
  classical
  simp [exactSuccessorFinset]

/-- Each relative candidate contributes mass one exactly when it survives the
ambient codimension filter, and mass zero otherwise. -/
theorem presentationMass_successorAtom
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (y : {y : pointClosureScheme V x.1 // Order.coheight y = 1}) :
    presentationMass (successorAtomPresentation V p x y) =
      if Order.coheight (ambientSuccessorPoint V x.1 y) = p + 1
      then 1 else 0 := by
  classical
  by_cases hy : Order.coheight (ambientSuccessorPoint V x.1 y) = p + 1
  · rw [successorAtomPresentation_eq_single V p x y hy]
    simp [presentationMass_single, hy]
  · rw [successorAtomPresentation_eq_zero V p x y hy]
    simp [hy]

/-- **EXACT SUCCESSOR MASS FORMULA.**
The actual projective successor mass is the rational cardinality of the
relative height-one candidates that land in ambient codimension p+1. -/
theorem successorMass_eq_exactSuccessor_card
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p) :
    successorMass V p x = (exactSuccessorFinset V p x).card := by
  classical
  unfold successorMass successorPresentation
  rw [map_sum]
  simp_rw [presentationMass_successorAtom]
  rw [Finset.sum_boole]
  simp [exactSuccessorFinset]

/-- Nonzero projective successor mass is equivalent to a nonempty exact
ambient-codimension successor set. -/
theorem successorMass_ne_zero_iff_exactSuccessor_nonempty
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p) :
    successorMass V p x ≠ 0 ↔
      (exactSuccessorFinset V p x).Nonempty := by
  rw [successorMass_eq_exactSuccessor_card]
  exact_mod_cast Finset.card_ne_zero

/-- Elementwise form: successor mass is nonzero exactly when one genuine
relative successor survives in the exact ambient p+1 stratum. -/
theorem successorMass_ne_zero_iff_exists_exact
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p) :
    successorMass V p x ≠ 0 ↔
      ∃ y : {y : pointClosureScheme V x.1 // Order.coheight y = 1},
        y ∈ relativeCodimensionOneFinset V x.1 ∧
        Order.coheight (ambientSuccessorPoint V x.1 y) = p + 1 := by
  rw [successorMass_ne_zero_iff_exactSuccessor_nonempty]
  constructor
  · rintro ⟨y,hy⟩
    exact ⟨y, (mem_exactSuccessorFinset V p x y).1 hy⟩
  · rintro ⟨y,hyrel,hygrade⟩
    exact ⟨y, (mem_exactSuccessorFinset V p x y).2 ⟨hyrel,hygrade⟩⟩

/-- Any one exact successor immediately gives intrinsic unit-mass normalization
and the canonical limitless next-weight shadow. -/
theorem exactSuccessor_yields_canonical_limitless_state
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (y : {y : pointClosureScheme V x.1 // Order.coheight y = 1})
    (hyrel : y ∈ relativeCodimensionOneFinset V x.1)
    (hygrade : Order.coheight (ambientSuccessorPoint V x.1 y) = p + 1) :
    nativeCycleMass V (p + 1)
        (intrinsicNormalizedSuccessor V p x) = 1
      ∧ intrinsicNormalizedSuccessor V p x ≠ 0
      ∧ nativeCycleCosmicShadow V (p + 1)
          (intrinsicNormalizedSuccessor V p x) =
            GSTClassicalHodgeLimitlessCosmicMatrixUnits.rationalCosmicBasis (p + 1) := by
  have hmass : successorMass V p x ≠ 0 :=
    (successorMass_ne_zero_iff_exists_exact V p x).2
      ⟨y,hyrel,hygrade⟩
  exact intrinsic_successor_normalization_crown V p x hmass

#check exactSuccessorFinset
#check mem_exactSuccessorFinset
#check presentationMass_successorAtom
#check successorMass_eq_exactSuccessor_card
#check successorMass_ne_zero_iff_exactSuccessor_nonempty
#check successorMass_ne_zero_iff_exists_exact
#check exactSuccessor_yields_canonical_limitless_state

#print axioms presentationMass_successorAtom
#print axioms successorMass_eq_exactSuccessor_card
#print axioms successorMass_ne_zero_iff_exactSuccessor_nonempty
#print axioms successorMass_ne_zero_iff_exists_exact
#print axioms exactSuccessor_yields_canonical_limitless_state

end GSTClassicalHodgeExactSuccessorMass
