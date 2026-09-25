import Mathlib
import GSTNativeCodimensionCyclePresentation

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTGeometricRealizationStage2D
open GSTNativeCodimensionCyclePresentation

namespace GSTCompactNativeCyclePresentation

universe u

/-- On a compact scheme every locally finite algebraic cycle has globally
finite support. -/
theorem native_cycle_support_finite
    (X : Scheme.{u}) [CompactSpace X]
    (Z : AlgebraicCycle X ℚ) :
    Z.support.Finite := by
  simpa using
    Z.locallyFiniteSupport.finite_inter_support_of_isCompact
      (W := Set.univ) isCompact_univ

/-- Restrict a compactly supported native codimension-p cycle to its genuine
codimension-p points, producing a finite rational presentation. -/
noncomputable def presentationOfNativeCycle
    (X : Scheme.{u}) [CompactSpace X] (p : Nat)
    (Z : codimensionCycles X p) :
    FiniteCodimensionPresentation X p :=
  Finsupp.ofSupportFinite
    (fun x : CodimensionPoint X p => (Z.1 : AlgebraicCycle X ℚ) x.1)
    (by
      have hfin : (Z.1 : AlgebraicCycle X ℚ).support.Finite :=
        native_cycle_support_finite X Z.1
      have hpre :
          (Subtype.val ⁻¹' (Z.1 : AlgebraicCycle X ℚ).support).Finite :=
        hfin.preimage Subtype.val_injective.injOn
      simpa [Function.support] using hpre)

@[simp]
theorem presentationOfNativeCycle_apply
    (X : Scheme.{u}) [CompactSpace X] (p : Nat)
    (Z : codimensionCycles X p)
    (x : CodimensionPoint X p) :
    presentationOfNativeCycle X p Z x = (Z.1 : AlgebraicCycle X ℚ) x.1 := by
  rfl

#check native_cycle_support_finite
#check presentationOfNativeCycle
#check presentationOfNativeCycle_apply

#print axioms native_cycle_support_finite
#print axioms presentationOfNativeCycle_apply

end GSTCompactNativeCyclePresentation
