import Mathlib
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import GSTNativeCodimensionCyclePresentation
import GSTProjectiveOverC

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicGeometry
open GSTGeometricRealizationStage2D
open GSTNativeCodimensionCyclePresentation
open GSTProjectiveOverC

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

/-- Standard projective space over C is compact in its Zariski topology. -/
theorem projectiveSpace_isCompact_univ (n : Nat) :
    IsCompact (Set.univ : Set (projectiveSpace n)) := by
  have hbase :
      IsCompact (Set.univ : Set (Spec (.of (ProjectiveGrading n 0)))) :=
    isCompact_univ
  have hpre :=
    QuasiCompact.isCompact_preimage
      (f := Proj.toSpecZero (ProjectiveGrading n))
      Set.univ isOpen_univ hbase
  simpa [projectiveSpace] using hpre

/-- Every bundled smooth projective complex scheme has compact underlying
Zariski space, obtained from its closed immersion into projective space. -/
theorem smoothProjective_isCompact_univ
    (V : SmoothProjectiveComplexScheme) :
    IsCompact (Set.univ : Set V.X) := by
  letI : IsClosedImmersion V.projective.immersion :=
    V.projective.closedImmersion
  have hpre :=
    QuasiCompact.isCompact_preimage
      (f := V.projective.immersion)
      Set.univ isOpen_univ
      (projectiveSpace_isCompact_univ V.projective.n)
  simpa using hpre

/-- Local compact-space instance usable inside downstream constructions. -/
noncomputable def smoothProjectiveCompactSpace
    (V : SmoothProjectiveComplexScheme) : CompactSpace V.X :=
  isCompact_iff_compactSpace.mp (smoothProjective_isCompact_univ V)

#check native_cycle_support_finite
#check presentationOfNativeCycle
#check presentationOfNativeCycle_apply
#check projectiveSpace_isCompact_univ
#check smoothProjective_isCompact_univ
#check smoothProjectiveCompactSpace

#print axioms native_cycle_support_finite
#print axioms presentationOfNativeCycle_apply
#print axioms projectiveSpace_isCompact_univ
#print axioms smoothProjective_isCompact_univ

end GSTCompactNativeCyclePresentation
