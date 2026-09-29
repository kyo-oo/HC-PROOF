import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import GSTClassicalHodgeAtomicOperatorAlgebra
import GSTClassicalHodgeCycleOperatorNaturality

/-!
# GST CLASSICAL HODGE — POINT-KERNEL OPERATOR LIFT

On a compact scheme, native codimension-p rational algebraic cycles are
exactly finite rational combinations of genuine codimension-p points.
The existing reconstruction theorem gives the right inverse; pointwise
coefficient recovery gives the left inverse.  Hence the two spaces are
rational-linearly equivalent.

This makes the generatorwise transition interface fully equivalent to the
older native-operator interface:

* a point-transition kernel extends freely to finite presentations;
* conjugating by the compact presentation equivalence gives a linear operator
  on all native codimension-p cycles;
* the pointwise transition equations imply the full cycle-class commuting
  square by linearity.

Therefore a point-transition kernel automatically manufactures the complete
`CycleClassOperatorPair` needed by native polynomial spectral extraction.
No independent operator on arbitrary cycles has to be supplied.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTCompactNativeCyclePresentation
open GSTClassicalHodgePointNormalForm
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeGeneratorwiseAtomicStability
open GSTClassicalHodgeCycleOperatorNaturality

namespace GSTClassicalHodgePointKernelOperatorLift

universe u v

variable {X : Scheme.{u}}
variable {Coh : Type v} [AddCommGroup Coh] [Module ℚ Coh]
variable {p : Nat}
variable {cl : codimensionCycles X p →ₗ[ℚ] Coh}

/-- Coefficient extraction after realization recovers the original finite
presentation exactly. -/
theorem presentation_realizeFiniteCodimensionPresentation
    (X : Scheme.{u}) [CompactSpace X] (p : Nat)
    (φ : FiniteCodimensionPresentation X p) :
    presentationOfNativeCycle X p
      (realizeFiniteCodimensionPresentation X p φ) = φ := by
  classical
  apply Finsupp.ext
  intro x
  rw [presentationOfNativeCycle_apply,
    realizeFiniteCodimensionPresentation_apply X p φ x.1]
  simp only [Finsupp.sum, smul_eq_mul]
  refine (Finset.sum_eq_single x ?_ ?_).trans ?_
  · intro b _ hb
    have hne : x.1 ≠ b.1 := fun heq => hb (Subtype.ext heq.symm)
    simp [hne]
  · intro hout
    simp [Finsupp.notMem_support_iff.mp hout]
  · simp

/-- **COMPACT CYCLE/PRESENTATION LINEAR EQUIVALENCE.** -/
noncomputable def compactCyclePresentationLinearEquiv
    (X : Scheme.{u}) [CompactSpace X] (p : Nat) :
    FiniteCodimensionPresentation X p ≃ₗ[ℚ] codimensionCycles X p where
  toLinearMap := realizePresentationLinear X p
  invFun := presentationOfNativeCycle X p
  left_inv := presentation_realizeFiniteCodimensionPresentation X p
  right_inv := realize_presentationOfNativeCycle X p

@[simp]
theorem compactCyclePresentationLinearEquiv_apply
    (X : Scheme.{u}) [CompactSpace X] (p : Nat)
    (φ : FiniteCodimensionPresentation X p) :
    compactCyclePresentationLinearEquiv X p φ =
      realizeFiniteCodimensionPresentation X p φ :=
  rfl

@[simp]
theorem compactCyclePresentationLinearEquiv_symm_apply
    (X : Scheme.{u}) [CompactSpace X] (p : Nat)
    (Z : codimensionCycles X p) :
    (compactCyclePresentationLinearEquiv X p).symm Z =
      presentationOfNativeCycle X p Z :=
  rfl

-- ISLAND-FROM-ROOT (empirically verified: dot-decl prefixes do NOT consult
-- `open`s — `PointClassTransitionKernel.x` declared in this file's own
-- namespace lands in the WRONG island and every dot-usage fails with
-- 'environment does not contain'. The extensions must be declared from the
-- structure's home namespace at top level.)
end GSTClassicalHodgePointKernelOperatorLift

namespace GSTClassicalHodgeGeneratorwiseAtomicStability
open GSTClassicalHodgePointKernelOperatorLift

variable {X : Scheme.{u}}
variable {Coh : Type v} [AddCommGroup Coh] [Module ℚ Coh]
variable {p : Nat}
variable {cl : codimensionCycles X p →ₗ[ℚ] Coh}

-- ISLAND-FROM-ROOT (empirically verified: dot-decl prefixes do NOT consult
-- `open`s — `PointClassTransitionKernel.x` declared in this file's own
-- namespace lands in the WRONG island and every dot-usage fails with
-- 'environment does not contain'. The extensions must be declared from the
-- structure's home namespace at top level.)
/-- Free linear extension of a point-transition kernel to arbitrary finite
point presentations. -/
noncomputable def PointClassTransitionKernel.presentationOperator
    {T : Coh →ₗ[ℚ] Coh}
    (K : PointClassTransitionKernel (p := p) (cl := cl) T) :
    FiniteCodimensionPresentation X p →ₗ[ℚ]
      FiniteCodimensionPresentation X p :=
  Finsupp.linearCombination ℚ K.transition

@[simp]
theorem PointClassTransitionKernel.presentationOperator_single
    {T : Coh →ₗ[ℚ] Coh}
    (K : PointClassTransitionKernel (p := p) (cl := cl) T)
    (x : CodimensionPoint X p) :
    K.presentationOperator (Finsupp.single x 1) = K.transition x := by
  simp [PointClassTransitionKernel.presentationOperator]

/-- The freely extended presentation operator intertwines the free point-class
map with the cohomological observable on every finite presentation. -/
theorem PointClassTransitionKernel.finitePointClass_natural
    {T : Coh →ₗ[ℚ] Coh}
    (K : PointClassTransitionKernel (p := p) (cl := cl) T) :
    (finitePointCycleClassMap p cl).comp K.presentationOperator =
      T.comp (finitePointCycleClassMap p cl) := by
  apply Finsupp.lhom_ext
  intro x q
  have hspec := K.transition_spec x
  simp only [PointClassTransitionKernel.presentationOperator]
  rw [LinearMap.comp_apply, LinearMap.comp_apply,
    Finsupp.linearCombination_single, map_smul, hspec,
    finitePointCycleClassMap_eq_cycleClass_realize,
    realizeFiniteCodimensionPresentation_single, map_smul]

/-- Conjugate the free presentation operator through the compact cycle/
presentation equivalence to obtain an operator on all native cycles. -/
noncomputable def PointClassTransitionKernel.nativeCycleOperator
    [CompactSpace X]
    {T : Coh →ₗ[ℚ] Coh}
    (K : PointClassTransitionKernel (p := p) (cl := cl) T) :
    codimensionCycles X p →ₗ[ℚ] codimensionCycles X p :=
  (compactCyclePresentationLinearEquiv X p).toLinearMap.comp
    (K.presentationOperator.comp
      (compactCyclePresentationLinearEquiv X p).symm.toLinearMap)

/-- **POINT KERNEL → FULL CYCLE-CLASS NATURALITY.**
The native cycle operator induced from the point-transition kernel commutes
exactly with the supplied cycle-class map on every native cycle. -/
theorem PointClassTransitionKernel.nativeCycleOperator_natural
    [CompactSpace X]
    {T : Coh →ₗ[ℚ] Coh}
    (K : PointClassTransitionKernel (p := p) (cl := cl) T) :
    cl.comp K.nativeCycleOperator = T.comp cl := by
  apply LinearMap.ext
  intro Z
  have hZ : realizeFiniteCodimensionPresentation X p
      (presentationOfNativeCycle X p Z) = Z :=
    realize_presentationOfNativeCycle X p Z
  have hfree' := LinearMap.congr_fun K.finitePointClass_natural
    (presentationOfNativeCycle X p Z)
  simp only [LinearMap.comp_apply,
    finitePointCycleClassMap_eq_cycleClass_realize] at hfree'
  rw [hZ] at hfree'
  exact hfree'

/-- Package the derived native operator and the original cohomological
observable into the exact commuting-square interface used by the constructive
spectral landing. -/
noncomputable def PointClassTransitionKernel.toCycleClassOperatorPair
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    {p : Nat}
    {T : RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
      RationalSingularCohomology H.analytification (2 * p)}
    (K : PointClassTransitionKernel
      (p := p) (cl := H.cycleClass p) T) :
    CycleClassOperatorPair V H p := by
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  exact {
    cycleOperator := K.nativeCycleOperator
    cohomologyOperator := T
    cycleClass_natural := K.nativeCycleOperator_natural
  }

end GSTClassicalHodgeGeneratorwiseAtomicStability

namespace GSTClassicalHodgePointKernelOperatorLift

/-- Every raw spectral observable equipped only with a point-transition kernel
therefore upgrades to the old full native spectral-cycle operator package. -/
noncomputable def
    GSTClassicalHodgeSpectralSeparatorCollision.RawClassicalHodgeSpectralObservable.toSpectralCycleOperatorViaPointKernel
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    {p : Nat}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : GSTClassicalHodgeSpectralSeparatorCollision.RawClassicalHodgeSpectralObservable
      V H p ι)
    (K : S.PointTransitionKernel) :
    SpectralCycleOperator V H p ι where
  operatorPair := K.toCycleClassOperatorPair
  basisIndex := S.basisIndex
  basisIndex_injective := S.basisIndex_injective
  eigenvalue := S.eigenvalue
  eigenvalue_injective := S.eigenvalue_injective
  eigenvector := S.eigenvector

#check realizePresentationLinear
#check presentationOfNativeCycleLinear
#check presentation_realizeFiniteCodimensionPresentation
#check compactCyclePresentationLinearEquiv
#check PointClassTransitionKernel.presentationOperator
#check PointClassTransitionKernel.finitePointClass_natural
#check PointClassTransitionKernel.nativeCycleOperator
#check PointClassTransitionKernel.nativeCycleOperator_natural
#check PointClassTransitionKernel.toCycleClassOperatorPair
#check GSTClassicalHodgeSpectralSeparatorCollision.RawClassicalHodgeSpectralObservable.toSpectralCycleOperatorViaPointKernel

#print axioms presentation_realizeFiniteCodimensionPresentation
#print axioms compactCyclePresentationLinearEquiv
#print axioms PointClassTransitionKernel.finitePointClass_natural
#print axioms PointClassTransitionKernel.nativeCycleOperator_natural
#print axioms PointClassTransitionKernel.toCycleClassOperatorPair
#print axioms GSTClassicalHodgeSpectralSeparatorCollision.RawClassicalHodgeSpectralObservable.toSpectralCycleOperatorViaPointKernel

end GSTClassicalHodgePointKernelOperatorLift
