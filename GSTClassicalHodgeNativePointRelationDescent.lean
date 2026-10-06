import GSTClassicalHodgePointKernelOperatorLift
import Mathlib.Algebra.Module.Projective

/-!
# GST native-first finite-relation descent

Upgrade of `PointClassTransitionKernel.nativeCycleOperator_natural`:
the old theorem starts with an ambient operator T and a kernel whose point
action already matches T. Here a RAW native point-transition kernel comes
first. Preservation of finite point-class relations constructs the ambient
operator and then constructs the old transition-kernel package.

The criterion quantifies over actual finite native relations. It assumes no
target representative and no all-target algebraicity. Ambient extension is
unique on the actual cycle-class range, with no uniqueness claim outside it.
-/

noncomputable section

open AlgebraicGeometry
open GSTGeometricRealizationStage2D
open GSTNativeCodimensionCyclePresentation
open GSTCompactNativeCyclePresentation
open GSTClassicalHodgePointNormalForm
open GSTClassicalHodgePointKernelOperatorLift
open GSTClassicalHodgeGeneratorwiseAtomicStability
open GSTClassicalHodgeAtomicSpan

namespace GSTClassicalHodgeNativePointRelationDescent

universe u v
variable {X : Scheme.{u}}
variable {Coh : Type v} [AddCommGroup Coh] [Module ℚ Coh]
variable {p : Nat}

/-- Explicitly retain the class map in the kernel condition. -/
def NativeClassKernelStable
    (cl : codimensionCycles X p →ₗ[ℚ] Coh)
    (A : Module.End ℚ (codimensionCycles X p)) : Prop :=
  ∀ Z, cl Z = 0 → cl (A Z) = 0

theorem transformedClass_congr
    (cl : codimensionCycles X p →ₗ[ℚ] Coh)
    (A : Module.End ℚ (codimensionCycles X p))
    (hk : NativeClassKernelStable cl A)
    {Z W : codimensionCycles X p} (hZW : cl Z = cl W) :
    cl (A Z) = cl (A W) := by
  have hz : cl (Z - W) = 0 := by rw [map_sub, hZW, sub_self]
  have h := hk (Z - W) hz
  simp only [map_sub] at h
  exact sub_eq_zero.mp h

def classRangeRepresentative
    (cl : codimensionCycles X p →ₗ[ℚ] Coh)
    (y : LinearMap.range cl) : codimensionCycles X p := Classical.choose y.2

@[simp] theorem classRangeRepresentative_spec
    (cl : codimensionCycles X p →ₗ[ℚ] Coh) (y : LinearMap.range cl) :
    cl (classRangeRepresentative cl y) = y.1 := Classical.choose_spec y.2

/-- The action is well-defined on the actual native class range because of
kernel preservation, independently of which native preimage is chosen. -/
def nativeClassRangeAction
    (cl : codimensionCycles X p →ₗ[ℚ] Coh)
    (A : Module.End ℚ (codimensionCycles X p))
    (hk : NativeClassKernelStable cl A) : LinearMap.range cl →ₗ[ℚ] Coh where
  toFun y := cl (A (classRangeRepresentative cl y))
  map_add' := by
    intro x y
    have heq : cl (classRangeRepresentative cl (x + y)) =
        cl (classRangeRepresentative cl x + classRangeRepresentative cl y) := by simp
    calc
      cl (A (classRangeRepresentative cl (x + y))) =
          cl (A (classRangeRepresentative cl x + classRangeRepresentative cl y)) :=
        transformedClass_congr cl A hk heq
      _ = _ := by simp
  map_smul' := by
    intro q x
    have heq : cl (classRangeRepresentative cl (q • x)) =
        cl (q • classRangeRepresentative cl x) := by simp
    calc
      cl (A (classRangeRepresentative cl (q • x))) =
          cl (A (q • classRangeRepresentative cl x)) :=
        transformedClass_congr cl A hk heq
      _ = _ := by simp

/-- Extend the derived range action; nothing is prescribed outside native
classes. This existing rational-linear extension device is used only after
the native finite-relation condition has been proved. -/
def nativeAmbientAction
    (cl : codimensionCycles X p →ₗ[ℚ] Coh)
    (A : Module.End ℚ (codimensionCycles X p))
    (hk : NativeClassKernelStable cl A) : Module.End ℚ Coh :=
  Classical.choose (LinearMap.exists_extend (nativeClassRangeAction cl A hk))

theorem nativeAmbientAction_natural
    (cl : codimensionCycles X p →ₗ[ℚ] Coh)
    (A : Module.End ℚ (codimensionCycles X p))
    (hk : NativeClassKernelStable cl A) (Z : codimensionCycles X p) :
    nativeAmbientAction cl A hk (cl Z) = cl (A Z) := by
  have hext : (nativeAmbientAction cl A hk).comp (LinearMap.range cl).subtype =
      nativeClassRangeAction cl A hk :=
    Classical.choose_spec (LinearMap.exists_extend (nativeClassRangeAction cl A hk))
  have h := LinearMap.congr_fun hext (cl.rangeRestrict Z)
  change nativeAmbientAction cl A hk (cl Z) =
    cl (A (classRangeRepresentative cl (cl.rangeRestrict Z))) at h
  exact h.trans (transformedClass_congr cl A hk (classRangeRepresentative_spec cl _))

/-- Native kernel preservation is also necessary. -/
theorem exists_nativeAmbientAction_iff
    (cl : codimensionCycles X p →ₗ[ℚ] Coh)
    (A : Module.End ℚ (codimensionCycles X p)) :
    (∃ T : Module.End ℚ Coh, cl.comp A = T.comp cl) ↔ NativeClassKernelStable cl A := by
  constructor
  · rintro ⟨T, hT⟩ Z hZ
    have h := LinearMap.congr_fun hT Z
    simpa [hZ] using h
  · intro hk
    refine ⟨nativeAmbientAction cl A hk, ?_⟩
    ext Z
    exact (nativeAmbientAction_natural cl A hk Z).symm

/-- Raw point transition: finite native output at each genuine point. -/
def rawPresentationOperator
    (κ : CodimensionPoint X p → FiniteCodimensionPresentation X p) :
    Module.End ℚ (FiniteCodimensionPresentation X p) := Finsupp.linearCombination ℚ κ

@[simp] theorem rawPresentationOperator_single
    (κ : CodimensionPoint X p → FiniteCodimensionPresentation X p)
    (x : CodimensionPoint X p) :
    rawPresentationOperator κ (Finsupp.single x 1) = κ x := by
  simp [rawPresentationOperator]

def rawNativeOperator [CompactSpace X]
    (κ : CodimensionPoint X p → FiniteCodimensionPresentation X p) :
    Module.End ℚ (codimensionCycles X p) :=
  (compactCyclePresentationLinearEquiv X p).toLinearMap.comp
    ((rawPresentationOperator κ).comp
      (compactCyclePresentationLinearEquiv X p).symm.toLinearMap)

@[simp] theorem rawNativeOperator_realize [CompactSpace X]
    (κ : CodimensionPoint X p → FiniteCodimensionPresentation X p)
    (φ : FiniteCodimensionPresentation X p) :
    rawNativeOperator κ (realizeFiniteCodimensionPresentation X p φ) =
      realizeFiniteCodimensionPresentation X p (rawPresentationOperator κ φ) := by
  simp [rawNativeOperator, presentation_realizeFiniteCodimensionPresentation]

@[simp] theorem rawNativeOperator_point [CompactSpace X]
    (κ : CodimensionPoint X p → FiniteCodimensionPresentation X p)
    (x : CodimensionPoint X p) :
    rawNativeOperator κ (codimensionPointCycle X p x) =
      realizeFiniteCodimensionPresentation X p (κ x) := by
  simp [rawNativeOperator, presentationOfNativeCycle_point]

/-- Finite class relations are preserved by the raw transition. -/
def PreservesFiniteClassRelations
    (cl : codimensionCycles X p →ₗ[ℚ] Coh)
    (κ : CodimensionPoint X p → FiniteCodimensionPresentation X p) : Prop :=
  ∀ φ : FiniteCodimensionPresentation X p,
    cl (realizeFiniteCodimensionPresentation X p φ) = 0 →
      cl (realizeFiniteCodimensionPresentation X p (rawPresentationOperator κ φ)) = 0

/-- Point relations detect exactly the genuine native kernel condition. -/
theorem finiteRelations_iff_nativeKernelStable [CompactSpace X]
    (cl : codimensionCycles X p →ₗ[ℚ] Coh)
    (κ : CodimensionPoint X p → FiniteCodimensionPresentation X p) :
    PreservesFiniteClassRelations cl κ ↔ NativeClassKernelStable cl (rawNativeOperator κ) := by
  constructor
  · intro h Z hZ
    let φ := presentationOfNativeCycle X p Z
    have hφ : realizeFiniteCodimensionPresentation X p φ = Z :=
      GSTClassicalHodgePointNormalForm.realize_presentationOfNativeCycle X p Z
    have hz := h φ (by simpa [hφ] using hZ)
    rw [← rawNativeOperator_realize, hφ] at hz
    exact hz
  · intro h φ hφ
    simpa using h (realizeFiniteCodimensionPresentation X p φ) hφ

/-- **NATIVE-FIRST ACTION SYNTHESIS.** The cohomological action is an OUTPUT
of a raw finite native transition precisely when its finite class relations
are respected. No action equation or target cycle is included as input. -/
theorem rawTransition_has_ambientAction_iff [CompactSpace X]
    (cl : codimensionCycles X p →ₗ[ℚ] Coh)
    (κ : CodimensionPoint X p → FiniteCodimensionPresentation X p) :
    (∃ T : Module.End ℚ Coh, cl.comp (rawNativeOperator κ) = T.comp cl) ↔
      PreservesFiniteClassRelations cl κ := by
  rw [exists_nativeAmbientAction_iff, finiteRelations_iff_nativeKernelStable]

/-- Upgrade the already-compiled point-kernel interface: both the ambient
action and the point action equation are now derived from raw native data. -/
def derivedPointClassTransitionKernel [CompactSpace X]
    (cl : codimensionCycles X p →ₗ[ℚ] Coh)
    (κ : CodimensionPoint X p → FiniteCodimensionPresentation X p)
    (hκ : PreservesFiniteClassRelations cl κ) :
    PointClassTransitionKernel (p := p) (cl := cl)
      (nativeAmbientAction cl (rawNativeOperator κ)
        ((finiteRelations_iff_nativeKernelStable cl κ).mp hκ)) where
  transition := κ
  transition_spec := by
    intro x
    have h := nativeAmbientAction_natural cl (rawNativeOperator κ)
      ((finiteRelations_iff_nativeKernelStable cl κ).mp hκ)
      (codimensionPointCycle X p x)
    simpa [rawNativeOperator_point, finitePointCycleClassMap_eq_cycleClass_realize]
      using h.symm

#print axioms nativeAmbientAction_natural
#print axioms exists_nativeAmbientAction_iff
#print axioms finiteRelations_iff_nativeKernelStable
#print axioms rawTransition_has_ambientAction_iff
#print axioms derivedPointClassTransitionKernel

end GSTClassicalHodgeNativePointRelationDescent
