import GSTClassicalHodgePointClosureRelativeCut
import GSTClassicalHodgeSchemeCodimensionStalk
import GSTCompactNativeCyclePresentation
import GSTGeometricRealizationStage2D
import GSTClassicalHodgePointKernelOperatorLift

/-!
# GST CLASSICAL HODGE — EXACT-STRATUM PRINCIPAL-CUT SUCCESSOR OPERATOR

The relative principal-cut engine gives finitely many codimension-one successor
candidates inside the irreducible closure of every source point.  Their ambient
codimension need not be guessed: the native cycle space already has an exact
coheight grading, equivalently an exact stalk-Krull-dimension grading.

For a source atom of ambient codimension `p`, this module maps all relative
successors back to the ambient smooth projective scheme and retains precisely
those lying in the exact ambient codimension `p+1` stratum.  The resulting
finite presentation is therefore unconditionally a native codimension-`p+1`
presentation.  Free linear extension and the compact point-normal form then
produce a genuine native graded operator

    codimensionCycles V.X p -> codimensionCycles V.X (p+1).

No Hodge data and no cycle-class map occur in this construction.  The later
nonvanishing/exhaustion theorem must prove that the exact-stratum filter really
captures the projective principal-cut successors required for Lefschetz
propagation; it is not assumed here.
-/

set_option maxHeartbeats 40000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTNativeCodimensionCyclePresentation
open GSTCompactNativeCyclePresentation
open GSTClassicalHodgePointClosurePrincipalCut
open GSTClassicalHodgePointClosureRelativeCut
open GSTClassicalHodgeSchemeCodimensionStalk
open GSTGeometricRealizationStage2D
open GSTClassicalHodgePointKernelOperatorLift
open GSTClassicalHodgePointNormalForm

namespace GSTClassicalHodgePrincipalCutSuccessorOperator

/-- Ambient image of one relative codimension-one successor candidate. -/
noncomputable def ambientSuccessorPoint
    (V : SmoothProjectiveComplexScheme)
    (x : V.X)
    (y : {y : pointClosureScheme V x // Order.coheight y = 1}) : V.X :=
  pointClosureι V x y.1

/-- Exact-stratum contribution of one relative successor candidate.  It is a
unit atom when the ambient codimension is exactly one greater than the source
codimension, and zero otherwise. -/
noncomputable def successorAtomPresentation
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (y : {y : pointClosureScheme V x.1 // Order.coheight y = 1}) :
    FiniteCodimensionPresentation V.X (p + 1) := by
  classical
  by_cases hy : Order.coheight (ambientSuccessorPoint V x.1 y) = p + 1
  · exact Finsupp.single ⟨ambientSuccessorPoint V x.1 y, hy⟩ 1
  · exact 0

/-- Finite exact-ambient-codimension successor presentation of one source atom. -/
noncomputable def successorPresentation
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p) :
    FiniteCodimensionPresentation V.X (p + 1) := by
  classical
  exact (relativeCodimensionOneFinset V x.1).sum
    (successorAtomPresentation V p x)

/-- If a relative successor has the expected ambient codimension, its unit
point presentation occurs as its direct generator contribution. -/
theorem successorAtomPresentation_eq_single
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (y : {y : pointClosureScheme V x.1 // Order.coheight y = 1})
    (hy : Order.coheight (ambientSuccessorPoint V x.1 y) = p + 1) :
    successorAtomPresentation V p x y =
      Finsupp.single
        (⟨ambientSuccessorPoint V x.1 y, hy⟩ : CodimensionPoint V.X (p + 1)) 1 := by
  classical
  simp [successorAtomPresentation, hy]

/-- Wrong ambient grading contributes zero rather than contaminating the
codimension-p+1 cycle space. -/
theorem successorAtomPresentation_eq_zero
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (y : {y : pointClosureScheme V x.1 // Order.coheight y = 1})
    (hy : Order.coheight (ambientSuccessorPoint V x.1 y) ≠ p + 1) :
    successorAtomPresentation V p x y = 0 := by
  classical
  simp [successorAtomPresentation, hy]

/-- Free linear extension of the exact-stratum successor kernel to finite
codimension-p point presentations. -/
noncomputable def successorPresentationOperator
    (V : SmoothProjectiveComplexScheme)
    (p : Nat) :
    FiniteCodimensionPresentation V.X p →ₗ[ℚ]
      FiniteCodimensionPresentation V.X (p + 1) where
  toFun φ := φ.sum fun x q => q • successorPresentation V p x
  map_add' := by
    intro φ ψ
    classical
    refine Finsupp.sum_add_index (fun x _ => zero_smul _ _)
      (fun x _ a b => add_smul a b _)
  map_smul' := by
    intro q φ
    show (q • φ).sum (fun x c => c • successorPresentation V p x) =
      q • φ.sum (fun x c => c • successorPresentation V p x)
    rw [Finsupp.sum_smul_index']
    · simp only [smul_eq_mul, mul_smul, Finsupp.sum]
      rw [Finset.smul_sum]
    · exact fun x => zero_smul _ _

@[simp]
theorem successorPresentationOperator_single
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (q : ℚ) :
    successorPresentationOperator V p (Finsupp.single x q) =
      q • successorPresentation V p x := by
  classical
  simp [successorPresentationOperator]

/-- Realization of finite presentations is additive. -/
theorem realizeFiniteCodimensionPresentation_add
    (X : Scheme) (p : Nat)
    (φ ψ : FiniteCodimensionPresentation X p) :
    realizeFiniteCodimensionPresentation X p (φ + ψ) =
      realizeFiniteCodimensionPresentation X p φ +
        realizeFiniteCodimensionPresentation X p ψ := by
  refine Finsupp.sum_add_index' (fun x => zero_smul _ _)
    (fun x a b => add_smul a b _)

/-- Realization of finite presentations is homogeneous. -/
theorem realizeFiniteCodimensionPresentation_smul
    (X : Scheme) (p : Nat) (q : ℚ)
    (φ : FiniteCodimensionPresentation X p) :
    realizeFiniteCodimensionPresentation X p (q • φ) =
      q • realizeFiniteCodimensionPresentation X p φ := by
  show (q • φ).sum (fun x c => c • codimensionPointCycle X p x) =
    q • φ.sum (fun x c => c • codimensionPointCycle X p x)
  rw [Finsupp.sum_smul_index']
  · simp only [smul_eq_mul, mul_smul, Finsupp.sum]
    rw [Finset.smul_sum]
  · exact fun x => zero_smul _ _

/-- Realize the successor presentation as an actual native target cycle. -/
noncomputable def successorFiniteNativeOperator
    (V : SmoothProjectiveComplexScheme)
    (p : Nat) :
    FiniteCodimensionPresentation V.X p →ₗ[ℚ]
      codimensionCycles V.X (p + 1) where
  toFun φ :=
    realizeFiniteCodimensionPresentation V.X (p + 1)
      (successorPresentationOperator V p φ)
  map_add' := by
    intro φ ψ
    rw [LinearMap.map_add]
    exact realizeFiniteCodimensionPresentation_add V.X (p + 1) _ _
  map_smul' := by
    intro q φ
    rw [LinearMap.map_smul]
    exact realizeFiniteCodimensionPresentation_smul V.X (p + 1) q _

/-- **UNCONDITIONAL GEOMETRY-BUILT GRADED SUCCESSOR OPERATOR.** -/
noncomputable def successorNativeOperator
    (V : SmoothProjectiveComplexScheme)
    (p : Nat) :
    codimensionCycles V.X p →ₗ[ℚ]
      codimensionCycles V.X (p + 1) := by
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  exact (successorFiniteNativeOperator V p).comp
    (presentationOfNativeCycleLinear V.X p)

/-- Point-generator formula. -/
theorem successorNativeOperator_point
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p) :
    successorNativeOperator V p (codimensionPointCycle V.X p x) =
      realizeFiniteCodimensionPresentation V.X (p + 1)
        (successorPresentation V p x) := by
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  have h1 : presentationOfNativeCycleLinear V.X p
      (codimensionPointCycle V.X p x) = Finsupp.single x (1 : ℚ) := by
    classical
    rw [presentationOfNativeCycleLinear_apply]
    ext y
    show ((codimensionPointCycle V.X p x).1 : AlgebraicCycle V.X ℚ) y.1
      = (Finsupp.single x (1 : ℚ)) y
    by_cases hy : y = x
    · rw [hy]
      simp [codimensionPointCycle, Function.locallyFinsuppWithin.single_apply]
    · have hne : y.1 ≠ x.1 := fun heq => hy (Subtype.ext heq)
      have hz : ((codimensionPointCycle V.X p x).1 : AlgebraicCycle V.X ℚ) y.1 = 0 := by
        simp [codimensionPointCycle, hne, Function.locallyFinsuppWithin.single_apply]
      rw [hz]
      simp [hy]
  show (successorFiniteNativeOperator V p).comp
      (presentationOfNativeCycleLinear V.X p)
      (codimensionPointCycle V.X p x) =
    realizeFiniteCodimensionPresentation V.X (p + 1)
      (successorPresentation V p x)
  rw [LinearMap.comp_apply, h1]
  show realizeFiniteCodimensionPresentation V.X (p + 1)
      (successorPresentationOperator V p (Finsupp.single x (1 : ℚ))) =
    realizeFiniteCodimensionPresentation V.X (p + 1)
      (successorPresentation V p x)
  rw [successorPresentationOperator_single, one_smul]

/-- Every generator image is explicitly represented by finitely many exact
ambient codimension-p+1 point atoms. -/
theorem successorNativeOperator_has_finite_target
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p) :
    ∃ φ : FiniteCodimensionPresentation V.X (p + 1),
      successorNativeOperator V p (codimensionPointCycle V.X p x) =
        realizeFiniteCodimensionPresentation V.X (p + 1) φ := by
  exact ⟨successorPresentation V p x,
    successorNativeOperator_point V p x⟩

#check ambientSuccessorPoint
#check successorAtomPresentation
#check successorPresentation
#check successorPresentationOperator
#check successorFiniteNativeOperator
#check successorNativeOperator
#check successorNativeOperator_point
#check successorNativeOperator_has_finite_target

#print axioms successorAtomPresentation_eq_single
#print axioms successorPresentationOperator_single
#print axioms successorNativeOperator_point
#print axioms successorNativeOperator_has_finite_target

end GSTClassicalHodgePrincipalCutSuccessorOperator
