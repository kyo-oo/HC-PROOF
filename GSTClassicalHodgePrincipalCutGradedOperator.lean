import GSTClassicalHodgePrincipalCutNativeCycle
import GSTCompactNativeCyclePresentation

/-!
# GST CLASSICAL HODGE — PRINCIPAL-CUT GRADED NATIVE OPERATOR

The projective principal-cut construction is linearized into a genuine native
graded cycle operator.  On each codimension-zero generic point it outputs the
finite codimension-one cycle cut out by the point-specific positive-degree
projective separator.  Free finite presentations extend this generator action
linearly; compactness of the smooth projective carrier then extends it to every
native codimension-zero algebraic cycle.

This is an actual geometry-built `codimension 0 -> codimension 1` operator.
It is independent of Hodge semantics and of the cycle-class map.  Later
naturality modules compare its induced class with the limitless Lefschetz
transport.
-/

set_option maxHeartbeats 30000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTNativeCodimensionCyclePresentation
open GSTCompactNativeCyclePresentation
open GSTClassicalHodgePrincipalCutNativeCycle

namespace GSTClassicalHodgePrincipalCutGradedOperator

variable (V : SmoothProjectiveComplexScheme)
variable [IrreducibleSpace V.X]

/-- Generator kernel: a codimension-zero point is sent to the finite
codimension-one presentation produced by its selected principal cut. -/
noncomputable def zeroToOnePointKernel
    (x : CodimensionPoint V.X 0) :
    FiniteCodimensionPresentation V.X 1 :=
  principalCutPresentation V x.1

/-- Free linear extension on finite point presentations. -/
noncomputable def zeroToOnePresentationOperator :
    FiniteCodimensionPresentation V.X 0 →ₗ[ℚ]
      FiniteCodimensionPresentation V.X 1 where
  toFun φ := φ.sum fun x q => q • zeroToOnePointKernel V x
  map_add' := by
    intro φ ψ
    classical
    simp
  map_smul' := by
    intro q φ
    classical
    simp [smul_smul]

@[simp]
theorem zeroToOnePresentationOperator_single
    (x : CodimensionPoint V.X 0) (q : ℚ) :
    zeroToOnePresentationOperator V (Finsupp.single x q) =
      q • zeroToOnePointKernel V x := by
  classical
  simp [zeroToOnePresentationOperator]

/-- Realize the finite target presentation as an actual native
codimension-one cycle. -/
noncomputable def zeroToOneFiniteNative :
    FiniteCodimensionPresentation V.X 0 →ₗ[ℚ]
      codimensionCycles V.X 1 where
  toFun φ :=
    realizeFiniteCodimensionPresentation V.X 1
      (zeroToOnePresentationOperator V φ)
  map_add' := by
    intro φ ψ
    simp [zeroToOnePresentationOperator,
      realizeFiniteCodimensionPresentation]
  map_smul' := by
    intro q φ
    simp [zeroToOnePresentationOperator,
      realizeFiniteCodimensionPresentation, smul_smul]

/-- **NATIVE PRINCIPAL-CUT GRADED OPERATOR.**
Every native codimension-zero cycle has a finite point normal form; apply the
principal-cut kernel generatorwise and realize the result in codimension one. -/
noncomputable def zeroToOneNativeOperator :
    codimensionCycles V.X 0 →ₗ[ℚ] codimensionCycles V.X 1 := by
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  exact (zeroToOneFiniteNative V).comp
    (presentationOfNativeCycleLinear V.X 0)

/-- Point-generator formula for the native graded operator. -/
theorem zeroToOneNativeOperator_point
    (x : CodimensionPoint V.X 0) :
    zeroToOneNativeOperator V (codimensionPointCycle V.X 0 x) =
      principalCutCycle V x.1 := by
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  simp [zeroToOneNativeOperator, zeroToOneFiniteNative,
    zeroToOnePresentationOperator, zeroToOnePointKernel,
    principalCutCycle]

/-- The operator is geometrically generated on every codimension-zero atom by
an actual projective principal section. -/
theorem zeroToOneNativeOperator_generator_crown :
    ∀ x : CodimensionPoint V.X 0,
      zeroToOneNativeOperator V (codimensionPointCycle V.X 0 x) =
        principalCutCycle V x.1 := by
  exact zeroToOneNativeOperator_point V

#check zeroToOnePointKernel
#check zeroToOnePresentationOperator
#check zeroToOneFiniteNative
#check zeroToOneNativeOperator
#check zeroToOneNativeOperator_point
#check zeroToOneNativeOperator_generator_crown

#print axioms zeroToOnePresentationOperator_single
#print axioms zeroToOneNativeOperator_point
#print axioms zeroToOneNativeOperator_generator_crown

end GSTClassicalHodgePrincipalCutGradedOperator
