import GSTClassicalHodgeFiniteClosedCorrespondence
import GSTClassicalHodgePointNormalForm

/-!
# GST CLASSICAL HODGE — FINITE CLOSED CORRESPONDENCE OPERATOR

A finite closed correspondence already gives an actual native target cycle for
each genuine codimension-p source point.  On a smooth projective carrier every
native codimension-p cycle has globally finite support, hence an exact finite
point presentation.  Therefore the pointwise correspondence action extends
canonically and linearly to the complete native codimension-p cycle space.

This file performs that extension.  No cohomological realization and no Hodge
surjectivity statement is used.  The construction is entirely on actual
Mathlib algebraic cycles.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeFiniteClosedCorrespondenceOperator

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTNativeCodimensionCyclePresentation
open GSTCompactNativeCyclePresentation
open GSTClassicalHodgePointNormalForm
open GSTClassicalHodgeFiniteClosedCorrespondence

variable {V : SmoothProjectiveComplexScheme}
variable {p : Nat}

/-- On a smooth projective carrier, taking the actual finite codimension-point
coefficients of a native cycle is rational-linear. -/
noncomputable def nativePresentationLinear
    (V : SmoothProjectiveComplexScheme)
    (p : Nat) :
    codimensionCycles V.X p →ₗ[ℚ] FiniteCodimensionPresentation V.X p where
  toFun := fun Z =>
    letI : CompactSpace V.X := smoothProjectiveCompactSpace V
    presentationOfNativeCycle V.X p Z
  map_add' := by
    intro Z W
    letI : CompactSpace V.X := smoothProjectiveCompactSpace V
    apply Finsupp.ext
    intro x
    simp [presentationOfNativeCycle_apply]
  map_smul' := by
    intro q Z
    letI : CompactSpace V.X := smoothProjectiveCompactSpace V
    apply Finsupp.ext
    intro x
    simp [presentationOfNativeCycle_apply, smul_eq_mul]

/-- The point presentation of one native unit point-cycle is exactly the
corresponding singleton coefficient. -/
theorem nativePresentationLinear_point
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p) :
    nativePresentationLinear V p (codimensionPointCycle V.X p x) =
      Finsupp.single x 1 := by
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  apply Finsupp.ext
  intro y
  by_cases hxy : y = x
  · subst y
    simp [nativePresentationLinear, presentationOfNativeCycle_apply,
      codimensionPointCycle, Function.locallyFinsuppWithin.single_apply]
  · have hval : y.1 ≠ x.1 := by
      intro h
      exact hxy (Subtype.ext h)
    simp [nativePresentationLinear, presentationOfNativeCycle_apply,
      codimensionPointCycle, Function.locallyFinsuppWithin.single_apply,
      hxy, hval]

/-- Linear realization of a finite point presentation through one genuine
finite closed correspondence. -/
noncomputable def correspondencePresentationOperator
    (K : FiniteClosedCorrespondence V)
    (p : Nat) :
    FiniteCodimensionPresentation V.X p →ₗ[ℚ]
      codimensionCycles V.X p :=
  Finsupp.total (CodimensionPoint V.X p) (codimensionCycles V.X p) ℚ
    (fun x => K.nativePointImage p x)

/-- **GENUINE FINITE-CORRESPONDENCE NATIVE OPERATOR.**
First recover the exact finite point coefficients of the source native cycle,
then transport each point through the actual finite closed correspondence. -/
noncomputable def nativeCorrespondenceOperator
    (K : FiniteClosedCorrespondence V)
    (p : Nat) :
    codimensionCycles V.X p →ₗ[ℚ] codimensionCycles V.X p :=
  (correspondencePresentationOperator K p).comp
    (nativePresentationLinear V p)

/-- The global native correspondence operator really extends the original
pointwise correspondence construction. -/
theorem nativeCorrespondenceOperator_point
    (K : FiniteClosedCorrespondence V)
    (p : Nat)
    (x : CodimensionPoint V.X p) :
    nativeCorrespondenceOperator K p
      (codimensionPointCycle V.X p x) = K.nativePointImage p x := by
  rw [nativeCorrespondenceOperator, LinearMap.comp_apply,
    nativePresentationLinear_point]
  simp [correspondencePresentationOperator]

/-- Exact finite-presentation formula. -/
theorem nativeCorrespondenceOperator_realize
    (K : FiniteClosedCorrespondence V)
    (p : Nat)
    (φ : FiniteCodimensionPresentation V.X p) :
    nativeCorrespondenceOperator K p
      (realizeFiniteCodimensionPresentation V.X p φ) =
      φ.sum (fun x q => q • K.nativePointImage p x) := by
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  have hreconstruct := realize_presentationOfNativeCycle V.X p
    (realizeFiniteCodimensionPresentation V.X p φ)
  have hpresentation :
      nativePresentationLinear V p
          (realizeFiniteCodimensionPresentation V.X p φ) = φ := by
    apply Finsupp.ext
    intro x
    have hcoeff := congrArg
      (fun Z : codimensionCycles V.X p =>
        (Z.1 : AlgebraicCycle V.X ℚ) x.1) hreconstruct
    -- Both sides are the unique finite coefficient presentation of the same
    -- native cycle; point normal form makes this coefficient equality exact.
    simpa [nativePresentationLinear, presentationOfNativeCycle_apply,
      realizeFiniteCodimensionPresentation_apply] using hcoeff.symm
  rw [nativeCorrespondenceOperator, LinearMap.comp_apply, hpresentation]
  simp [correspondencePresentationOperator, Finsupp.total_apply]

#check nativePresentationLinear
#check nativePresentationLinear_point
#check correspondencePresentationOperator
#check nativeCorrespondenceOperator
#check nativeCorrespondenceOperator_point
#check nativeCorrespondenceOperator_realize

#print axioms nativePresentationLinear_point
#print axioms nativeCorrespondenceOperator_point
#print axioms nativeCorrespondenceOperator_realize

end GSTClassicalHodgeFiniteClosedCorrespondenceOperator
