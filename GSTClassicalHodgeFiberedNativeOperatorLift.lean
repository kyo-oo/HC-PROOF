import GSTClassicalHodgeFiberedNativeProjectiveTransport
import GSTClassicalHodgeProjectiveCorrespondenceAlgebra
import GSTClassicalHodgeFiberedNativePullback

/-!
# GST CLASSICAL HODGE — FIBERED NATIVE OPERATOR LIFT

The projective-correspondence algebra acts on genuine native codimension-p
cycles.  The multiplicity-preserving pullback carries an additional classical
Hodge sheet label.  This file lifts every native operator to the pullback by
acting on the genuine point coordinate and leaving the multiplicity label
untouched.

The point normal form makes this canonical: apply the native operator to a
point cycle, take its exact finite point presentation, and relabel every target
point with the same classical sheet.

The resulting lift satisfies a strict commuting square

  toNativeCycle ∘ lift(A) = A ∘ toNativeCycle.

Thus every genuine projective correspondence operator has an exact action on
the same fibered/limitless universe used by the GST multiplicity calculus.
-/

set_option maxHeartbeats 60000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open scoped BigOperators

namespace GSTClassicalHodgeFiberedNativeOperatorLift

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTNativeCodimensionCyclePresentation
open GSTCompactNativeCyclePresentation
open GSTClassicalHodgePointNormalForm
open GSTClassicalHodgeFiberedNativePullback
open GSTClassicalHodgeNativeCycleCosmicShadow
open GSTClassicalHodgeNativeTransferAddressIdentification
open GSTClassicalHodgeProjectiveCorrespondenceAlgebra

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Attach one fixed classical multiplicity label to every point of a finite
native point presentation. -/
noncomputable def labelPresentation
    (i : ClassicalHodgeBasisIndex V H p) :
    FiniteCodimensionPresentation V.X p →ₗ[ℚ]
      FiberedNativeAddress V H p where
  toFun φ := φ.sum fun x q => q • atom V H p i x
  map_add' := by intro φ ψ; classical; simp
  map_smul' := by intro q φ; classical; simp [smul_smul]

@[simp]
theorem labelPresentation_single
    (i : ClassicalHodgeBasisIndex V H p)
    (x : CodimensionPoint V.X p) (q : ℚ) :
    labelPresentation i (Finsupp.single x q) =
      q • atom V H p i x := by
  classical
  simp [labelPresentation]

/-- Forgetting the label after labelling a finite presentation realizes exactly
the original native cycle. -/
theorem toNativeCycle_labelPresentation
    (i : ClassicalHodgeBasisIndex V H p)
    (φ : FiniteCodimensionPresentation V.X p) :
    toNativeCycle V H p (labelPresentation i φ) =
      realizeFiniteCodimensionPresentation V.X p φ := by
  classical
  induction φ using Finsupp.induction_linear with
  | zero => simp [labelPresentation, toNativeCycle]
  | add f g hf hg => simp [hf, hg]
  | single x q =>
      simp [labelPresentation_single, toNativeCycle_atom,
        realizeFiniteCodimensionPresentation_single]

/-- Canonical fibrewise lift of an arbitrary native codimension-p cycle
operator. -/
noncomputable def liftNativeOperator
    (A : Module.End ℚ (codimensionCycles V.X p)) :
    Module.End ℚ (FiberedNativeAddress V H p) where
  toFun Φ := Φ.sum fun ix q =>
    q • labelPresentation ix.1
      (GSTClassicalHodgeProjectiveCorrespondenceAlgebra.operatorPointPresentation
        V p A ix.2)
  map_add' := by intro Φ Ψ; classical; simp
  map_smul' := by intro q Φ; classical; simp [smul_smul]

/-- Exact action of the lifted operator on a common-refinement atom. -/
@[simp]
theorem liftNativeOperator_atom
    (A : Module.End ℚ (codimensionCycles V.X p))
    (i : ClassicalHodgeBasisIndex V H p)
    (x : CodimensionPoint V.X p) :
    liftNativeOperator A (atom V H p i x) =
      labelPresentation i
        (GSTClassicalHodgeProjectiveCorrespondenceAlgebra.operatorPointPresentation
          V p A x) := by
  classical
  simp [liftNativeOperator, atom]

/-- **STRICT NATIVE COMMUTING SQUARE.**
For every native operator, forgetting multiplicity after the fibrewise lift is
exactly the original native operator after forgetting multiplicity. -/
theorem toNativeCycle_liftNativeOperator
    (A : Module.End ℚ (codimensionCycles V.X p))
    (Φ : FiberedNativeAddress V H p) :
    toNativeCycle V H p (liftNativeOperator A Φ) =
      A (toNativeCycle V H p Φ) := by
  classical
  induction Φ using Finsupp.induction_linear with
  | zero => simp [liftNativeOperator]
  | add f g hf hg => simp [hf, hg]
  | single ix q =>
      rw [show Finsupp.single ix q = q • atom V H p ix.1 ix.2 by
        simp [atom]]
      rw [map_smul, map_smul]
      rw [liftNativeOperator_atom]
      rw [map_smul]
      rw [toNativeCycle_labelPresentation]
      rw [GSTClassicalHodgeProjectiveCorrespondenceAlgebra.operatorPointPresentation_realize]
      rw [toNativeCycle_atom]

/-- Operator equality form of the strict commuting square. -/
theorem toNativeCycle_comp_liftNativeOperator
    (A : Module.End ℚ (codimensionCycles V.X p)) :
    (toNativeCycle V H p).comp (liftNativeOperator A) =
      A.comp (toNativeCycle V H p) := by
  apply LinearMap.ext
  intro Φ
  exact toNativeCycle_liftNativeOperator A Φ

/-- The identity native operator lifts to an operator whose native face is
identity. -/
theorem liftNativeOperator_id_nativeFace
    (Φ : FiberedNativeAddress V H p) :
    toNativeCycle V H p
        (liftNativeOperator
          (LinearMap.id : Module.End ℚ (codimensionCycles V.X p)) Φ) =
      toNativeCycle V H p Φ := by
  simpa using toNativeCycle_liftNativeOperator
    (V:=V) (H:=H) (p:=p)
    (LinearMap.id : Module.End ℚ (codimensionCycles V.X p)) Φ

/-- Composition of native operators is represented correctly after forgetting
the multiplicity fiber. -/
theorem liftNativeOperator_comp_nativeFace
    (A B : Module.End ℚ (codimensionCycles V.X p))
    (Φ : FiberedNativeAddress V H p) :
    toNativeCycle V H p
        (liftNativeOperator A (liftNativeOperator B Φ)) =
      (A.comp B) (toNativeCycle V H p Φ) := by
  rw [toNativeCycle_liftNativeOperator]
  rw [toNativeCycle_liftNativeOperator]
  rfl

/-- Rational linear combinations are represented correctly on the native face. -/
theorem liftNativeOperator_add_nativeFace
    (A B : Module.End ℚ (codimensionCycles V.X p))
    (Φ : FiberedNativeAddress V H p) :
    toNativeCycle V H p (liftNativeOperator (A+B) Φ) =
      A (toNativeCycle V H p Φ) + B (toNativeCycle V H p Φ) := by
  rw [toNativeCycle_liftNativeOperator]
  rfl

/-- Every projective-correspondence kernel therefore acts canonically on the
fibered pullback. -/
noncomputable def liftProjectiveKernel
    (K : ProjectiveNativeKernel V p) :
    Module.End ℚ (FiberedNativeAddress V H p) :=
  liftNativeOperator K.operator

/-- Native face of one lifted projective-correspondence kernel. -/
theorem toNativeCycle_liftProjectiveKernel
    (K : ProjectiveNativeKernel V p)
    (Φ : FiberedNativeAddress V H p) :
    toNativeCycle V H p (liftProjectiveKernel K Φ) =
      K.operator (toNativeCycle V H p Φ) :=
  toNativeCycle_liftNativeOperator K.operator Φ

/-- The limitless base face of a lifted native operator is exactly the cosmic
shadow of the genuine native operator output. -/
theorem limitlessFace_liftNativeOperator
    (A : Module.End ℚ (codimensionCycles V.X p))
    (Φ : FiberedNativeAddress V H p) :
    pureWeightToUniversalAddress
      (nativeCycleCosmicShadow V p
        (toNativeCycle V H p (liftNativeOperator A Φ))) =
      pureWeightToUniversalAddress
        (nativeCycleCosmicShadow V p
          (A (toNativeCycle V H p Φ))) := by
  rw [toNativeCycle_liftNativeOperator]

/-- Crown: the entire native projective operator algebra acts on the common
fibered/limitless universe with an exact native commuting square. -/
theorem fibered_native_operator_lift_crown :
    ∀ A : Module.End ℚ (codimensionCycles V.X p),
      (toNativeCycle V H p).comp (liftNativeOperator A) =
        A.comp (toNativeCycle V H p) := by
  intro A
  exact toNativeCycle_comp_liftNativeOperator A

#check labelPresentation
#check liftNativeOperator
#check liftNativeOperator_atom
#check toNativeCycle_liftNativeOperator
#check toNativeCycle_comp_liftNativeOperator
#check liftProjectiveKernel
#check limitlessFace_liftNativeOperator
#check fibered_native_operator_lift_crown

#print axioms toNativeCycle_labelPresentation
#print axioms toNativeCycle_liftNativeOperator
#print axioms toNativeCycle_comp_liftNativeOperator
#print axioms liftNativeOperator_comp_nativeFace
#print axioms toNativeCycle_liftProjectiveKernel
#print axioms fibered_native_operator_lift_crown

end GSTClassicalHodgeFiberedNativeOperatorLift
