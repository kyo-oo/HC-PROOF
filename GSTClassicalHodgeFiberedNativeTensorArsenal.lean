import GSTClassicalHodgeFiberedNativeOperatorLift
import GSTClassicalHodgeLimitlessCosmicMatrixUnits
import GSTClassicalHodgeRankFreeArsenalIrreducibility

/-!
# GST CLASSICAL HODGE — FIBERED NATIVE TENSOR ARSENAL

The common-refinement universe has two genuinely independent coordinates:

* a classical Hodge multiplicity label `i`;
* a genuine codimension-p projective point `x`.

The full operator algebra therefore has two commuting factors.

1. **Multiplicity matrix units** read one Hodge-fiber label and rewrite it as
   another label while leaving the native point untouched.
2. **Native correspondence operators** act on the projective point/cycle
   coordinate through exact finite point normal form while leaving the Hodge
   label untouched.

These factors commute on every atom and hence on every finite state.  The
result is the natural tensor-product architecture demanded by arbitrary Hodge
multiplicity: limitless GST sheet algebra on one axis, genuine projective
correspondence algebra on the other.
-/

set_option maxHeartbeats 60000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open scoped BigOperators

namespace GSTClassicalHodgeFiberedNativeTensorArsenal

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeFiberedNativePullback
open GSTClassicalHodgeFiberedNativeOperatorLift
open GSTClassicalHodgeNativeCycleCosmicShadow
open GSTClassicalHodgeNativeTransferAddressIdentification
open GSTClassicalHodgeRankFreeArsenalIrreducibility

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Matrix unit on the fixed-weight multiplicity coordinate of the pullback.
It leaves every genuine native point untouched. -/
noncomputable def multiplicityMatrixUnit
    (i j : ClassicalHodgeBasisIndex V H p) :
    Module.End ℚ (FiberedNativeAddress V H p) where
  toFun Φ := Φ.sum fun kx q =>
    if kx.1 = i then q • atom V H p j kx.2 else 0
  map_add' := by intro Φ Ψ; classical; simp
  map_smul' := by intro q Φ; classical; simp [smul_smul]

@[simp]
theorem multiplicityMatrixUnit_atom_source
    (i j : ClassicalHodgeBasisIndex V H p)
    (x : CodimensionPoint V.X p) :
    multiplicityMatrixUnit i j (atom V H p i x) =
      atom V H p j x := by
  classical
  simp [multiplicityMatrixUnit, atom]

@[simp]
theorem multiplicityMatrixUnit_atom_other
    (i j k : ClassicalHodgeBasisIndex V H p)
    (hki : k ≠ i)
    (x : CodimensionPoint V.X p) :
    multiplicityMatrixUnit i j (atom V H p k x) = 0 := by
  classical
  simp [multiplicityMatrixUnit, atom, hki]

/-- Fixed-weight coordinate matrix unit on the pure classical multiplicity
address `i ->₀ Q`. -/
noncomputable def multiplicityAddressMatrixUnit
    (i j : ClassicalHodgeBasisIndex V H p) :
    Module.End ℚ (ClassicalHodgeBasisIndex V H p →₀ ℚ) where
  toFun a := Finsupp.single j (a i)
  map_add' := by intro a b; ext k; simp
  map_smul' := by intro q a; ext k; simp

/-- Forgetting the native point intertwines the pullback matrix unit with the
ordinary matrix unit on Hodge multiplicity coordinates. -/
theorem forgetPoint_multiplicityMatrixUnit
    (i j : ClassicalHodgeBasisIndex V H p)
    (Φ : FiberedNativeAddress V H p) :
    forgetPoint V H p (multiplicityMatrixUnit i j Φ) =
      multiplicityAddressMatrixUnit i j (forgetPoint V H p Φ) := by
  classical
  induction Φ using Finsupp.induction_linear with
  | zero => simp [multiplicityMatrixUnit, multiplicityAddressMatrixUnit]
  | add f g hf hg => simp [hf, hg]
  | single kx q =>
      by_cases hki : kx.1 = i
      · subst kx.1
        simp [multiplicityMatrixUnit, multiplicityAddressMatrixUnit,
          forgetPoint, atom]
      · simp [multiplicityMatrixUnit, multiplicityAddressMatrixUnit,
          forgetPoint, atom, hki]

/-- Pullback multiplicity matrix units satisfy the exact matrix-unit
composition law. -/
theorem multiplicityMatrixUnit_comp
    (i j k : ClassicalHodgeBasisIndex V H p) :
    (multiplicityMatrixUnit j k).comp (multiplicityMatrixUnit i j) =
      multiplicityMatrixUnit i k := by
  apply LinearMap.ext
  intro Φ
  classical
  induction Φ using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg]
  | single lx q =>
      by_cases hli : lx.1 = i
      · subst lx.1
        simp [multiplicityMatrixUnit, atom]
      · simp [multiplicityMatrixUnit, atom, hli]

/-- Mismatched intermediate labels annihilate exactly. -/
theorem multiplicityMatrixUnit_comp_zero
    (i j k l : ClassicalHodgeBasisIndex V H p)
    (hjk : j ≠ k) :
    (multiplicityMatrixUnit k l).comp (multiplicityMatrixUnit i j) = 0 := by
  apply LinearMap.ext
  intro Φ
  classical
  induction Φ using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg]
  | single mx q =>
      by_cases hmi : mx.1 = i
      · subst mx.1
        simp [multiplicityMatrixUnit, atom, hjk]
      · simp [multiplicityMatrixUnit, atom, hmi]

/-- The diagonal matrix unit is the exact multiplicity projector. -/
def multiplicityProjector
    (i : ClassicalHodgeBasisIndex V H p) :
    Module.End ℚ (FiberedNativeAddress V H p) :=
  multiplicityMatrixUnit i i

@[simp]
theorem multiplicityProjector_atom_self
    (i : ClassicalHodgeBasisIndex V H p)
    (x : CodimensionPoint V.X p) :
    multiplicityProjector i (atom V H p i x) = atom V H p i x := by
  simp [multiplicityProjector]

@[simp]
theorem multiplicityProjector_atom_other
    (i k : ClassicalHodgeBasisIndex V H p)
    (hki : k ≠ i)
    (x : CodimensionPoint V.X p) :
    multiplicityProjector i (atom V H p k x) = 0 := by
  simp [multiplicityProjector, multiplicityMatrixUnit_atom_other, hki]

/-- **TENSOR COMMUTATION LAW.**
Multiplicity matrix units and arbitrary lifted native cycle operators commute
exactly because they act on independent coordinates of the common pullback. -/
theorem multiplicityMatrixUnit_commutes_liftNativeOperator
    (i j : ClassicalHodgeBasisIndex V H p)
    (A : Module.End ℚ (codimensionCycles V.X p)) :
    (multiplicityMatrixUnit i j).comp (liftNativeOperator A) =
      (liftNativeOperator A).comp (multiplicityMatrixUnit i j) := by
  apply LinearMap.ext
  intro Φ
  classical
  induction Φ using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg]
  | single kx q =>
      rw [show Finsupp.single kx q = q • atom V H p kx.1 kx.2 by simp [atom]]
      rw [map_smul, map_smul, map_smul, map_smul]
      rw [liftNativeOperator_atom]
      by_cases hki : kx.1 = i
      · subst kx.1
        simp [labelPresentation, multiplicityMatrixUnit, atom]
      · simp [labelPresentation, multiplicityMatrixUnit, atom, hki]

/-- Consequently every multiplicity matrix unit commutes with every actual
projective-correspondence kernel lifted to the pullback. -/
theorem multiplicityMatrixUnit_commutes_projectiveKernel
    (i j : ClassicalHodgeBasisIndex V H p)
    (K : GSTClassicalHodgeProjectiveCorrespondenceAlgebra.ProjectiveNativeKernel V p) :
    (multiplicityMatrixUnit i j).comp (liftProjectiveKernel K) =
      (liftProjectiveKernel K).comp (multiplicityMatrixUnit i j) :=
  multiplicityMatrixUnit_commutes_liftNativeOperator i j K.operator

/-- Tensor word: first apply one genuine native operator, then one unrestricted
Hodge multiplicity matrix unit.  By commutation the order is irrelevant. -/
noncomputable def tensorWord
    (i j : ClassicalHodgeBasisIndex V H p)
    (A : Module.End ℚ (codimensionCycles V.X p)) :
    Module.End ℚ (FiberedNativeAddress V H p) :=
  (multiplicityMatrixUnit i j).comp (liftNativeOperator A)

/-- Exact tensor-word action on an atom in the source multiplicity sheet. -/
theorem tensorWord_atom_source
    (i j : ClassicalHodgeBasisIndex V H p)
    (A : Module.End ℚ (codimensionCycles V.X p))
    (x : CodimensionPoint V.X p) :
    tensorWord i j A (atom V H p i x) =
      labelPresentation j
        (GSTClassicalHodgeProjectiveCorrespondenceAlgebra.operatorPointPresentation
          V p A x) := by
  simp [tensorWord, liftNativeOperator_atom,
    multiplicityMatrixUnit, labelPresentation, atom]

/-- Native face of a tensor word is the native operator applied to the selected
source multiplicity slice. -/
theorem tensorWord_nativeFace_atom_source
    (i j : ClassicalHodgeBasisIndex V H p)
    (A : Module.End ℚ (codimensionCycles V.X p))
    (x : CodimensionPoint V.X p) :
    toNativeCycle V H p (tensorWord i j A (atom V H p i x)) =
      A (codimensionPointCycle V.X p x) := by
  rw [tensorWord_atom_source]
  rw [toNativeCycle_labelPresentation]
  exact GSTClassicalHodgeProjectiveCorrespondenceAlgebra.operatorPointPresentation_realize
    V p A x

/-- Multiplicity face of the same tensor word lands entirely in the target
classical sheet j. -/
theorem tensorWord_hodgeFace_supported_at_target
    (i j : ClassicalHodgeBasisIndex V H p)
    (A : Module.End ℚ (codimensionCycles V.X p))
    (x : CodimensionPoint V.X p) :
    ∃ q : ℚ,
      toGlobalHodgeAddress V H p (tensorWord i j A (atom V H p i x)) =
        q • fiberedSheetGenerator V H ⟨p,j⟩ := by
  refine ⟨GSTClassicalHodgeNativeCycleCosmicShadow.presentationMass
      (GSTClassicalHodgeProjectiveCorrespondenceAlgebra.operatorPointPresentation
        V p A x), ?_⟩
  rw [tensorWord_atom_source]
  classical
  unfold labelPresentation toGlobalHodgeAddress forgetPoint
  ext s
  simp [fiberedSheetGenerator,
    GSTClassicalHodgeNativeCycleCosmicShadow.presentationMass,
    weightFiberEmbedding, smul_eq_mul]

/-- **FIBERED NATIVE TENSOR-ARSENAL CROWN.**
The unrestricted classical multiplicity matrix-unit algebra and the genuine
native projective operator algebra act as two commuting factors on one common
limitless pullback universe. -/
theorem fibered_native_tensor_arsenal_crown :
    (∀ i j k : ClassicalHodgeBasisIndex V H p,
      (multiplicityMatrixUnit j k).comp (multiplicityMatrixUnit i j) =
        multiplicityMatrixUnit i k)
    ∧ (∀ i j A,
      (multiplicityMatrixUnit i j).comp (liftNativeOperator A) =
        (liftNativeOperator A).comp (multiplicityMatrixUnit i j)) := by
  exact ⟨multiplicityMatrixUnit_comp,
    multiplicityMatrixUnit_commutes_liftNativeOperator⟩

#check multiplicityMatrixUnit
#check multiplicityAddressMatrixUnit
#check forgetPoint_multiplicityMatrixUnit
#check multiplicityMatrixUnit_comp
#check multiplicityMatrixUnit_commutes_liftNativeOperator
#check tensorWord
#check tensorWord_atom_source
#check tensorWord_nativeFace_atom_source
#check fibered_native_tensor_arsenal_crown

#print axioms forgetPoint_multiplicityMatrixUnit
#print axioms multiplicityMatrixUnit_comp
#print axioms multiplicityMatrixUnit_commutes_liftNativeOperator
#print axioms tensorWord_atom_source
#print axioms tensorWord_nativeFace_atom_source
#print axioms fibered_native_tensor_arsenal_crown

end GSTClassicalHodgeFiberedNativeTensorArsenal
