import GSTClassicalHodgeAtomicDefectEquivariantIrreducibility
import GSTClassicalHodgeTwoSlotLefschetzPoincareGeneration
import GSTClassicalHodgeTwoGeneratorPointKernelSaturation

/-!
# GST CLASSICAL HODGE — ATOMIC-NATURAL LEFSCHETZ–POINCARE CLOSURE

The atomic-defect equivariance layer reduced the classical landing to an
independently geometric ambient realization of the rank-free GST matrix-unit
arsenal.  This file compresses that obligation to the two primitive operators
already intrinsic to the GST cosmology:

* the two-step Lefschetz motion `L²`;
* Poincare reversal `P`.

The finite two-slot identity already proved in the cosmology is

  D = (1/2) L² P,

where `D = diag(0,1)` is the target-sheet code observable.  Hence source and
target projectors, and then the normalized rank-one transfer word, are all
built from `L²`, `P`, identity, rational scaling, addition and composition.
The preceding `AtomicNaturalHodgeOperator` algebra proves that all of those
constructions preserve the genuine atomic cycle-class span whenever the two
primitive ambient operators do.

A subtle point is handled explicitly: the two-slot read/write chart is a true
conjugation only for DISTINCT global basis indices.  For distinct `i,j` we
prove the chart composition law and derive the exact matrix unit `E_ij` from
atomic-natural Lefschetz and Poincare.  Diagonal matrix units are then obtained
by composing opposite off-diagonal transfers.  If the Hodge basis has only one
index, the identity operator already is its unique diagonal matrix unit.

Thus the final operator-theoretic frontier is reduced from arbitrary matrix
units, projectors, or code observables to independently constructed
atomic-natural Lefschetz and Poincare primitives on each genuine two-sheet
chart.  No cycle representative for the target Hodge sheet is assumed.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeAtomicNaturalLefschetzPoincareClosure

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeFullArsenalIrreducibility
open GSTClassicalHodgeExplicitArsenalGeneration
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeRankFreePrimitiveGeneration
open GSTClassicalHodgeUniversalTwoSlotNativeClosure
open GSTClassicalHodgeTwoGeneratorNativeArsenal
open GSTClassicalHodgeTwoGeneratorPointKernelSaturation
open GSTClassicalHodgeTwoSlotLefschetzPoincareGeneration
open GSTClassicalHodgeAtomicDefectEquivariantIrreducibility

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

abbrev HFiber := ClassicalHodgeFiber V H p
abbrev AtomicOp := AtomicNaturalHodgeOperator V H p

/-- A distinct ordered pair gives an injective genuine two-slot basis chart. -/
theorem pairBasisIndex_injective_of_ne
    (i j : ClassicalHodgeBasisIndex V H p)
    (hij : i ≠ j) :
    Function.Injective (pairBasisIndex i j) := by
  intro r s hrs
  fin_cases r <;> fin_cases s <;> simp_all [pairBasisIndex]

/-- Reading after writing an injectively selected finite Hodge window is the
identity on that finite GST window. -/
theorem finiteHodgeRead_write_of_injective
    {N : Nat}
    (e : Fin N → ClassicalHodgeBasisIndex V H p)
    (he : Function.Injective e)
    (a : RationalPureWindow N) :
    finiteHodgeRead e (finiteHodgeWrite e a) = a := by
  funext r
  change hodgeCoordinate (e r)
      (∑ s : Fin N, a s • classicalHodgeBasis V H p (e s)) = a r
  rw [map_sum]
  simp only [map_smul]
  rw [Finset.sum_eq_single r]
  · simp
  · intro s _ hsr
    have hers : e r ≠ e s := by
      intro h
      exact hsr (he h)
    simp [hodgeCoordinate_basis_other _ _ hers]
  · simp

/-- On an injective finite Hodge chart, lifting respects composition exactly. -/
theorem liftFiniteHodgeOperator_comp_of_injective
    {N : Nat}
    (e : Fin N → ClassicalHodgeBasisIndex V H p)
    (he : Function.Injective e)
    (A B : Module.End ℚ (RationalPureWindow N)) :
    liftFiniteHodgeOperator e (A.comp B) =
      (liftFiniteHodgeOperator e A).comp
        (liftFiniteHodgeOperator e B) := by
  apply LinearMap.ext
  intro alpha
  simp only [liftFiniteHodgeOperator, LinearMap.comp_apply]
  rw [finiteHodgeRead_write_of_injective e he]

/-- Lifting commutes with rational scaling. -/
theorem liftFiniteHodgeOperator_smul
    {N : Nat}
    (e : Fin N → ClassicalHodgeBasisIndex V H p)
    (q : ℚ)
    (A : Module.End ℚ (RationalPureWindow N)) :
    liftFiniteHodgeOperator e (q • A) =
      q • liftFiniteHodgeOperator e A := by
  apply LinearMap.ext
  intro alpha
  simp [liftFiniteHodgeOperator]

/-- The pure Hodge-fiber normalized code/Lefschetz word. -/
noncomputable def twoGeneratorHodgeWord
    (i j : ClassicalHodgeBasisIndex V H p) :
    Module.End ℚ (HFiber (V := V) (H := H) p) :=
  (forwardScalar sourceSlot targetSlot : ℚ)⁻¹ •
    ((twoSlotCodeHodge i j).comp
      ((twoSlotHodgeOperator i j (diagonalLefschetzQ 2 2)).comp
        (LinearMap.id - twoSlotCodeHodge i j)))

/-- The Hodge-fiber word is exactly the rank-free matrix unit. -/
theorem twoGeneratorHodgeWord_eq_matrixUnit
    (i j : ClassicalHodgeBasisIndex V H p) :
    twoGeneratorHodgeWord i j = hodgeMatrixUnit i j := by
  apply LinearMap.ext
  intro alpha
  apply Subtype.ext
  let src : HFiber (V := V) (H := H) p :=
    (LinearMap.id - twoSlotCodeHodge i j) alpha
  let mid : HFiber (V := V) (H := H) p :=
    twoSlotHodgeOperator i j (diagonalLefschetzQ 2 2) src
  have hambient := twoGeneratorAmbientWord_on_hodge i j alpha
  have hcode0 := extendHodgeEndomorphism_on_hodge
    (V := V) (H := H) (twoSlotCodeHodge i j) alpha
  have hsrc :
      (LinearMap.id - ambientTwoSlotCode i j) alpha.1 = src.1 := by
    simp only [LinearMap.sub_apply, LinearMap.id_apply]
    rw [hcode0]
    rfl
  have hL := extendHodgeEndomorphism_on_hodge
    (V := V) (H := H)
    (twoSlotHodgeOperator i j (diagonalLefschetzQ 2 2)) src
  have htgt := extendHodgeEndomorphism_on_hodge
    (V := V) (H := H) (twoSlotCodeHodge i j) mid
  unfold twoGeneratorAmbientWord at hambient
  unfold twoGeneratorHodgeWord
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [hsrc, hL, htgt] at hambient
  exact hambient

/-- The two independently geometric primitive actions needed on one distinct
ordered Hodge pair.  Only atomic naturality plus exact primitive Hodge actions
are stored. -/
structure AtomicNaturalLefschetzPoincarePair
    (i j : ClassicalHodgeBasisIndex V H p)
    (hij : i ≠ j) where
  lefschetz : AtomicOp (V := V) (H := H) (p := p)
  poincare : AtomicOp (V := V) (H := H) (p := p)
  lefschetz_hodge :
    lefschetz.hodge =
      twoSlotHodgeOperator i j (diagonalLefschetzQ 2 2)
  poincare_hodge :
    poincare.hodge =
      twoSlotHodgeOperator i j (poincareReverseQ 2).toLinearMap

namespace AtomicNaturalLefschetzPoincarePair

/-- Derive the target-sheet code from the genuine primitive pair using
`D = (1/2)L²P`. -/
noncomputable def code
    {i j : ClassicalHodgeBasisIndex V H p}
    {hij : i ≠ j}
    (R : AtomicNaturalLefschetzPoincarePair (V := V) (H := H) i j hij) :
    AtomicOp (V := V) (H := H) (p := p) :=
  AtomicNaturalHodgeOperator.smul (2 : ℚ)⁻¹
    (R.lefschetz.comp R.poincare)

/-- On a distinct two-slot chart, the derived primitive composite has exactly
the canonical GST code action on the Hodge fiber. -/
theorem code_hodge
    {i j : ClassicalHodgeBasisIndex V H p}
    {hij : i ≠ j}
    (R : AtomicNaturalLefschetzPoincarePair (V := V) (H := H) i j hij) :
    R.code.hodge = twoSlotCodeHodge i j := by
  unfold code AtomicNaturalHodgeOperator.smul AtomicNaturalHodgeOperator.comp
  change (2 : ℚ)⁻¹ • (R.lefschetz.hodge.comp R.poincare.hodge) =
    twoSlotCodeHodge i j
  rw [R.lefschetz_hodge, R.poincare_hodge]
  rw [← liftFiniteHodgeOperator_comp_of_injective
    (pairBasisIndex i j) (pairBasisIndex_injective_of_ne i j hij)]
  rw [← liftFiniteHodgeOperator_smul]
  exact (twoSlotCodeHodge_eq_lift_half_lefschetz_comp_poincare i j).symm

/-- Source projector `I-D`, still atomic-natural because the operator algebra
is closed under linear combinations. -/
noncomputable def sourceProjector
    {i j : ClassicalHodgeBasisIndex V H p}
    {hij : i ≠ j}
    (R : AtomicNaturalLefschetzPoincarePair (V := V) (H := H) i j hij) :
    AtomicOp (V := V) (H := H) (p := p) :=
  AtomicNaturalHodgeOperator.id.add
    (AtomicNaturalHodgeOperator.smul (-1 : ℚ) R.code)

/-- Target projector is the derived code itself. -/
noncomputable def targetProjector
    {i j : ClassicalHodgeBasisIndex V H p}
    {hij : i ≠ j}
    (R : AtomicNaturalLefschetzPoincarePair (V := V) (H := H) i j hij) :
    AtomicOp (V := V) (H := H) (p := p) :=
  R.code

/-- Exact normalized two-slot transfer built solely from the two primitive
atomic-natural actions. -/
noncomputable def matrixWord
    {i j : ClassicalHodgeBasisIndex V H p}
    {hij : i ≠ j}
    (R : AtomicNaturalLefschetzPoincarePair (V := V) (H := H) i j hij) :
    AtomicOp (V := V) (H := H) (p := p) :=
  AtomicNaturalHodgeOperator.smul
    (forwardScalar sourceSlot targetSlot : ℚ)⁻¹
    (R.targetProjector.comp
      (R.lefschetz.comp R.sourceProjector))

/-- The derived word is exactly the global rank-free matrix unit on its Hodge
restriction. -/
theorem matrixWord_hodge
    {i j : ClassicalHodgeBasisIndex V H p}
    {hij : i ≠ j}
    (R : AtomicNaturalLefschetzPoincarePair (V := V) (H := H) i j hij) :
    R.matrixWord.hodge = hodgeMatrixUnit i j := by
  rw [← twoGeneratorHodgeWord_eq_matrixUnit i j]
  unfold matrixWord targetProjector sourceProjector
  unfold AtomicNaturalHodgeOperator.smul
    AtomicNaturalHodgeOperator.comp AtomicNaturalHodgeOperator.add
    AtomicNaturalHodgeOperator.id
  rw [R.code_hodge, R.lefschetz_hodge]
  rfl

end AtomicNaturalLefschetzPoincarePair

/-- Opposite off-diagonal matrix units compose to the corresponding diagonal
matrix unit. -/
theorem hodgeMatrixUnit_opposite_comp
    (i k : ClassicalHodgeBasisIndex V H p)
    (hik : i ≠ k) :
    (hodgeMatrixUnit k i).comp (hodgeMatrixUnit i k) =
      hodgeMatrixUnit i i := by
  apply LinearMap.ext
  intro alpha
  simp [hodgeMatrixUnit_apply, hodgeCoordinate, hik]

/-- If one basis index is the only index, its diagonal matrix unit is identity. -/
theorem hodgeMatrixUnit_self_eq_id_of_unique
    (i : ClassicalHodgeBasisIndex V H p)
    (hunique : ∀ k : ClassicalHodgeBasisIndex V H p, k = i) :
    hodgeMatrixUnit i i = LinearMap.id := by
  apply LinearMap.ext
  intro alpha
  apply (classicalHodgeBasis V H p).repr.injective
  apply Finsupp.ext
  intro k
  have hki : k = i := hunique k
  subst k
  simp [hodgeMatrixUnit_apply, hodgeCoordinate]

/-- A family of atomic-natural Lefschetz/Poincare primitive realizations for
every DISTINCT ordered pair compiles to the complete matrix-unit arsenal.
Diagonal units use opposite transfers when another sheet exists, and identity
in the singleton case. -/
noncomputable def atomicNaturalMatrixArsenal_of_lefschetzPoincare
    (R : ∀ i j : ClassicalHodgeBasisIndex V H p,
      i ≠ j → AtomicNaturalLefschetzPoincarePair
        (V := V) (H := H) i j ‹i ≠ j›) :
    AtomicNaturalMatrixArsenal V H p where
  realize := fun i j => by
    by_cases hij : i ≠ j
    · exact (R i j hij).matrixWord
    · subst j
      by_cases hex : ∃ k : ClassicalHodgeBasisIndex V H p, k ≠ i
      · let k := Classical.choose hex
        have hki : k ≠ i := Classical.choose_spec hex
        have hik : i ≠ k := Ne.symm hki
        exact (R k i hki).matrixWord.comp (R i k hik).matrixWord
      · exact AtomicNaturalHodgeOperator.id
  hodge_action := by
    intro i j
    by_cases hij : i ≠ j
    · simp only [dif_pos hij]
      exact (R i j hij).matrixWord_hodge
    · subst j
      by_cases hex : ∃ k : ClassicalHodgeBasisIndex V H p, k ≠ i
      · simp only [dif_neg rfl, dif_pos hex]
        let k := Classical.choose hex
        have hki : k ≠ i := Classical.choose_spec hex
        have hik : i ≠ k := Ne.symm hki
        change ((R k i hki).matrixWord.hodge.comp
          (R i k hik).matrixWord.hodge) = hodgeMatrixUnit i i
        rw [(R k i hki).matrixWord_hodge, (R i k hik).matrixWord_hodge]
        exact hodgeMatrixUnit_opposite_comp i k hik
      · simp only [dif_neg rfl, dif_neg hex]
        have hunique : ∀ k : ClassicalHodgeBasisIndex V H p, k = i := by
          intro k
          by_contra hki
          exact hex ⟨k, hki⟩
        exact (hodgeMatrixUnit_self_eq_id_of_unique i hunique).symm

/-- **LEFSCHETZ–POINCARE DEFECT EXTINCTION, FIXED WEIGHT.**
One nonzero algebraic seed plus atomic-natural realizations of the two genuine
GST primitives on every distinct local pair kills the entire atomic defect in
that weight. -/
theorem atomicDefect_eq_zero_of_lefschetzPoincare
    (hseed : AlgebraicHodgeSubspace V H p ≠ ⊥)
    (R : ∀ i j : ClassicalHodgeBasisIndex V H p,
      i ≠ j → AtomicNaturalLefschetzPoincarePair
        (V := V) (H := H) i j ‹i ≠ j›) :
    atomicDefectLinearMap V H p = 0 := by
  exact (atomicNaturalMatrixArsenal_of_lefschetzPoincare R).atomicDefect_eq_zero
    hseed

/-- **RANK-FREE LEFSCHETZ–POINCARE HODGE CROWN.**
At every nontrivial weight, a nonzero algebraic seed and independently
constructed atomic-natural Lefschetz/Poincare primitives on distinct two-sheet
charts imply the complete Stage-2G Hodge statement. -/
theorem bigradedBettiHodge_of_atomicNaturalLefschetzPoincare
    (R : ∀ q : Nat,
      rationalHodgeSubspace (H.hodgeBigrading q) ≠ ⊥ →
      ∀ i j : ClassicalHodgeBasisIndex V H q,
        i ≠ j → AtomicNaturalLefschetzPoincarePair
          (V := V) (H := H) i j ‹i ≠ j›)
    (hseed : ∀ q : Nat,
      rationalHodgeSubspace (H.hodgeBigrading q) ≠ ⊥ →
        AlgebraicHodgeSubspace V H q ≠ ⊥) :
    BigradedBettiHodgeStatement V H := by
  exact bigradedBettiHodge_of_atomicNaturalMatrixArsenal
    (fun q hq => atomicNaturalMatrixArsenal_of_lefschetzPoincare (R q hq))
    hseed

#check pairBasisIndex_injective_of_ne
#check finiteHodgeRead_write_of_injective
#check liftFiniteHodgeOperator_comp_of_injective
#check liftFiniteHodgeOperator_smul
#check twoGeneratorHodgeWord
#check twoGeneratorHodgeWord_eq_matrixUnit
#check AtomicNaturalLefschetzPoincarePair
#check AtomicNaturalLefschetzPoincarePair.code
#check AtomicNaturalLefschetzPoincarePair.code_hodge
#check AtomicNaturalLefschetzPoincarePair.sourceProjector
#check AtomicNaturalLefschetzPoincarePair.matrixWord
#check AtomicNaturalLefschetzPoincarePair.matrixWord_hodge
#check hodgeMatrixUnit_opposite_comp
#check hodgeMatrixUnit_self_eq_id_of_unique
#check atomicNaturalMatrixArsenal_of_lefschetzPoincare
#check atomicDefect_eq_zero_of_lefschetzPoincare
#check bigradedBettiHodge_of_atomicNaturalLefschetzPoincare

#print axioms finiteHodgeRead_write_of_injective
#print axioms liftFiniteHodgeOperator_comp_of_injective
#print axioms AtomicNaturalLefschetzPoincarePair.code_hodge
#print axioms AtomicNaturalLefschetzPoincarePair.matrixWord_hodge
#print axioms atomicNaturalMatrixArsenal_of_lefschetzPoincare
#print axioms atomicDefect_eq_zero_of_lefschetzPoincare
#print axioms bigradedBettiHodge_of_atomicNaturalLefschetzPoincare

end GSTClassicalHodgeAtomicNaturalLefschetzPoincareClosure
