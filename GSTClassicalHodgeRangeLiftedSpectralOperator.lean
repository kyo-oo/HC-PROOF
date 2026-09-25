import Mathlib.Algebra.Module.Projective
import GSTClassicalHodgeConstructiveCyclicLanding

/-!
# GST CLASSICAL HODGE — RANGE-LIFTED SPECTRAL OPERATORS

The classical cyclic engine does not need a separately postulated operator on
native algebraic cycles.

For a rational linear cycle-class map `cl : Cycles → Coh`, its range is a
rational vector space and therefore a projective module.  Hence the canonical
surjection `Cycles → range(cl)` admits a rational linear section.  Every
cohomology endomorphism preserving `range(cl)` can consequently be lifted to
an endomorphism of native cycles, with an exact commuting cycle-class square.

On a smooth projective carrier the repo already identifies the native
cycle-class range with the atomic point-cycle span.  Therefore the
`atomic_stable` field of `ClassicalHodgeSpectralOperator` is precisely enough
to manufacture the native cycle operator required by
`SpectralCycleOperator`.

As a consequence, every existing `LocalCyclicRealization` upgrades
constructively to `LocalCycleSpectralRealization`: the single atomic seed is
lifted to one native seed cycle, the spectral operator is lifted through the
cycle-class range, and Lagrange functional calculus constructs the individual
native basis cycles.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeCyclicSpectralGeneration
open GSTClassicalHodgeLocalCyclicCriterion
open GSTClassicalHodgeCycleOperatorNaturality
open GSTClassicalHodgeConstructiveCyclicLanding

namespace GSTClassicalHodgeRangeLiftedSpectralOperator

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Canonical-choice rational linear section of the cycle-class map onto its
actual range.  The existence is pure projectivity of rational vector spaces. -/
noncomputable def cycleClassRangeSection
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) :
    LinearMap.range (H.cycleClass p) →ₗ[ℚ] codimensionCycles V.X p :=
  Classical.choose
    ((H.cycleClass p).rangeRestrict.exists_rightInverse_of_surjective
      (H.cycleClass p).range_rangeRestrict)

/-- The chosen range section is an exact right inverse of the native
cycle-class map restricted to its range. -/
theorem cycleClassRangeSection_spec
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) :
    (H.cycleClass p).rangeRestrict ∘ₗ cycleClassRangeSection V H p =
      LinearMap.id := by
  exact Classical.choose_spec
    ((H.cycleClass p).rangeRestrict.exists_rightInverse_of_surjective
      (H.cycleClass p).range_rangeRestrict)

/-- Restrict a cohomology operator to the native cycle-class range once that
range is invariant. -/
noncomputable def rangeStableRestriction
    (T : RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
      RationalSingularCohomology H.analytification (2 * p))
    (hstable : ∀ x,
      x ∈ LinearMap.range (H.cycleClass p) →
        T x ∈ LinearMap.range (H.cycleClass p)) :
    LinearMap.range (H.cycleClass p) →ₗ[ℚ]
      LinearMap.range (H.cycleClass p) where
  toFun := fun x => ⟨T x.1, hstable x.1 x.2⟩
  map_add' := by
    intro x y
    ext
    simp
  map_smul' := by
    intro q x
    ext
    simp

/-- Lift a range-preserving cohomological operator to native algebraic cycles
through the projective section of the cycle-class range. -/
noncomputable def liftedCycleOperator
    (T : RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
      RationalSingularCohomology H.analytification (2 * p))
    (hstable : ∀ x,
      x ∈ LinearMap.range (H.cycleClass p) →
        T x ∈ LinearMap.range (H.cycleClass p)) :
    codimensionCycles V.X p →ₗ[ℚ] codimensionCycles V.X p :=
  (cycleClassRangeSection V H p).comp
    ((rangeStableRestriction T hstable).comp
      (H.cycleClass p).rangeRestrict)

/-- **RANGE-LIFT NATURALITY.**  The manufactured native cycle operator has
exactly the prescribed cohomological action after applying cycle class. -/
theorem cycleClass_liftedCycleOperator
    (T : RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
      RationalSingularCohomology H.analytification (2 * p))
    (hstable : ∀ x,
      x ∈ LinearMap.range (H.cycleClass p) →
        T x ∈ LinearMap.range (H.cycleClass p))
    (Z : codimensionCycles V.X p) :
    H.cycleClass p (liftedCycleOperator T hstable Z) =
      T (H.cycleClass p Z) := by
  let y : LinearMap.range (H.cycleClass p) :=
    rangeStableRestriction T hstable ((H.cycleClass p).rangeRestrict Z)
  have hsec := LinearMap.congr_fun
    (cycleClassRangeSection_spec V H p) y
  have hval := congrArg Subtype.val hsec
  simpa [liftedCycleOperator, y, rangeStableRestriction] using hval

/-- Any range-preserving cohomology operator therefore determines a complete
native/cohomological operator pair. -/
noncomputable def CycleClassOperatorPair.ofRangeStable
    (T : RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
      RationalSingularCohomology H.analytification (2 * p))
    (hstable : ∀ x,
      x ∈ LinearMap.range (H.cycleClass p) →
        T x ∈ LinearMap.range (H.cycleClass p)) :
    CycleClassOperatorPair V H p where
  cycleOperator := liftedCycleOperator T hstable
  cohomologyOperator := T
  cycleClass_natural := by
    ext Z
    exact cycleClass_liftedCycleOperator T hstable Z

/-- On a smooth projective scheme, atomic-span stability is the same range
stability needed by the range-lift theorem. -/
theorem ClassicalHodgeSpectralOperator.cycleClassRange_stable
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : ClassicalHodgeSpectralOperator V H p ι) :
    ∀ x,
      x ∈ LinearMap.range (H.cycleClass p) →
        S.observable x ∈ LinearMap.range (H.cycleClass p) := by
  intro x hx
  have hxAtomic :
      x ∈ pointCycleClassSpan p (H.cycleClass p) := by
    rwa [← smoothProjective_cycleClass_range_eq_atomic_span V H p]
  have hTxAtomic := S.atomic_stable x hxAtomic
  rwa [← smoothProjective_cycleClass_range_eq_atomic_span V H p] at hTxAtomic

/-- **AUTOMATIC NATIVE SPECTRAL LIFT.**  Every classical Hodge spectral
operator already carries enough information to become a native spectral cycle
operator; no independent native operator datum is required. -/
noncomputable def ClassicalHodgeSpectralOperator.toSpectralCycleOperatorViaRange
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : ClassicalHodgeSpectralOperator V H p ι) :
    SpectralCycleOperator V H p ι where
  operatorPair := CycleClassOperatorPair.ofRangeStable
    S.observable S.cycleClassRange_stable
  basisIndex := S.basisIndex
  basisIndex_injective := S.basisIndex_injective
  eigenvalue := S.eigenvalue
  eigenvalue_injective := S.eigenvalue_injective
  eigenvector := S.eigenvector

/-- The automatically lifted spectral operator preserves the original selected
basis indexing exactly. -/
@[simp]
theorem ClassicalHodgeSpectralOperator.toSpectralCycleOperatorViaRange_basisIndex
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : ClassicalHodgeSpectralOperator V H p ι) :
    S.toSpectralCycleOperatorViaRange.basisIndex = S.basisIndex :=
  rfl

/-- **LOCAL CYCLIC → CONSTRUCTIVE NATIVE UPGRADE.**

A local cyclic realization already contains every mathematical ingredient
needed for explicit native cycle construction.  Its atomic seed belongs to
the actual cycle-class range, so choose one native seed cycle representing it;
its atomic-stable spectral observable automatically lifts to native cycles by
the range-lift theorem above. -/
noncomputable def LocalCyclicRealization.toLocalCycleSpectralRealization
    {alpha : ClassicalHodgeFiber V H p}
    (R : LocalCyclicRealization V H p alpha) :
    LocalCycleSpectralRealization V H p alpha := by
  let S := R.spectral.toSpectralCycleOperatorViaRange
  have hseedRange := R.seed_mem_atomic
  rw [← smoothProjective_cycleClass_range_eq_atomic_span V H p] at hseedRange
  obtain ⟨Z, hZ⟩ := hseedRange
  have hSindex : S.basisIndex = HodgeSupportIndex.include := by
    exact R.spectral_basisIndex
  refine {
    spectral := S
    spectral_basisIndex := hSindex
    seed := {
      cycle := Z
      coefficient := fun _ => 1
      coefficient_ne_zero := by
        intro i
        norm_num
      class_eq := ?_
    }
  }
  rw [hSindex]
  simpa using hZ

/-- Every local cyclic realization therefore constructs an explicit native
cycle for the original Hodge class. -/
theorem LocalCyclicRealization.exists_native_cycle_constructive
    {alpha : ClassicalHodgeFiber V H p}
    (R : LocalCyclicRealization V H p alpha) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha.1 :=
  R.toLocalCycleSpectralRealization.exists_native_cycle

/-- Every local cyclic realization also constructs an explicit finite
codimension-point presentation of the original Hodge class. -/
theorem LocalCyclicRealization.exists_point_presentation_constructive
    {alpha : ClassicalHodgeFiber V H p}
    (R : LocalCyclicRealization V H p alpha) :
    ∃ φ : FiniteCodimensionPresentation V.X p,
      φ.sum (fun x q => q • H.cycleClass p
        (codimensionPointCycle V.X p x)) = alpha.1 := by
  let RC := R.toLocalCycleSpectralRealization
  exact ⟨RC.reconstructedPresentation, RC.reconstructedPresentation_spec⟩

/-- The previous local cyclic criterion can now be upgraded from span
membership to a fully constructive native-cycle theorem without strengthening
its hypotheses. -/
theorem constructive_hodge_of_local_cyclic_realizations
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (hlocal :
      ∀ p : Nat, ∀ alpha : ClassicalHodgeFiber V H p,
        Nonempty (LocalCyclicRealization V H p alpha)) :
    BigradedBettiHodgeStatement V H
    ∧ (∀ p : Nat, ∀ alpha : ClassicalHodgeFiber V H p,
      ∃ Z : codimensionCycles V.X p,
        H.cycleClass p Z = alpha.1)
    ∧ (∀ p : Nat, ∀ alpha : ClassicalHodgeFiber V H p,
      ∃ φ : FiniteCodimensionPresentation V.X p,
        φ.sum (fun x q => q • H.cycleClass p
          (codimensionPointCycle V.X p x)) = alpha.1) := by
  have hcycle :
      ∀ p : Nat, ∀ alpha : ClassicalHodgeFiber V H p,
        Nonempty (LocalCycleSpectralRealization V H p alpha) := by
    intro q alpha
    rcases hlocal q alpha with ⟨R⟩
    exact ⟨R.toLocalCycleSpectralRealization⟩
  exact constructive_cyclic_landing_crown V H hcycle

#check cycleClassRangeSection
#check cycleClassRangeSection_spec
#check rangeStableRestriction
#check liftedCycleOperator
#check cycleClass_liftedCycleOperator
#check CycleClassOperatorPair.ofRangeStable
#check ClassicalHodgeSpectralOperator.cycleClassRange_stable
#check ClassicalHodgeSpectralOperator.toSpectralCycleOperatorViaRange
#check LocalCyclicRealization.toLocalCycleSpectralRealization
#check LocalCyclicRealization.exists_native_cycle_constructive
#check LocalCyclicRealization.exists_point_presentation_constructive
#check constructive_hodge_of_local_cyclic_realizations

#print axioms cycleClass_liftedCycleOperator
#print axioms CycleClassOperatorPair.ofRangeStable
#print axioms ClassicalHodgeSpectralOperator.toSpectralCycleOperatorViaRange
#print axioms LocalCyclicRealization.toLocalCycleSpectralRealization
#print axioms LocalCyclicRealization.exists_native_cycle_constructive
#print axioms constructive_hodge_of_local_cyclic_realizations

end GSTClassicalHodgeRangeLiftedSpectralOperator
