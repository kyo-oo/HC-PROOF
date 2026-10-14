import GSTClassicalHodgeGeometricCycleClassSpine

/-!
# Strict semantic test of GST geometric cycle-class spine

This is a noncircular audit of what the existing geometric operator laws
can and cannot establish. The G spine supplies genuine native geometric
operators and *commutation* with a chosen cycle-class map; it does not fix
that map to the canonical Betti cycle-class construction.

The zero linear cycle-class map satisfies all of the current G spine laws:
its naturality identities commute trivially, and the cohomology realization
of the principal-cut native operator may be chosen to be zero.

Therefore those laws ALONE cannot logically prove universal rational Hodge
algebraicity in any nonzero Hodge fiber. A complete argument must derive
additional semantics of the actual canonical cycle-class map from geometry,
rather than postulate operator stability or arbitrary basis realizations.

The result is a theorem-level consistency test; it neither asserts that the
actual geometric cycle class is zero nor disproves the classical conjecture.
-/

set_option maxHeartbeats 7000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeStage2GSemanticRigidity
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgePrimitivePushforwardNaturality
open GSTClassicalHodgeCrossWeightNativePropagation
open GSTClassicalHodgePrincipalCutSuccessorOperator

namespace GSTClassicalHodgeGeometricSpineSemanticCountermodel

variable {V : SmoothProjectiveComplexScheme}

/-- Construct an ACTUAL inhabitant of every field of the current GST spine
interface while the underlying cycle-class map is the zero linear map.
Nothing resembling Hodge surjectivity is assumed here. -/
noncomputable def zeroCycleClassSpine
    (H : HodgeBigradedBettiData V) :
    GeometricCycleClassSpine V (zeroCycleClassData H) where
  algebraic_is_hodge := by
    intro p Z
    change (0 : RationalSingularCohomology H.analytification (2 * p)) ∈
      rationalHodgeSubspace (H.hodgeBigrading p)
    exact Submodule.zero_mem _
  pushforward_naturality := by
    intro p f
    refine { cohomologyPushforward := 0, naturality := ?_ }
    intro Z
    change (0 : RationalSingularCohomology H.analytification (2 * p)) = 0
    rfl
  principalCutPair := by
    intro p
    refine {
      cycleOperator := successorNativeOperator V p,
      cohomologyOperator := 0,
      cycleClass_natural := ?_ }
    intro Z
    change (0 : RationalSingularCohomology H.analytification (2 * (p + 1))) = 0
    rfl
  principalCutPair_native := by
    intro p
    rfl
  principalCut_hodge := by
    intro p alpha halpha
    change (0 : RationalSingularCohomology H.analytification (2 * (p + 1))) ∈
      rationalHodgeSubspace (H.hodgeBigrading (p + 1))
    exact Submodule.zero_mem _

/-- The current geometric spine laws do NOT rule out a zero-cycle-class
model, even if the rational Hodge bigrading has nonzero directions. -/
theorem zero_cycle_class_satisfies_all_current_spine_laws
    (H : HodgeBigradedBettiData V) :
    Nonempty (GeometricCycleClassSpine V (zeroCycleClassData H)) :=
  ⟨zeroCycleClassSpine H⟩

/-- The same package simultaneously satisfies the geometric spine's declared
operator laws while FAILING the Hodge conclusion whenever the underlying
rational Hodge fiber is nontrivial. This prevents treating spine naturality
and arbitrary algebraic-operator formulas as a universal Hodge proof. -/
theorem geometric_spine_laws_do_not_force_hodge
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p))
    (hnonzero : alpha ≠ 0) :
    ∃ H0 : HodgeBigradedBettiData V,
      Nonempty (GeometricCycleClassSpine V H0) ∧
      ¬ BigradedBettiHodgeStatement V H0 := by
  refine ⟨zeroCycleClassData H, ⟨zeroCycleClassSpine H⟩, ?_⟩
  exact not_bigradedBettiHodge_zeroCycleClass H p alpha halpha hnonzero

#check zeroCycleClassSpine
#check zero_cycle_class_satisfies_all_current_spine_laws
#check geometric_spine_laws_do_not_force_hodge

#print axioms zero_cycle_class_satisfies_all_current_spine_laws
#print axioms geometric_spine_laws_do_not_force_hodge

end GSTClassicalHodgeGeometricSpineSemanticCountermodel
