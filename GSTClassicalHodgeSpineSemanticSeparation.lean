import GSTClassicalHodgeGeometricCycleClassSpine
import GSTClassicalHodgeStage2GSemanticRigidity

/-!
# GST CLASSICAL HODGE — GEOMETRIC-SPINE SEMANTIC SEPARATION

This audit closes a logical loophole in the transformed-cosmology attack.

`GeometricCycleClassSpine` records algebraic-is-Hodge, projective pushforward
naturality and the principal-cut commuting square.  Those laws are all genuine
properties expected of the classical cycle-class map, but in the current
Stage-2G carrier they still do not force the stored `cycleClass` field to be the
actual nontrivial geometric cycle-class construction.

Indeed the zero cycle-class countermodel admits a `GeometricCycleClassSpine`
tautologically:

* every zero cycle class has Hodge type;
* every projective pushforward square commutes with the zero cohomology map;
* the genuine native principal-cut operator commutes with the zero cycle-class
  map and the zero cohomological operator;
* zero lies in every rational Hodge subspace.

Consequently no theorem whose only geometric input is the present spine can
close Stage 2G in a nontrivial Hodge weight.  A successful transformed proof
must consume a strictly stronger native/geometric law which the zero map cannot
satisfy — precisely the horizontal native realization / orbit-visibility
artery isolated by the limitless ghost reductions.

This theorem is not a statement against the GST cosmology.  It identifies the
exact semantic boundary at which the cosmology has to be attached to genuine
cycle-class geometry rather than to an arbitrary linear-map placeholder.
-/

set_option maxHeartbeats 60000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeSpineSemanticSeparation

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgePrimitivePushforwardNaturality
open GSTClassicalHodgeCrossWeightNativePropagation
open GSTClassicalHodgePrincipalCutSuccessorOperator
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeStage2GSemanticRigidity

variable {V : SmoothProjectiveComplexScheme}

/-- The zero-cycle-class semantic package still satisfies the present
`GeometricCycleClassSpine` interface.  The native principal-cut operator remains
fully genuine; only its cohomological realization becomes zero, which is enough
for the current commuting-square fields when the cycle-class map itself is
zero. -/
noncomputable def zeroCycleClassGeometricSpine
    (H : HodgeBigradedBettiData V) :
    GeometricCycleClassSpine V (zeroCycleClassData H) where
  algebraic_is_hodge := by
    intro p Z
    change (0 : RationalSingularCohomology H.analytification (2 * p)) ∈
      rationalHodgeSubspace (H.hodgeBigrading p)
    exact Submodule.zero_mem _

  pushforward_naturality := by
    intro p f
    refine {
      cohomologyPushforward := 0
      naturality := ?_
    }
    intro Z
    simp [zeroCycleClassData]

  principalCutPair := by
    intro p
    refine {
      cycleOperator := successorNativeOperator V p
      cohomologyOperator := 0
      cycleClass_natural := ?_
    }
    intro Z
    simp [zeroCycleClassData]

  principalCutPair_native := by
    intro p
    rfl

  principalCut_hodge := by
    intro p alpha halpha
    change (0 : RationalSingularCohomology H.analytification (2 * (p + 1))) ∈
      rationalHodgeSubspace (H.hodgeBigrading (p + 1))
    exact Submodule.zero_mem _

/-- **SPINE-PRESERVING ZERO-MAP COUNTERMODEL.**
Whenever the original Hodge bigrading has one nonzero rational `(p,p)` class,
the semantic package obtained by zeroing the cycle-class map simultaneously

1. carries the current genuine geometric-spine interface, and
2. fails the exact Stage-2G Hodge statement.

Thus the present spine by itself is formally insufficient for unconditional
closure. -/
theorem zeroCycleClassData_has_spine_and_fails_hodge
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p))
    (halpha0 : alpha ≠ 0) :
    Nonempty (GeometricCycleClassSpine V (zeroCycleClassData H))
      ∧ ¬ BigradedBettiHodgeStatement V (zeroCycleClassData H) := by
  exact ⟨
    ⟨zeroCycleClassGeometricSpine H⟩,
    not_bigradedBettiHodge_zeroCycleClass H p alpha halpha halpha0⟩

/-- No universal theorem can derive Stage-2G Hodge merely from the current
`GeometricCycleClassSpine` interface.  The zero-map model is an explicit
counterexample to that implication whenever a nonzero Hodge class exists. -/
theorem geometricSpine_alone_cannot_close
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p))
    (halpha0 : alpha ≠ 0) :
    ¬ (∀ H' : HodgeBigradedBettiData V,
        GeometricCycleClassSpine V H' →
          BigradedBettiHodgeStatement V H') := by
  intro hall
  have hfalse :
      BigradedBettiHodgeStatement V (zeroCycleClassData H) :=
    hall (zeroCycleClassData H) (zeroCycleClassGeometricSpine H)
  exact
    (not_bigradedBettiHodge_zeroCycleClass H p alpha halpha halpha0) hfalse

#check zeroCycleClassGeometricSpine
#check zeroCycleClassData_has_spine_and_fails_hodge
#check geometricSpine_alone_cannot_close

#print axioms zeroCycleClassGeometricSpine
#print axioms zeroCycleClassData_has_spine_and_fails_hodge
#print axioms geometricSpine_alone_cannot_close

end GSTClassicalHodgeSpineSemanticSeparation
