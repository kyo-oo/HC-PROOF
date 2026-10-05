import GSTClassicalHodgePlaneCompletenessUnboundedCrown
import GSTClassicalHodgeStage2GSemanticRigidity
import GSTClassicalHodgeLocalizedL2NativeCircularity

/-!
# GST CLASSICAL HODGE — PLANE / GEOMETRIC SEMANTIC INDEPENDENCE

The intrinsic GST plane theorem is intentionally independent of the cycle-class
map.  That independence should be proved sharply, not merely stated.

Keep one Hodge bigrading and analytification fixed, and replace only the
Stage-2G cycle-class map by zero.  The resulting world has exactly the same
Hodge fibers and therefore exactly the same fixed-source GST plane calculus:
all sectors, all targets, normalized local `L^2`, exact finite collapse, and
the full unbounded higher-causal tower survive unchanged.

But any nonzero Hodge class makes the Hodge landing false in that same world.
Therefore no amount of intrinsic GST plane completeness alone can imply the
geometric Hodge statement for the unconstrained Stage-2G record.  Any
unconditional geometric proof must genuinely constrain/construct the
cycle-class semantics somewhere.
-/

set_option maxHeartbeats 180000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry

namespace GSTClassicalHodgePlaneSemanticIndependence

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgePlaneCompletenessUnboundedCrown
open GSTClassicalHodgeStage2GSemanticRigidity
open GSTClassicalHodgeOmniverseTwoSlotLefschetzBranch
open GSTClassicalHodgePrimitiveArsenalRationalization
open GSTClassicalHodgePiUnboundedOmniverseCrown
open GSTGraphV2OmniversalCore

variable {V : SmoothProjectiveComplexScheme}

/-- Transport a genuine Hodge-fiber state into the zero-cycle-class semantic
copy.  Analytification and Hodge bigrading are unchanged definitionally. -/
noncomputable def zeroCycleClassHodgeState
    (H : HodgeBigradedBettiData V)
    {p : Nat}
    (alpha : ClassicalHodgeFiber V H p) :
    ClassicalHodgeFiber V (zeroCycleClassData H) p :=
  ⟨alpha.1, alpha.2⟩

@[simp]
theorem zeroCycleClassHodgeState_val
    (H : HodgeBigradedBettiData V)
    {p : Nat}
    (alpha : ClassicalHodgeFiber V H p) :
    (zeroCycleClassHodgeState H alpha).1 = alpha.1 :=
  rfl

/-- Nonzeroness of a Hodge state is unchanged when only the cycle-class map is
erased. -/
theorem zeroCycleClassHodgeState_ne_zero
    (H : HodgeBigradedBettiData V)
    {p : Nat}
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0) :
    zeroCycleClassHodgeState H alpha ≠ 0 := by
  intro hzero
  apply halpha
  apply Subtype.ext
  exact congrArg Subtype.val hzero

/-- **ZERO-CYCLE WORLD STILL HAS FULL GST PLANE COMPLETENESS.**
All intrinsic omniverse data survive because the plane theorem depends on the
Hodge fiber and GST operators, not on cycle-class semantics. -/
theorem zeroCycleClass_full_GST_plane
    (H : HodgeBigradedBettiData V)
    {p : Nat}
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0) :=
  gst_plane_completeness_unbounded_via_universal_L2
    (V := V) (H := zeroCycleClassData H) (p := p)
    (zeroCycleClassHodgeState H alpha)
    (zeroCycleClassHodgeState_ne_zero H alpha halpha)

/-- **SHARP SEMANTIC INDEPENDENCE COUNTERMODEL.**
A nonzero rational Hodge state gives a single Stage-2G world in which the full
unbounded GST plane theorem is true while the geometric Hodge conclusion is
false. -/
theorem zeroCycleClass_plane_complete_and_hodge_false
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0) :
    (Nonempty
      { i : HodgeSupportIndex (zeroCycleClassHodgeState H alpha) //
        hodgeCoordinate i.1 (zeroCycleClassHodgeState H alpha) ≠ 0 })
    ∧ ¬ BigradedBettiHodgeStatement V (zeroCycleClassData H) := by
  constructor
  · obtain ⟨i, hi, _hevent, _hreach, _htower, _hL2, _hcollapse⟩ :=
      zeroCycleClass_full_GST_plane H alpha halpha
    exact ⟨⟨i, hi⟩⟩
  · exact not_bigradedBettiHodge_zeroCycleClass
      H p alpha.1 alpha.2 (by
        intro hzero
        apply halpha
        apply Subtype.ext
        exact hzero)

/-- **FULL PLANE / NATIVE-COMPLETION SEPARATION.**

The zero-cycle-class copy still has the complete intrinsic GST plane but fails
the exact native-plane completion predicate.  Because native completion was
proved equivalent to Stage-2G Hodge, this is the definitive obstruction: no
future strengthening of the intrinsic plane alone can manufacture the missing
native semantics. -/
theorem zeroCycleClass_plane_complete_and_nativeCompletion_false
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0) :
    (Nonempty
      { i : HodgeSupportIndex (zeroCycleClassHodgeState H alpha) //
        hodgeCoordinate i.1 (zeroCycleClassHodgeState H alpha) ≠ 0 })
      ∧
    ¬ GSTClassicalHodgeLocalizedL2NativeCircularity.NativePlaneCompletion
        V (zeroCycleClassData H) := by
  constructor
  · exact (zeroCycleClass_plane_complete_and_hodge_false H p alpha halpha).1
  · intro hcomplete
    have hHodge :
        BigradedBettiHodgeStatement V (zeroCycleClassData H) := by
      exact
        (GSTClassicalHodgeLocalizedL2NativeCircularity
          .nativePlaneCompletion_iff_bigradedBettiHodge
            (GSTClassicalHodgeGeometricCycleClassSpine.zeroCycleClassSpine H)).1
          hcomplete
    exact
      (not_bigradedBettiHodge_zeroCycleClass
        H p alpha.1 alpha.2 (by
          intro hzero
          apply halpha
          apply Subtype.ext
          exact hzero)) hHodge

/-- Consequently there is no universal implication from bare intrinsic plane
completeness to exact native-plane completion over the unconstrained Stage-2G
semantic record. -/
theorem no_bareStage2G_plane_to_nativeCompletion_implication
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0) :
    ¬ (∀ H' : HodgeBigradedBettiData V,
      (∀ q : Nat, ∀ a : ClassicalHodgeFiber V H' q,
        a ≠ 0 →
        Nonempty { i : HodgeSupportIndex a // hodgeCoordinate i.1 a ≠ 0 }) →
      GSTClassicalHodgeLocalizedL2NativeCircularity.NativePlaneCompletion
        V H') := by
  intro h
  let H0 := zeroCycleClassData H
  have hplane :
      ∀ q : Nat, ∀ a : ClassicalHodgeFiber V H0 q,
        a ≠ 0 →
        Nonempty { i : HodgeSupportIndex a // hodgeCoordinate i.1 a ≠ 0 } := by
    intro q a ha
    obtain ⟨i, hi, _hevent, _hreach, _htower, _hL2, _hcollapse⟩ :=
      gst_plane_completeness_unbounded_via_universal_L2
        (V := V) (H := H0) (p := q) a ha
    exact ⟨⟨i, hi⟩⟩
  have hcomplete := h H0 hplane
  exact
    (zeroCycleClass_plane_complete_and_nativeCompletion_false
      H p alpha halpha).2 hcomplete

/-- No universally quantified implication from intrinsic unbounded GST plane
completeness to Stage-2G Hodge can exist over the current unconstrained semantic
record.  The zero-cycle-class copy is the explicit witness. -/
theorem no_bareStage2G_plane_to_hodge_implication
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0) :
    ¬ (∀ H' : HodgeBigradedBettiData V,
      (∀ q : Nat, ∀ a : ClassicalHodgeFiber V H' q,
        a ≠ 0 →
        Nonempty { i : HodgeSupportIndex a // hodgeCoordinate i.1 a ≠ 0 }) →
      BigradedBettiHodgeStatement V H') := by
  intro h
  let H0 := zeroCycleClassData H
  have hplane :
      ∀ q : Nat, ∀ a : ClassicalHodgeFiber V H0 q,
        a ≠ 0 →
        Nonempty { i : HodgeSupportIndex a // hodgeCoordinate i.1 a ≠ 0 } := by
    intro q a ha
    obtain ⟨i, hi, _hevent, _hreach, _htower, _hL2, _hcollapse⟩ :=
      gst_plane_completeness_unbounded_via_universal_L2
        (V := V) (H := H0) (p := q) a ha
    exact ⟨⟨i, hi⟩⟩
  have hHodge := h H0 hplane
  exact (not_bigradedBettiHodge_zeroCycleClass
    H p alpha.1 alpha.2 (by
      intro hzero
      apply halpha
      apply Subtype.ext
      exact hzero)) hHodge

#check zeroCycleClassHodgeState
#check zeroCycleClassHodgeState_ne_zero
#check zeroCycleClass_full_GST_plane
#check zeroCycleClass_plane_complete_and_hodge_false
#check zeroCycleClass_plane_complete_and_nativeCompletion_false
#check no_bareStage2G_plane_to_nativeCompletion_implication
#check no_bareStage2G_plane_to_hodge_implication

#print axioms zeroCycleClassHodgeState_ne_zero
#print axioms zeroCycleClass_full_GST_plane
#print axioms zeroCycleClass_plane_complete_and_hodge_false
#print axioms zeroCycleClass_plane_complete_and_nativeCompletion_false
#print axioms no_bareStage2G_plane_to_nativeCompletion_implication
#print axioms no_bareStage2G_plane_to_hodge_implication

end GSTClassicalHodgePlaneSemanticIndependence
