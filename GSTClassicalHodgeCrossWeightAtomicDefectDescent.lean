import GSTClassicalHodgeAtomicDefectOperatorDescent
import GSTClassicalHodgeCrossWeightNativePropagation
import GSTClassicalHodgeGeometricCycleClassSpine

/-!
# GST CLASSICAL HODGE — CROSS-WEIGHT ATOMIC DEFECT DESCENT

The same-weight defect-operator layer proved that atomic-span preserving
cohomological endomorphisms act canonically on the atomic defect quotient.  The
genuine projective spine, however, contains a stronger operation that was not
yet placed on that quotient: the native principal-cut successor moves
codimension `p` to codimension `p+1`.

This file performs the graded descent with no new geometric hypothesis.
Every `GradedCycleClassOperatorPair` already carries an actual native cycle
operator and its exact cycle-class commuting square.  Consequently its
cohomological action sends the complete atomic cycle-class span in the source
weight into the complete atomic span in the target weight, and therefore
induces a canonical linear map

  AtomicDefectSpace p -> AtomicDefectSpace q.

Specializing to `GeometricCycleClassSpine.principalCutPair` produces a genuine
forward atomic-defect ladder.  This is strictly weaker than Hodge: a nonzero
defect is allowed to propagate forever.  The construction merely puts the
actual cross-weight projective geometry and the synchronized GST defect on the
same quotient universe, ready for a later contraction/duality argument.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeCrossWeightAtomicDefectDescent

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeAtomicDefectDuality
open GSTClassicalHodgeCrossWeightNativePropagation
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeFiberedCosmology

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p q r : Nat}

abbrev CohAt (H : HodgeBigradedBettiData V) (p : Nat) :=
  RationalSingularCohomology H.analytification (2 * p)

abbrev AtomicSpanAt (H : HodgeBigradedBettiData V) (p : Nat) :=
  pointCycleClassSpan p (H.cycleClass p)

abbrev DefectAt (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) (p : Nat) :=
  AtomicDefectSpace V H p

/-- The cohomological half of every genuine graded cycle-class operator sends
source atomic classes into target atomic classes. -/
theorem GradedCycleClassOperatorPair.atomicSpanStable
    (T : GradedCycleClassOperatorPair V H p q) :
    ∀ alpha : CohAt H p,
      alpha ∈ AtomicSpanAt H p →
        T.cohomologyOperator alpha ∈ AtomicSpanAt H q := by
  intro alpha halpha
  have hsource : alpha ∈ LinearMap.range (H.cycleClass p) := by
    rwa [smoothProjective_cycleClass_range_eq_atomic_span V H p]
  rcases hsource with ⟨Z, hZ⟩
  have htarget :
      T.cohomologyOperator alpha ∈ LinearMap.range (H.cycleClass q) := by
    refine ⟨T.cycleOperator Z, ?_⟩
    rw [T.cycleClass_natural, hZ]
  rwa [smoothProjective_cycleClass_range_eq_atomic_span V H q] at htarget

/-- Apply a graded cohomological transport and then project to the target
atomic defect quotient. -/
noncomputable def GradedCycleClassOperatorPair.quotientAfter
    (T : GradedCycleClassOperatorPair V H p q) :
    CohAt H p →ₗ[ℚ] DefectAt V H q :=
  (Submodule.mkQ (AtomicSpanAt H q)).comp T.cohomologyOperator

/-- The graded quotient map vanishes on the complete source atomic span. -/
theorem GradedCycleClassOperatorPair.atomicSpan_le_ker_quotientAfter
    (T : GradedCycleClassOperatorPair V H p q) :
    AtomicSpanAt H p ≤ LinearMap.ker T.quotientAfter := by
  intro alpha halpha
  change Submodule.Quotient.mk (T.cohomologyOperator alpha) = 0
  exact (Submodule.Quotient.mk_eq_zero (AtomicSpanAt H q)).2
    (T.atomicSpanStable alpha halpha)

/-- **GRADED ATOMIC-DEFECT DESCENT.**  Every genuine graded native/cohomology
pair acts canonically between the corresponding atomic defect quotients. -/
noncomputable def GradedCycleClassOperatorPair.defectOperator
    (T : GradedCycleClassOperatorPair V H p q) :
    DefectAt V H p →ₗ[ℚ] DefectAt V H q :=
  Submodule.liftQ
    (AtomicSpanAt H p)
    T.quotientAfter
    T.atomicSpan_le_ker_quotientAfter

/-- Exact representative formula for the graded defect action. -/
@[simp]
theorem GradedCycleClassOperatorPair.defectOperator_mk
    (T : GradedCycleClassOperatorPair V H p q)
    (alpha : CohAt H p) :
    T.defectOperator (Submodule.Quotient.mk alpha) =
      Submodule.Quotient.mk (T.cohomologyOperator alpha) := by
  rfl

/-- **CROSS-WEIGHT DEFECT EQUIVARIANCE.**  Whenever a Hodge class is carried
into the target Hodge fiber, taking its atomic defect commutes exactly with the
genuine graded transport. -/
theorem GradedCycleClassOperatorPair.defect_equivariant
    (T : GradedCycleClassOperatorPair V H p q)
    (alpha : ClassicalHodgeFiber V H p)
    (hq : T.cohomologyOperator alpha.1 ∈
      rationalHodgeSubspace (H.hodgeBigrading q)) :
    atomicDefectLinearMap V H q
        (⟨T.cohomologyOperator alpha.1, hq⟩ : ClassicalHodgeFiber V H q) =
      T.defectOperator (atomicDefectLinearMap V H p alpha) := by
  rw [atomicDefectLinearMap_apply, atomicDefectLinearMap_apply]
  exact T.defectOperator_mk alpha.1

/-- Composition of genuine graded pairs. -/
noncomputable def GradedCycleClassOperatorPair.comp
    (T : GradedCycleClassOperatorPair V H q r)
    (U : GradedCycleClassOperatorPair V H p q) :
    GradedCycleClassOperatorPair V H p r where
  cycleOperator := T.cycleOperator.comp U.cycleOperator
  cohomologyOperator := T.cohomologyOperator.comp U.cohomologyOperator
  cycleClass_natural := by
    intro Z
    rw [LinearMap.comp_apply, T.cycleClass_natural,
      LinearMap.comp_apply, U.cycleClass_natural]

/-- Graded defect descent respects composition exactly. -/
theorem GradedCycleClassOperatorPair.defectOperator_comp
    (T : GradedCycleClassOperatorPair V H q r)
    (U : GradedCycleClassOperatorPair V H p q) :
    (T.comp U).defectOperator = T.defectOperator.comp U.defectOperator := by
  apply LinearMap.ext
  intro z
  refine Submodule.Quotient.induction_on z ?_
  intro alpha
  rfl

/-- The genuine projective principal-cut successor gives a canonical forward
map on atomic defect spaces. -/
noncomputable def principalCutDefectOperator
    (G : GeometricCycleClassSpine V H)
    (p : Nat) :
    DefectAt V H p →ₗ[ℚ] DefectAt V H (p + 1) :=
  (G.principalCutPair p).defectOperator

/-- Representative formula for the genuine principal-cut defect transport. -/
@[simp]
theorem principalCutDefectOperator_mk
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (alpha : CohAt H p) :
    principalCutDefectOperator G p (Submodule.Quotient.mk alpha) =
      Submodule.Quotient.mk
        ((G.principalCutPair p).cohomologyOperator alpha) := by
  rfl

/-- Principal-cut defect transport is equivariant on the genuine Hodge fiber. -/
theorem principalCut_defect_equivariant
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (alpha : ClassicalHodgeFiber V H p) :
    atomicDefectLinearMap V H (p + 1)
        (⟨(G.principalCutPair p).cohomologyOperator alpha.1,
          G.principalCut_hodge p alpha.1 alpha.2⟩ :
          ClassicalHodgeFiber V H (p + 1)) =
      principalCutDefectOperator G p
        (atomicDefectLinearMap V H p alpha) := by
  exact (G.principalCutPair p).defect_equivariant alpha
    (G.principalCut_hodge p alpha.1 alpha.2)

/-- The entire finite principal-cut ladder acts on defect quotients by
composition, with no additional semantic assumption. -/
noncomputable def principalCutDefectIterate
    (G : GeometricCycleClassSpine V H) :
    (p n : Nat) → DefectAt V H p →ₗ[ℚ] DefectAt V H (p + n)
  | p, 0 => LinearMap.id
  | p, n + 1 =>
      principalCutDefectOperator G (p + n) |>.comp
        (principalCutDefectIterate G p n)

@[simp]
theorem principalCutDefectIterate_zero
    (G : GeometricCycleClassSpine V H)
    (p : Nat) :
    principalCutDefectIterate G p 0 = LinearMap.id := by
  rfl

@[simp]
theorem principalCutDefectIterate_succ
    (G : GeometricCycleClassSpine V H)
    (p n : Nat) :
    principalCutDefectIterate G p (n + 1) =
      (principalCutDefectOperator G (p + n)).comp
        (principalCutDefectIterate G p n) := by
  rfl

#check GradedCycleClassOperatorPair.atomicSpanStable
#check GradedCycleClassOperatorPair.quotientAfter
#check GradedCycleClassOperatorPair.defectOperator
#check GradedCycleClassOperatorPair.defectOperator_mk
#check GradedCycleClassOperatorPair.defect_equivariant
#check GradedCycleClassOperatorPair.comp
#check GradedCycleClassOperatorPair.defectOperator_comp
#check principalCutDefectOperator
#check principalCutDefectOperator_mk
#check principalCut_defect_equivariant
#check principalCutDefectIterate

#print axioms GradedCycleClassOperatorPair.atomicSpanStable
#print axioms GradedCycleClassOperatorPair.defectOperator
#print axioms GradedCycleClassOperatorPair.defect_equivariant
#print axioms GradedCycleClassOperatorPair.defectOperator_comp
#print axioms principalCut_defect_equivariant
#print axioms principalCutDefectIterate

end GSTClassicalHodgeCrossWeightAtomicDefectDescent
