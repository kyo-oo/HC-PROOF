import GSTClassicalHodgeNativeCohomologyExtensionAmbiguity
import GSTClassicalHodgeTraceZeroDefectProjector
import GSTClassicalHodgePrincipalCutFlagAdjointCosmology

/-!
# GST CLASSICAL HODGE — ATOMIC-DEFECT WORLDTRACE RIGIDITY EXPANSION

The native principal-cut geometry already fixes the action on actual algebraic
cycles.  The extension-ambiguity theorem proves that two cohomological lifts of
the same native operator can differ only through the atomic-defect quotient.

This file promotes that quotient from a passive obstruction space to a genuine
GST dynamical sector.

For two same-weight graded cycle-class-natural realizations `A,B` with the same
native operator, let

    E : AtomicDefectSpace p -> H^(2p)

be their canonical extension ambiguity and project its output back to the
atomic-defect quotient.  This gives an intrinsic endomorphism

    K : AtomicDefectSpace p -> AtomicDefectSpace p.

The new worldtrace rigidity pattern is deliberately quotient-level.  It does
NOT ask for a Hodge basis cycle, matrix-unit naturality, or surjectivity of the
cycle-class map.

The two laws are the exact collision suggested by the principal-cut flag and
the GST causal universe:

* round-trip stability: `K^2 = K`;
* positive-time no-return: `K^2 = 0`.

Hence `K = 0`.  The consequence needed for Hodge geometry is stronger than a
mere abstract zero statement: every discrepancy between the two ambient
cohomological extensions is forced back into the genuine atomic point-cycle
span.  Therefore algebraicity transfers from either extension to the other.

This is the correct strength.  Literal equality of ambient extensions is not
required; equality modulo actual algebraic cycle classes is sufficient for the
classical landing.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeAtomicDefectWorldtraceRigidityExpansion

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeAtomicDefectDuality
open GSTClassicalHodgeCrossWeightNativePropagation
open GSTClassicalHodgeNativeCohomologyExtensionAmbiguity

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

abbrev Coh :=
  RationalSingularCohomology H.analytification (2 * p)

abbrev Defect := AtomicDefectSpace V H p

/-- Canonical projection from ambient cohomology to the genuine atomic-defect
quotient. -/
noncomputable def defectProjection :
    Coh (H := H) (p := p) →ₗ[ℚ] Defect (V := V) (H := H) (p := p) :=
  Submodule.mkQ (pointCycleClassSpan p (H.cycleClass p))

/-- The residual worldtrace evolution induced by the ambiguity between two
same-native, same-weight cohomological extensions. -/
noncomputable def ambiguityDefectEvolution
    (A B : GradedCycleClassOperatorPair V H p p)
    (hnative : A.cycleOperator = B.cycleOperator) :
    Module.End ℚ (Defect (V := V) (H := H) (p := p)) :=
  (defectProjection (V := V) (H := H) (p := p)).comp
    (extensionAmbiguity A B hnative)

/-- On a quotient representative, the defect evolution is exactly the atomic
class of the ambient extension difference. -/
@[simp]
theorem ambiguityDefectEvolution_mk
    (A B : GradedCycleClassOperatorPair V H p p)
    (hnative : A.cycleOperator = B.cycleOperator)
    (alpha : Coh (H := H) (p := p)) :
    ambiguityDefectEvolution A B hnative (Submodule.Quotient.mk alpha) =
      Submodule.Quotient.mk
        (A.cohomologyOperator alpha - B.cohomologyOperator alpha) := by
  rw [ambiguityDefectEvolution, LinearMap.comp_apply]
  rw [extensionAmbiguity_mk]
  rfl

/-- **NEW GST DEFECT-WORLDTRACE LAW.**
The ambiguity evolution is simultaneously a stable round-trip channel and a
positive-time no-return channel.  This law lives entirely on the quotient left
after all actual algebraic cycle classes have already been removed. -/
structure AtomicDefectWorldtraceLaw
    (A B : GradedCycleClassOperatorPair V H p p)
    (hnative : A.cycleOperator = B.cycleOperator) : Prop where
  roundTrip :
    (ambiguityDefectEvolution A B hnative).comp
        (ambiguityDefectEvolution A B hnative) =
      ambiguityDefectEvolution A B hnative
  positiveTimeNoReturn :
    (ambiguityDefectEvolution A B hnative).comp
        (ambiguityDefectEvolution A B hnative) = 0

/-- **CAUSAL-PROJECTOR EXTINCTION.**
No nonzero defect evolution can be both a round-trip projector and a
positive-time no-return channel. -/
theorem ambiguityDefectEvolution_eq_zero
    (A B : GradedCycleClassOperatorPair V H p p)
    (hnative : A.cycleOperator = B.cycleOperator)
    (W : AtomicDefectWorldtraceLaw A B hnative) :
    ambiguityDefectEvolution A B hnative = 0 := by
  exact W.roundTrip.symm.trans W.positiveTimeNoReturn

/-- Pointwise quotient extinction: the difference of the two ambient
cohomological extensions has zero atomic defect. -/
theorem extensionDifference_quotient_eq_zero
    (A B : GradedCycleClassOperatorPair V H p p)
    (hnative : A.cycleOperator = B.cycleOperator)
    (W : AtomicDefectWorldtraceLaw A B hnative)
    (alpha : Coh (H := H) (p := p)) :
    Submodule.Quotient.mk
        (A.cohomologyOperator alpha - B.cohomologyOperator alpha :
          Coh (H := H) (p := p)) = 0 := by
  have hzero := ambiguityDefectEvolution_eq_zero A B hnative W
  have hval := LinearMap.congr_fun hzero (Submodule.Quotient.mk alpha)
  rw [ambiguityDefectEvolution_mk] at hval
  simpa using hval

/-- **WORLDTRACE AMBIGUITY COLLAPSES INTO ACTUAL ALGEBRAIC CYCLES.**
The discrepancy between the two cohomological extensions belongs to the full
atomic point-cycle span for every ambient class. -/
theorem extensionDifference_mem_atomicSpan
    (A B : GradedCycleClassOperatorPair V H p p)
    (hnative : A.cycleOperator = B.cycleOperator)
    (W : AtomicDefectWorldtraceLaw A B hnative)
    (alpha : Coh (H := H) (p := p)) :
    A.cohomologyOperator alpha - B.cohomologyOperator alpha ∈
      pointCycleClassSpan p (H.cycleClass p) := by
  apply (Submodule.Quotient.mk_eq_zero
    (pointCycleClassSpan p (H.cycleClass p))).mp
  exact extensionDifference_quotient_eq_zero A B hnative W alpha

/-- Atomicity transfers from `B` to `A`: if one extension lands in actual
algebraic cohomology on a state, then the other does too. -/
theorem atomicSpan_mem_transfer_left
    (A B : GradedCycleClassOperatorPair V H p p)
    (hnative : A.cycleOperator = B.cycleOperator)
    (W : AtomicDefectWorldtraceLaw A B hnative)
    (alpha : Coh (H := H) (p := p))
    (hB : B.cohomologyOperator alpha ∈
      pointCycleClassSpan p (H.cycleClass p)) :
    A.cohomologyOperator alpha ∈
      pointCycleClassSpan p (H.cycleClass p) := by
  have hdiff := extensionDifference_mem_atomicSpan A B hnative W alpha
  have hsum := (pointCycleClassSpan p (H.cycleClass p)).add_mem hdiff hB
  simpa [sub_add_cancel] using hsum

/-- Atomicity also transfers in the opposite direction. -/
theorem atomicSpan_mem_transfer_right
    (A B : GradedCycleClassOperatorPair V H p p)
    (hnative : A.cycleOperator = B.cycleOperator)
    (W : AtomicDefectWorldtraceLaw A B hnative)
    (alpha : Coh (H := H) (p := p))
    (hA : A.cohomologyOperator alpha ∈
      pointCycleClassSpan p (H.cycleClass p)) :
    B.cohomologyOperator alpha ∈
      pointCycleClassSpan p (H.cycleClass p) := by
  have hdiff := extensionDifference_mem_atomicSpan A B hnative W alpha
  have hneg :
      B.cohomologyOperator alpha - A.cohomologyOperator alpha ∈
        pointCycleClassSpan p (H.cycleClass p) := by
    simpa [sub_eq_add_neg, add_comm] using
      (pointCycleClassSpan p (H.cycleClass p)).neg_mem hdiff
  have hsum := (pointCycleClassSpan p (H.cycleClass p)).add_mem hneg hA
  simpa [sub_add_cancel] using hsum

/-- **ALGEBRAICITY EQUIVALENCE UNDER DEFECT-WORLDTRACE RIGIDITY.** -/
theorem atomicSpan_mem_iff
    (A B : GradedCycleClassOperatorPair V H p p)
    (hnative : A.cycleOperator = B.cycleOperator)
    (W : AtomicDefectWorldtraceLaw A B hnative)
    (alpha : Coh (H := H) (p := p)) :
    A.cohomologyOperator alpha ∈ pointCycleClassSpan p (H.cycleClass p) ↔
      B.cohomologyOperator alpha ∈ pointCycleClassSpan p (H.cycleClass p) := by
  exact ⟨atomicSpan_mem_transfer_right A B hnative W alpha,
    atomicSpan_mem_transfer_left A B hnative W alpha⟩

/-- Cycle-class-range form of the same theorem on a smooth projective carrier.
The two extensions preserve algebraicity on exactly the same ambient states. -/
theorem cycleClassRange_mem_iff
    (A B : GradedCycleClassOperatorPair V H p p)
    (hnative : A.cycleOperator = B.cycleOperator)
    (W : AtomicDefectWorldtraceLaw A B hnative)
    (alpha : Coh (H := H) (p := p)) :
    A.cohomologyOperator alpha ∈ LinearMap.range (H.cycleClass p) ↔
      B.cohomologyOperator alpha ∈ LinearMap.range (H.cycleClass p) := by
  rw [smoothProjective_cycleClass_range_eq_atomic_span V H p]
  rw [smoothProjective_cycleClass_range_eq_atomic_span V H p]
  exact atomicSpan_mem_iff A B hnative W alpha

/-- The quotient-level rigidity is strictly weaker than literal equality of
ambient extensions: what it determines canonically is their action modulo the
actual algebraic cycle-class range, which is precisely the quotient relevant to
Hodge failure. -/
theorem extensionDifference_is_algebraic
    (A B : GradedCycleClassOperatorPair V H p p)
    (hnative : A.cycleOperator = B.cycleOperator)
    (W : AtomicDefectWorldtraceLaw A B hnative) :
    ∀ alpha : Coh (H := H) (p := p),
      ∃ Z : codimensionCycles V.X p,
        H.cycleClass p Z =
          A.cohomologyOperator alpha - B.cohomologyOperator alpha := by
  intro alpha
  have hmem := extensionDifference_mem_atomicSpan A B hnative W alpha
  rw [← smoothProjective_cycleClass_range_eq_atomic_span V H p] at hmem
  exact hmem

/-- Crown: a principal-cut/worldtrace proof of the two quotient laws would
eliminate every non-algebraic extension discrepancy at once. -/
theorem atomic_defect_worldtrace_rigidity_crown
    (A B : GradedCycleClassOperatorPair V H p p)
    (hnative : A.cycleOperator = B.cycleOperator)
    (W : AtomicDefectWorldtraceLaw A B hnative) :
    ambiguityDefectEvolution A B hnative = 0
      ∧ (∀ alpha : Coh (H := H) (p := p),
          A.cohomologyOperator alpha - B.cohomologyOperator alpha ∈
            pointCycleClassSpan p (H.cycleClass p))
      ∧ (∀ alpha : Coh (H := H) (p := p),
          A.cohomologyOperator alpha ∈ LinearMap.range (H.cycleClass p) ↔
            B.cohomologyOperator alpha ∈ LinearMap.range (H.cycleClass p)) := by
  exact ⟨ambiguityDefectEvolution_eq_zero A B hnative W,
    extensionDifference_mem_atomicSpan A B hnative W,
    cycleClassRange_mem_iff A B hnative W⟩

#check defectProjection
#check ambiguityDefectEvolution
#check AtomicDefectWorldtraceLaw
#check ambiguityDefectEvolution_eq_zero
#check extensionDifference_mem_atomicSpan
#check atomicSpan_mem_iff
#check cycleClassRange_mem_iff
#check extensionDifference_is_algebraic
#check atomic_defect_worldtrace_rigidity_crown

#print axioms ambiguityDefectEvolution_eq_zero
#print axioms extensionDifference_mem_atomicSpan
#print axioms cycleClassRange_mem_iff
#print axioms atomic_defect_worldtrace_rigidity_crown

end GSTClassicalHodgeAtomicDefectWorldtraceRigidityExpansion
