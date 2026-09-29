import GSTClassicalHodgeAtomicDefectWorldtraceRigidityExpansion
import GSTUniversalLefschetzCausalGeometry
import GSTTruncatedWorldCohomologyRing

/-!
# GST CLASSICAL HODGE — FINITE-DEPTH ATOMIC-DEFECT WORLDTRACE

The first defect-worldtrace expansion used the sharp local collision `K^2 = K`
and `K^2 = 0`.  The limitless GST universe supplies a more natural principle:
finite windows have a finite causal depth, and positive-time propagation dies
at the boundary.

This module therefore replaces the special two-step extinction law by arbitrary
finite-time extinction.

For an atomic-defect evolution `K` define its causal time iterates by

    K^[0]   = id,
    K^[n+1] = K o K^[n].

If the principal-cut round trip makes `K` idempotent, then every positive-time
iterate is already `K`.  If the GST worldtrace dynamics also force one positive
iterate to vanish at finite depth, `K` itself must vanish.

This is exactly the algebraic collision required to splice the finite-depth
truncated GST worlds into the residual extension-ambiguity quotient.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeAtomicDefectFiniteDepthWorldtrace

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeAtomicDefectDuality
open GSTClassicalHodgeCrossWeightNativePropagation
open GSTClassicalHodgeNativeCohomologyExtensionAmbiguity
open GSTClassicalHodgeAtomicDefectWorldtraceRigidityExpansion

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Intrinsic time iteration of an endomorphism, written with composition so
it can be used independently of any particular multiplication convention on
`Module.End`. -/
def defectTimeIterate
    {Q : Type*} [AddCommGroup Q] [Module ℚ Q]
    (K : Module.End ℚ Q) : Nat → Module.End ℚ Q
  | 0 => LinearMap.id
  | n + 1 => K.comp (defectTimeIterate K n)

@[simp]
theorem defectTimeIterate_zero
    {Q : Type*} [AddCommGroup Q] [Module ℚ Q]
    (K : Module.End ℚ Q) :
    defectTimeIterate K 0 = LinearMap.id :=
  rfl

@[simp]
theorem defectTimeIterate_one
    {Q : Type*} [AddCommGroup Q] [Module ℚ Q]
    (K : Module.End ℚ Q) :
    defectTimeIterate K 1 = K := by
  apply LinearMap.ext
  intro x
  rfl

/-- Idempotence freezes every positive causal time: after the first step there
is no further change. -/
theorem defectTimeIterate_eq_self_of_idempotent
    {Q : Type*} [AddCommGroup Q] [Module ℚ Q]
    (K : Module.End ℚ Q)
    (hidem : K.comp K = K) :
    ∀ n : Nat, 0 < n → defectTimeIterate K n = K := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases hn0 : n = 0
      · subst n
        exact defectTimeIterate_one K
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
        rw [defectTimeIterate]
        rw [ih hnpos]
        exact hidem

/-- **FINITE-DEPTH CAUSAL PROJECTOR EXTINCTION.**
An idempotent channel cannot also die after a positive finite amount of causal
time unless it was zero from the start. -/
theorem eq_zero_of_idempotent_and_finite_extinction
    {Q : Type*} [AddCommGroup Q] [Module ℚ Q]
    (K : Module.End ℚ Q)
    (hidem : K.comp K = K)
    (N : Nat) (hN : 0 < N)
    (hext : defectTimeIterate K N = 0) :
    K = 0 := by
  have hfreeze := defectTimeIterate_eq_self_of_idempotent K hidem N hN
  exact hfreeze.symm.trans hext

/-- Finite-depth worldtrace rigidity for one residual extension ambiguity. -/
structure FiniteDepthAtomicDefectWorldtraceLaw
    (A B : GradedCycleClassOperatorPair V H p p)
    (hnative : A.cycleOperator = B.cycleOperator) : Prop where
  roundTrip :
    (ambiguityDefectEvolution A B hnative).comp
        (ambiguityDefectEvolution A B hnative) =
      ambiguityDefectEvolution A B hnative
  depth : Nat
  depth_pos : 0 < depth
  boundaryExtinction :
    defectTimeIterate (ambiguityDefectEvolution A B hnative) depth = 0

/-- The arbitrary finite-depth GST law kills the residual defect evolution. -/
theorem ambiguityDefectEvolution_eq_zero_of_finiteDepth
    (A B : GradedCycleClassOperatorPair V H p p)
    (hnative : A.cycleOperator = B.cycleOperator)
    (W : FiniteDepthAtomicDefectWorldtraceLaw A B hnative) :
    ambiguityDefectEvolution A B hnative = 0 := by
  exact eq_zero_of_idempotent_and_finite_extinction
    (ambiguityDefectEvolution A B hnative)
    W.roundTrip W.depth W.depth_pos W.boundaryExtinction

/-- Finite-depth extinction forces every extension discrepancy into the genuine
atomic span. -/
theorem extensionDifference_mem_atomicSpan_of_finiteDepth
    (A B : GradedCycleClassOperatorPair V H p p)
    (hnative : A.cycleOperator = B.cycleOperator)
    (W : FiniteDepthAtomicDefectWorldtraceLaw A B hnative)
    (alpha : Coh (H := H) (p := p)) :
    A.cohomologyOperator alpha - B.cohomologyOperator alpha ∈
      pointCycleClassSpan p (H.cycleClass p) := by
  apply (Submodule.Quotient.mk_eq_zero
    (pointCycleClassSpan p (H.cycleClass p))).mp
  have hzero := ambiguityDefectEvolution_eq_zero_of_finiteDepth A B hnative W
  have hval := LinearMap.congr_fun hzero (Submodule.Quotient.mk alpha)
  rw [ambiguityDefectEvolution_mk] at hval
  simpa using hval

/-- Consequently the two extensions have exactly the same algebraicity
behavior on every ambient class. -/
theorem cycleClassRange_mem_iff_of_finiteDepth
    (A B : GradedCycleClassOperatorPair V H p p)
    (hnative : A.cycleOperator = B.cycleOperator)
    (W : FiniteDepthAtomicDefectWorldtraceLaw A B hnative)
    (alpha : Coh (H := H) (p := p)) :
    A.cohomologyOperator alpha ∈ LinearMap.range (H.cycleClass p) ↔
      B.cohomologyOperator alpha ∈ LinearMap.range (H.cycleClass p) := by
  rw [smoothProjective_cycleClass_range_eq_atomic_span V H p]
  rw [smoothProjective_cycleClass_range_eq_atomic_span V H p]
  constructor
  · intro hA
    have hdiff := extensionDifference_mem_atomicSpan_of_finiteDepth
      A B hnative W alpha
    have hneg :
        B.cohomologyOperator alpha - A.cohomologyOperator alpha ∈
          pointCycleClassSpan p (H.cycleClass p) := by
      simpa [sub_eq_add_neg, add_comm] using
        (pointCycleClassSpan p (H.cycleClass p)).neg_mem hdiff
    have hsum := (pointCycleClassSpan p (H.cycleClass p)).add_mem hneg hA
    simpa [sub_add_cancel] using hsum
  · intro hB
    have hdiff := extensionDifference_mem_atomicSpan_of_finiteDepth
      A B hnative W alpha
    have hsum := (pointCycleClassSpan p (H.cycleClass p)).add_mem hdiff hB
    simpa [sub_add_cancel] using hsum

/-- The earlier two-step law embeds into the finite-depth cosmology at depth
`2`. -/
noncomputable def AtomicDefectWorldtraceLaw.toFiniteDepth
    (A B : GradedCycleClassOperatorPair V H p p)
    (hnative : A.cycleOperator = B.cycleOperator)
    (W : AtomicDefectWorldtraceLaw A B hnative) :
    FiniteDepthAtomicDefectWorldtraceLaw A B hnative where
  roundTrip := W.roundTrip
  depth := 2
  depth_pos := by omega
  boundaryExtinction := by
    change (ambiguityDefectEvolution A B hnative).comp
        (ambiguityDefectEvolution A B hnative) = 0
    exact W.positiveTimeNoReturn

/-- Crown: arbitrary finite GST causal depth is enough; no fixed historical
world size is built into the defect-rigidity mechanism. -/
theorem finite_depth_worldtrace_crown
    (A B : GradedCycleClassOperatorPair V H p p)
    (hnative : A.cycleOperator = B.cycleOperator)
    (W : FiniteDepthAtomicDefectWorldtraceLaw A B hnative) :
    ambiguityDefectEvolution A B hnative = 0
      ∧ (∀ alpha : Coh (H := H) (p := p),
          A.cohomologyOperator alpha - B.cohomologyOperator alpha ∈
            pointCycleClassSpan p (H.cycleClass p))
      ∧ (∀ alpha : Coh (H := H) (p := p),
          A.cohomologyOperator alpha ∈ LinearMap.range (H.cycleClass p) ↔
            B.cohomologyOperator alpha ∈ LinearMap.range (H.cycleClass p)) := by
  exact ⟨ambiguityDefectEvolution_eq_zero_of_finiteDepth A B hnative W,
    extensionDifference_mem_atomicSpan_of_finiteDepth A B hnative W,
    cycleClassRange_mem_iff_of_finiteDepth A B hnative W⟩

#check defectTimeIterate
#check defectTimeIterate_eq_self_of_idempotent
#check eq_zero_of_idempotent_and_finite_extinction
#check FiniteDepthAtomicDefectWorldtraceLaw
#check ambiguityDefectEvolution_eq_zero_of_finiteDepth
#check extensionDifference_mem_atomicSpan_of_finiteDepth
#check cycleClassRange_mem_iff_of_finiteDepth
#check AtomicDefectWorldtraceLaw.toFiniteDepth
#check finite_depth_worldtrace_crown

#print axioms eq_zero_of_idempotent_and_finite_extinction
#print axioms ambiguityDefectEvolution_eq_zero_of_finiteDepth
#print axioms extensionDifference_mem_atomicSpan_of_finiteDepth
#print axioms finite_depth_worldtrace_crown

end GSTClassicalHodgeAtomicDefectFiniteDepthWorldtrace
