import GSTClassicalHodgePolarizedHodgeGhost
import GSTClassicalHodgeDefectAnnihilatorReciprocity

/-!
# GST CLASSICAL HODGE — POLARIZED DEFECT RECIPROCITY

The annihilator formulation still quantifies over arbitrary ambient rational
linear functionals.  On the genuine Hodge fiber, a perfect polarization-like
pairing identifies every restricted functional with a unique Hodge vector.
This lets us replace the arbitrary-functional condition by an intrinsic
orthogonal-complement condition.

For a Hodge vector alpha:

  alpha is atomic/algebraic
    iff
  pair(u, alpha) = 0 for every Hodge vector u orthogonal to all algebraic
  Hodge classes.

This is a double-orthogonal criterion proved from the existing quotient
separation theorem and the perfect Hodge-fiber pairing.  No Hodge conclusion
is inserted: for each individual alpha it is exactly equivalent to alpha's
membership in the genuine atomic span.

We then package a graded forward/return pair that preserves the Hodge fibers.
If its nonzero-scaled round-trip error pairs to zero against the algebraic
orthogonal complement, the error is automatically atomic.  Hence the earlier
modulo-atomic defect reciprocity theorem applies.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgePolarizedDefectReciprocity

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeAtomicAnnihilator
open GSTClassicalHodgeAtomicDefectDuality
open GSTClassicalHodgePolarizedHodgeGhost
open GSTClassicalHodgeCrossWeightNativePropagation
open GSTClassicalHodgeCrossWeightAtomicDefectDescent
open GSTClassicalHodgeDefectModuloAtomicReciprocity

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p q : Nat}

/-- **POLARIZED DOUBLE-ORTHOGONAL CRITERION.**
A genuine rational Hodge vector is algebraic exactly when it is orthogonal to
every Hodge vector which is itself orthogonal to all algebraic Hodge vectors. -/
theorem hodge_mem_atomicSpan_iff_pair_orthogonalComplement_zero
    (P : PerfectHodgeFiberPairing (V := V) (H := H) p)
    (alpha : ClassicalHodgeFiber V H p) :
    alpha.1 ∈ pointCycleClassSpan p (H.cycleClass p) ↔
      ∀ u : ClassicalHodgeFiber V H p,
        OrthogonalToAlgebraicHodge P u →
          P.pair u alpha = 0 := by
  constructor
  · intro halpha u hu
    exact hu alpha halpha
  · intro hall
    by_contra hnot
    obtain ⟨ell, hellSpan, hellAlpha⟩ :=
      exists_linearFunctional_separating_submodule
        (pointCycleClassSpan p (H.cycleClass p)) alpha.1 hnot
    let ellH := separatorOnHodge (V := V) (H := H) ell
    let u := P.dualClass ellH
    have hu : OrthogonalToAlgebraicHodge P u := by
      intro beta hbeta
      rw [P.pair_dualClass]
      exact hellSpan beta.1 hbeta
    have hzero := hall u hu
    rw [P.pair_dualClass] at hzero
    exact hellAlpha hzero

/-- Graded return data whose forward and backward cohomological maps preserve
the genuine Hodge fibers. -/
structure HodgeStableGradedReturnData
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p q : Nat) where
  forward : GradedCycleClassOperatorPair V H p q
  backward : GradedCycleClassOperatorPair V H q p
  forward_hodge :
    ∀ alpha : CohAt H p,
      alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p) →
        forward.cohomologyOperator alpha ∈
          rationalHodgeSubspace (H.hodgeBigrading q)
  backward_hodge :
    ∀ beta : CohAt H q,
      beta ∈ rationalHodgeSubspace (H.hodgeBigrading q) →
        backward.cohomologyOperator beta ∈
          rationalHodgeSubspace (H.hodgeBigrading p)
  scalar : ℚ
  scalar_ne_zero : scalar ≠ 0

namespace HodgeStableGradedReturnData

/-- The round-trip error is a genuine source-weight Hodge vector. -/
noncomputable def roundtripError
    (R : HodgeStableGradedReturnData V H p q)
    (alpha : ClassicalHodgeFiber V H p) :
    ClassicalHodgeFiber V H p := by
  refine ⟨
    R.backward.cohomologyOperator
        (R.forward.cohomologyOperator alpha.1) - R.scalar • alpha.1,
    ?_⟩
  apply (rationalHodgeSubspace (H.hodgeBigrading p)).sub_mem
  · exact R.backward_hodge
      (R.forward.cohomologyOperator alpha.1)
      (R.forward_hodge alpha.1 alpha.2)
  · exact (rationalHodgeSubspace (H.hodgeBigrading p)).smul_mem
      R.scalar alpha.2

@[simp]
theorem roundtripError_coe
    (R : HodgeStableGradedReturnData V H p q)
    (alpha : ClassicalHodgeFiber V H p) :
    (R.roundtripError alpha).1 =
      R.backward.cohomologyOperator
          (R.forward.cohomologyOperator alpha.1) -
        R.scalar • alpha.1 := by
  rfl

/-- Intrinsic polarized criterion for the round-trip error to disappear in the
atomic defect quotient. -/
def OrthogonalRoundtripLaw
    (R : HodgeStableGradedReturnData V H p q)
    (P : PerfectHodgeFiberPairing (V := V) (H := H) p) : Prop :=
  ∀ alpha : ClassicalHodgeFiber V H p,
    ∀ u : ClassicalHodgeFiber V H p,
      OrthogonalToAlgebraicHodge P u →
        P.pair u (R.roundtripError alpha) = 0

/-- A polarized orthogonal round-trip law manufactures the preferred
modulo-atomic reciprocity package. -/
noncomputable def toModuloAtomic
    (R : HodgeStableGradedReturnData V H p q)
    (P : PerfectHodgeFiberPairing (V := V) (H := H) p)
    (hpair : R.OrthogonalRoundtripLaw P) :
    HodgeDefectReturnModuloAtomic V H p q where
  forward := R.forward
  backward := R.backward
  forward_hodge := R.forward_hodge
  scalar := R.scalar
  scalar_ne_zero := R.scalar_ne_zero
  roundtrip_mod_atomic := by
    intro alpha halpha
    let alphaH : ClassicalHodgeFiber V H p := ⟨alpha, halpha⟩
    have hmem :
        (R.roundtripError alphaH).1 ∈
          pointCycleClassSpan p (H.cycleClass p) :=
      (hodge_mem_atomicSpan_iff_pair_orthogonalComplement_zero
        P (R.roundtripError alphaH)).2
        (fun u hu => hpair alphaH u hu)
    simpa [alphaH, R.roundtripError] using hmem

/-- Consequently target Hodge-defect vanishing propagates backwards from a
pure pairing identity on the algebraic orthogonal complement. -/
theorem source_hodge_of_target_hodge
    (R : HodgeStableGradedReturnData V H p q)
    (P : PerfectHodgeFiberPairing (V := V) (H := H) p)
    (hpair : R.OrthogonalRoundtripLaw P)
    (htarget : atomicDefectLinearMap V H q = 0) :
    atomicDefectLinearMap V H p = 0 :=
  (R.toModuloAtomic P hpair).source_hodge_of_target_hodge htarget

end HodgeStableGradedReturnData

#check hodge_mem_atomicSpan_iff_pair_orthogonalComplement_zero
#check HodgeStableGradedReturnData
#check HodgeStableGradedReturnData.roundtripError
#check HodgeStableGradedReturnData.OrthogonalRoundtripLaw
#check HodgeStableGradedReturnData.toModuloAtomic
#check HodgeStableGradedReturnData.source_hodge_of_target_hodge

#print axioms hodge_mem_atomicSpan_iff_pair_orthogonalComplement_zero
#print axioms HodgeStableGradedReturnData.toModuloAtomic
#print axioms HodgeStableGradedReturnData.source_hodge_of_target_hodge

end GSTClassicalHodgePolarizedDefectReciprocity
