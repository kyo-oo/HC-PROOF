import GSTClassicalHodgePolarizedDefectReciprocity

/-!
# GST CLASSICAL HODGE — POLARIZED ADJOINT RECIPROCITY

The polarized defect route can be reduced to two familiar geometric identities.
Let F be a genuine graded forward transport and R a genuine graded return
transport, both preserving the relevant Hodge fibers.  Equip source and target
Hodge fibers with perfect rational pairings P and Q.

Assume:

1. R is adjoint to F:

     P(u, R beta) = Q(F u, beta),

2. F is a nonzero-scaled pairing embedding:

     Q(F u, F alpha) = lambda * P(u, alpha).

Then

  P(u, R(F alpha) - lambda alpha) = 0

for every source Hodge vector u.  In particular it vanishes on the algebraic
orthogonal complement, so the previous polarized defect theorem makes the
round-trip error atomic and propagates target Hodge algebraicity backwards.

This isolates a classical-looking, noncircular frontier: projection-formula
adjointness plus the polarized Lefschetz pairing law.  Neither hypothesis says
that an arbitrary Hodge class is algebraic.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgePolarizedAdjointReciprocity

open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicDefectDuality
open GSTClassicalHodgePolarizedHodgeGhost
open GSTClassicalHodgeCrossWeightAtomicDefectDescent
open GSTClassicalHodgePolarizedDefectReciprocity

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p q : Nat}

namespace HodgeStableGradedReturnData

/-- Forward transport restricted to the genuine Hodge fiber. -/
noncomputable def forwardOnHodge
    (R : HodgeStableGradedReturnData V H p q) :
    ClassicalHodgeFiber V H p →ₗ[ℚ] ClassicalHodgeFiber V H q where
  toFun alpha :=
    ⟨R.forward.cohomologyOperator alpha.1,
      R.forward_hodge alpha.1 alpha.2⟩
  map_add' := by
    intro a b
    apply Subtype.ext
    simp
  map_smul' := by
    intro c a
    apply Subtype.ext
    simp

/-- Return transport restricted to the target Hodge fiber. -/
noncomputable def backwardOnHodge
    (R : HodgeStableGradedReturnData V H p q) :
    ClassicalHodgeFiber V H q →ₗ[ℚ] ClassicalHodgeFiber V H p where
  toFun beta :=
    ⟨R.backward.cohomologyOperator beta.1,
      R.backward_hodge beta.1 beta.2⟩
  map_add' := by
    intro a b
    apply Subtype.ext
    simp
  map_smul' := by
    intro c a
    apply Subtype.ext
    simp

@[simp]
theorem forwardOnHodge_coe
    (R : HodgeStableGradedReturnData V H p q)
    (alpha : ClassicalHodgeFiber V H p) :
    (R.forwardOnHodge alpha).1 = R.forward.cohomologyOperator alpha.1 :=
  rfl

@[simp]
theorem backwardOnHodge_coe
    (R : HodgeStableGradedReturnData V H p q)
    (beta : ClassicalHodgeFiber V H q) :
    (R.backwardOnHodge beta).1 = R.backward.cohomologyOperator beta.1 :=
  rfl

/-- Pairing adjointness of the genuine return to the genuine forward map. -/
def PairingAdjointLaw
    (R : HodgeStableGradedReturnData V H p q)
    (P : PerfectHodgeFiberPairing (V := V) (H := H) p)
    (Q : PerfectHodgeFiberPairing (V := V) (H := H) q) : Prop :=
  ∀ u : ClassicalHodgeFiber V H p,
    ∀ beta : ClassicalHodgeFiber V H q,
      P.pair u (R.backwardOnHodge beta) =
        Q.pair (R.forwardOnHodge u) beta

/-- Nonzero-scaled Lefschetz/polarization compatibility of the forward map. -/
def ScaledPairingLaw
    (R : HodgeStableGradedReturnData V H p q)
    (P : PerfectHodgeFiberPairing (V := V) (H := H) p)
    (Q : PerfectHodgeFiberPairing (V := V) (H := H) q) : Prop :=
  ∀ u alpha : ClassicalHodgeFiber V H p,
    Q.pair (R.forwardOnHodge u) (R.forwardOnHodge alpha) =
      R.scalar * P.pair u alpha

/-- **ADJOINT + SCALED PAIRING => ZERO ROUND-TRIP PAIRING.** -/
theorem pair_roundtripError_eq_zero
    (R : HodgeStableGradedReturnData V H p q)
    (P : PerfectHodgeFiberPairing (V := V) (H := H) p)
    (Q : PerfectHodgeFiberPairing (V := V) (H := H) q)
    (hadj : R.PairingAdjointLaw P Q)
    (hscale : R.ScaledPairingLaw P Q)
    (u alpha : ClassicalHodgeFiber V H p) :
    P.pair u (R.roundtripError alpha) = 0 := by
  change
    P.pair u
      ⟨R.backward.cohomologyOperator
          (R.forward.cohomologyOperator alpha.1) - R.scalar • alpha.1,
        _⟩ = 0
  have hadj' := hadj u (R.forwardOnHodge alpha)
  have hscale' := hscale u alpha
  rw [map_sub, map_smul]
  change
    P.pair u (R.backwardOnHodge (R.forwardOnHodge alpha)) -
        R.scalar * P.pair u alpha = 0
  rw [hadj', hscale']
  ring

/-- The two pairing identities imply the exact orthogonal-roundtrip law needed
by the quotient argument. -/
theorem orthogonalRoundtripLaw_of_adjoint_scaled
    (R : HodgeStableGradedReturnData V H p q)
    (P : PerfectHodgeFiberPairing (V := V) (H := H) p)
    (Q : PerfectHodgeFiberPairing (V := V) (H := H) q)
    (hadj : R.PairingAdjointLaw P Q)
    (hscale : R.ScaledPairingLaw P Q) :
    R.OrthogonalRoundtripLaw P := by
  intro alpha u _hu
  exact R.pair_roundtripError_eq_zero P Q hadj hscale u alpha

/-- **POLARIZED ADJOINT DEFECT PROPAGATION.**
Projection-formula adjointness plus the scaled Lefschetz pairing law propagate
vanishing of the target Hodge defect back to the source. -/
theorem source_hodge_of_adjoint_scaled_target_hodge
    (R : HodgeStableGradedReturnData V H p q)
    (P : PerfectHodgeFiberPairing (V := V) (H := H) p)
    (Q : PerfectHodgeFiberPairing (V := V) (H := H) q)
    (hadj : R.PairingAdjointLaw P Q)
    (hscale : R.ScaledPairingLaw P Q)
    (htarget : atomicDefectLinearMap V H q = 0) :
    atomicDefectLinearMap V H p = 0 :=
  R.source_hodge_of_target_hodge P
    (R.orthogonalRoundtripLaw_of_adjoint_scaled P Q hadj hscale)
    htarget

end HodgeStableGradedReturnData

#check HodgeStableGradedReturnData.forwardOnHodge
#check HodgeStableGradedReturnData.backwardOnHodge
#check HodgeStableGradedReturnData.PairingAdjointLaw
#check HodgeStableGradedReturnData.ScaledPairingLaw
#check HodgeStableGradedReturnData.pair_roundtripError_eq_zero
#check HodgeStableGradedReturnData.orthogonalRoundtripLaw_of_adjoint_scaled
#check HodgeStableGradedReturnData.source_hodge_of_adjoint_scaled_target_hodge

#print axioms HodgeStableGradedReturnData.pair_roundtripError_eq_zero
#print axioms HodgeStableGradedReturnData.orthogonalRoundtripLaw_of_adjoint_scaled
#print axioms HodgeStableGradedReturnData.source_hodge_of_adjoint_scaled_target_hodge

end GSTClassicalHodgePolarizedAdjointReciprocity
