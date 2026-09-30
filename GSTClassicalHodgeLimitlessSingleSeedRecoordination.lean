import GSTClassicalHodgeFiniteSupportChart
import GSTClassicalHodgeRecoordinationArsenalCrown
import GSTClassicalHodgePrincipalCutIncidenceTransposeCosmology

/-!
# GST CLASSICAL HODGE — LIMITLESS SINGLE-SEED RECOORDINATION

This layer uses the unbounded GST world/recoordination cosmology at the exact
single-seed flag frontier.

There are two independent geometric rigidities.

1. On the singleton source chart `{x}`, the principal-cut incidence transpose
   has no room for cross-talk.  Hence the native normal return is exactly the
   nonzero self-energy scalar times the source atom.

2. A finite rational GST Poincare read can be transported to *any*
   equal-cardinality world shape.  The state is transported covariantly by the
   world groupoid; the probe is transported by the induced Poincare-transpose
   rechart.  The top pairing is then exactly invariant.

Thus the canonical N x 1 support chart is not a geometric restriction.  At the
single minimal-ghost seed one may re-coordinate the entire finite observation
into whatever equal-cardinality geometry is best adapted to the genuine flag,
without changing the separator/Poincare scalar.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open scoped BigOperators

namespace GSTClassicalHodgeLimitlessSingleSeedRecoordination

open GSTProjectiveOverC
open GSTNativeCodimensionCyclePresentation
open GSTWorldCosmology
open GSTWorldPoincareDuality
open GSTWorldRecoordinationGroupoid
open GSTClassicalHodgeFiniteSupportChart
open GSTClassicalHodgeRecoordinationArsenalCrown
open GSTClassicalHodgePrincipalCutIncidenceTransposeCosmology
open GSTClassicalHodgeRelativeSuccessorExactStratum

/-- Poincare-transpose transport of a rational probe through a world
recoordination.  The two `worldDual`s are the finite-world incarnation of
transporting a covector rather than a vector. -/
def transportPoincareProbeQ
    {N : Nat}
    (S T : GSTWorldShape N)
    (g : ShapeState S → ℚ) : ShapeState T → ℚ :=
  fun y =>
    g (worldDual ((worldRecoordinate S T).symm (worldDual y)))

/-- **LIMITLESS POINCARE RECOORDINATION LAW.**
The rational top pairing is invariant under arbitrary equal-cardinality world
recoordination when the state and probe are transported by the covariant and
Poincare-transpose actions respectively. -/
theorem rationalWorldTopPairing_recoordinate
    {N : Nat}
    (S T : GSTWorldShape N)
    (f g : ShapeState S → ℚ) :
    rationalWorldTopPairing f g =
      rationalWorldTopPairing
        (transportCoefQ S T f)
        (transportPoincareProbeQ S T g) := by
  classical
  unfold rationalWorldTopPairing transportCoefQ transportPoincareProbeQ
  symm
  exact Fintype.sum_equiv
    (worldRecoordinate S T).symm
    (fun y : ShapeState T =>
      f ((worldRecoordinate S T).symm y) *
        g (worldDual
          ((worldRecoordinate S T).symm (worldDual (worldDual y)))))
    (fun x : ShapeState S => f x * g (worldDual x))
    (fun y => by simp)

/-- A finite-support Hodge Poincare read may therefore be evaluated in any
world shape of the same live cardinality. -/
theorem fiberedPairing_eq_recoordinatedGSTPoincare
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (f : GSTClassicalHodgeFiberedCosmology.FiberedHodgeAddress V H)
    (g : GSTClassicalHodgeFiberedCosmology.FiberedCompletedAddress V H)
    (T : GSTWorldShape (fiberedSupportSize f)) :
    GSTClassicalHodgeFiberedCosmology.fiberedPairing f g =
      rationalWorldTopPairing
        (transportCoefQ (fiberedSupportShape f) T (fiberedSupportWorld f))
        (transportPoincareProbeQ
          (fiberedSupportShape f) T (dualizedSupportProbe f g)) := by
  rw [fiberedPairing_eq_finiteGSTPoincare f g]
  exact rationalWorldTopPairing_recoordinate
    (fiberedSupportShape f) T
    (fiberedSupportWorld f) (dualizedSupportProbe f g)

/-- On a singleton source chart the off-diagonal remainder vanishes globally,
not merely at the distinguished source coordinate. -/
theorem successorCrossTalk_singleton_eq_zero
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p) :
    successorCrossTalk V p ({x} : Finset (CodimensionPoint V.X p)) x = 0 := by
  classical
  apply Finsupp.ext
  intro z
  by_cases hzx : z = x
  · subst z
    exact successorCrossTalk_apply_self V p {x} x (by simp)
  · unfold successorCrossTalk
    rw [Finsupp.sub_apply]
    have hnormal :
        localSuccessorNormal V p ({x} : Finset (CodimensionPoint V.X p))
            (Finsupp.single x (1 : ℚ)) z = 0 := by
      unfold localSuccessorNormal
      rw [LinearMap.comp_apply]
      rw [successorPresentationOperator_single]
      rw [map_smul]
      unfold localSuccessorTranspose
      classical
      simp [localTransposeColumn, hzx]
    rw [hnormal]
    simp [hzx]

/-- **SINGLE-SEED EXACT FLAG NORMAL FORM.**
The genuine finite incidence round trip on the singleton source chart is
exactly its scalar self-energy times the original atom. -/
theorem localSuccessorNormal_singleton_exact
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p) :
    localSuccessorNormal V p ({x} : Finset (CodimensionPoint V.X p))
        (Finsupp.single x (1 : ℚ)) =
      successorSelfEnergy V p x • Finsupp.single x (1 : ℚ) := by
  rw [localSuccessorNormal_decomposition]
  rw [successorCrossTalk_singleton_eq_zero]
  simp

/-- Exact live principal-cut geometry makes the singleton normal scalar
nonzero, so the one-seed round trip is a genuine nonzero eigen-return. -/
theorem localSuccessorNormal_singleton_ne_zero
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hExact : RelativeSuccessorAmbientExact V p x)
    (hNonempty : (GSTClassicalHodgeRelativeSuccessorExactStratum.relativeCodimensionOneFinset
      V x.1).Nonempty) :
    localSuccessorNormal V p ({x} : Finset (CodimensionPoint V.X p))
        (Finsupp.single x (1 : ℚ)) ≠ 0 := by
  rw [localSuccessorNormal_singleton_exact]
  exact smul_ne_zero
    (successorSelfEnergy_ne_zero_of_exact_nonempty V p x hExact hNonempty)
    (by simp)

#check transportPoincareProbeQ
#check rationalWorldTopPairing_recoordinate
#check fiberedPairing_eq_recoordinatedGSTPoincare
#check successorCrossTalk_singleton_eq_zero
#check localSuccessorNormal_singleton_exact
#check localSuccessorNormal_singleton_ne_zero

#print axioms rationalWorldTopPairing_recoordinate
#print axioms fiberedPairing_eq_recoordinatedGSTPoincare
#print axioms successorCrossTalk_singleton_eq_zero
#print axioms localSuccessorNormal_singleton_exact
#print axioms localSuccessorNormal_singleton_ne_zero

end GSTClassicalHodgeLimitlessSingleSeedRecoordination
