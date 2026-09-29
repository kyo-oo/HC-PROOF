import GSTClassicalHodgeFirstGhostPolarizedCorrespondenceCriterion

/-!
# GST CLASSICAL HODGE — FIRST GHOST ADJOINT / SCALED CRITERION

The first-ghost polarized correspondence criterion still stores the final
orthogonality equation

  P(u, L K(E) - lambda E) = 0.

This file splits that equation into the two geometric identities from which it
should arise.

For the distinguished first primitive ghost `E` and one actual finite closed
correspondence `K : (p+1) -> p`, require only for algebraic-orthogonal test
vectors `u`:

1. **one-ghost adjointness**

     P(u, L beta_E) = Q(Ku, beta_E),

   where `beta_E = K(E)`;

2. **one-ghost scaled pairing**

     Q(Ku, beta_E) = lambda * P(u,E).

The downward image of `u` only has to be Hodge for those orthogonal test
vectors.  Neither identity is quantified over arbitrary target Hodge vectors
or arbitrary pairs of source vectors.

Their composition gives the previous round-trip orthogonality law and hence
the concrete modulo-atomic correspondence collision.  This is strictly weaker
than the repo's global `PairingAdjointLaw` and `ScaledPairingLaw` interfaces.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeFirstGhostAdjointScaledCriterion

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeProjectiveDegreeTrace
open GSTClassicalHodgePrimitiveAtomicDefectReduction
open GSTClassicalHodgeTraceZeroPrimitiveTomographyGhost
open GSTClassicalHodgeFiniteClosedCorrespondence
open GSTClassicalHodgeGradedFiniteClosedCorrespondence
open GSTClassicalHodgePolarizedHodgeGhost
open GSTClassicalHodgeFirstGhostPolarizedCorrespondenceCriterion
open GSTClassicalHodgeFirstPrimitiveProjectiveFailure

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {G : GeometricCycleClassSpine V H}
variable {D : LefschetzPrimitiveDecomposition G}
variable {T : ProjectiveDegreeTraceSemantics V H}
variable {p : Nat}

/-- Downward Hodge image of an orthogonal test vector under the concrete
correspondence. -/
noncomputable def orthogonalDownHodgeClass
    {A : GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor G T (p + 1)}
    {E : TraceZeroPrimitiveTomographyGhost A D}
    {K : FiniteClosedCorrespondence V}
    {P : PerfectHodgeFiberPairing (V := V) (H := H) (p + 1)}
    (N : GradedCorrespondencePointNaturality K H (p + 1) p)
    (hdown : ∀ u : ClassicalHodgeFiber V H (p + 1),
      OrthogonalToAlgebraicHodge P u →
        N.cohomologyOperator u.1 ∈
          rationalHodgeSubspace (H.hodgeBigrading p))
    (u : ClassicalHodgeFiber V H (p + 1))
    (hu : OrthogonalToAlgebraicHodge P u) :
    ClassicalHodgeFiber V H p :=
  ⟨N.cohomologyOperator u.1, hdown u hu⟩

/-- One actual correspondence satisfying only the pointwise adjoint/scaled
laws needed for the distinguished ghost and algebraic-orthogonal tests. -/
structure FirstGhostAdjointScaledCorrespondenceReturn
    (A : GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor G T (p + 1))
    (E : TraceZeroPrimitiveTomographyGhost A D)
    (K : FiniteClosedCorrespondence V)
    (P : PerfectHodgeFiberPairing (V := V) (H := H) (p + 1))
    (Q : PerfectHodgeFiberPairing (V := V) (H := H) p) where
  naturality : GradedCorrespondencePointNaturality K H (p + 1) p
  ghost_down_hodge :
    naturality.cohomologyOperator E.traceZeroClass.1 ∈
      rationalHodgeSubspace (H.hodgeBigrading p)
  orthogonal_down_hodge :
    ∀ u : ClassicalHodgeFiber V H (p + 1),
      OrthogonalToAlgebraicHodge P u →
        naturality.cohomologyOperator u.1 ∈
          rationalHodgeSubspace (H.hodgeBigrading p)
  scalar : ℚ
  scalar_ne_zero : scalar ≠ 0
  ghost_adjoint :
    ∀ u : ClassicalHodgeFiber V H (p + 1),
      ∀ hu : OrthogonalToAlgebraicHodge P u,
        P.pair u
            (principalCutHodgeMap G p
              (ghostDownHodgeClass (G := G) (D := D) (T := T)
                naturality ghost_down_hodge)) =
          Q.pair
            (orthogonalDownHodgeClass (G := G) (D := D) (T := T)
              naturality orthogonal_down_hodge u hu)
            (ghostDownHodgeClass (G := G) (D := D) (T := T)
              naturality ghost_down_hodge)
  ghost_scaled :
    ∀ u : ClassicalHodgeFiber V H (p + 1),
      ∀ hu : OrthogonalToAlgebraicHodge P u,
        Q.pair
            (orthogonalDownHodgeClass (G := G) (D := D) (T := T)
              naturality orthogonal_down_hodge u hu)
            (ghostDownHodgeClass (G := G) (D := D) (T := T)
              naturality ghost_down_hodge) =
          scalar * P.pair u E.traceZeroClass

namespace FirstGhostAdjointScaledCorrespondenceReturn

/-- The two one-ghost geometric identities imply the exact orthogonality of the
scaled round-trip error. -/
theorem ghost_roundtrip_orthogonal
    {A : GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor G T (p + 1)}
    {E : TraceZeroPrimitiveTomographyGhost A D}
    {K : FiniteClosedCorrespondence V}
    {P : PerfectHodgeFiberPairing (V := V) (H := H) (p + 1)}
    {Q : PerfectHodgeFiberPairing (V := V) (H := H) p}
    (R : FirstGhostAdjointScaledCorrespondenceReturn A E K P Q) :
    ∀ u : ClassicalHodgeFiber V H (p + 1),
      OrthogonalToAlgebraicHodge P u →
        P.pair u
          (ghostRoundtripError (G := G) (D := D) (T := T)
            R.naturality R.ghost_down_hodge R.scalar) = 0 := by
  intro u hu
  change
    P.pair u
      (principalCutHodgeMap G p
        (ghostDownHodgeClass (G := G) (D := D) (T := T)
          R.naturality R.ghost_down_hodge) -
        R.scalar • E.traceZeroClass) = 0
  rw [map_sub, map_smul]
  change
    P.pair u
        (principalCutHodgeMap G p
          (ghostDownHodgeClass (G := G) (D := D) (T := T)
            R.naturality R.ghost_down_hodge)) -
      R.scalar * P.pair u E.traceZeroClass = 0
  rw [R.ghost_adjoint u hu, R.ghost_scaled u hu]
  ring

/-- Package the pointwise adjoint/scaled laws into the previous one-error
polarized correspondence criterion. -/
noncomputable def toPolarizedReturn
    {A : GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor G T (p + 1)}
    {E : TraceZeroPrimitiveTomographyGhost A D}
    {K : FiniteClosedCorrespondence V}
    {P : PerfectHodgeFiberPairing (V := V) (H := H) (p + 1)}
    {Q : PerfectHodgeFiberPairing (V := V) (H := H) p}
    (R : FirstGhostAdjointScaledCorrespondenceReturn A E K P Q) :
    FirstGhostPolarizedCorrespondenceReturn
      (G := G) (D := D) (T := T) (p := p) A E K P where
  naturality := R.naturality
  ghost_down_hodge := R.ghost_down_hodge
  scalar := R.scalar
  scalar_ne_zero := R.scalar_ne_zero
  roundtrip_orthogonal := R.ghost_roundtrip_orthogonal

/-- Consequently the pointwise adjoint/scaled packet is impossible whenever
the predecessor defect vanishes. -/
theorem impossible_of_predecessor_defect_zero
    {A : GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor G T (p + 1)}
    {E : TraceZeroPrimitiveTomographyGhost A D}
    {K : FiniteClosedCorrespondence V}
    {P : PerfectHodgeFiberPairing (V := V) (H := H) (p + 1)}
    {Q : PerfectHodgeFiberPairing (V := V) (H := H) p}
    (R : FirstGhostAdjointScaledCorrespondenceReturn A E K P Q)
    (hsource : GSTClassicalHodgeAtomicDefectDuality.atomicDefectLinearMap V H p = 0) : False :=
  R.toPolarizedReturn.impossible_of_predecessor_defect_zero hsource

/-- At the globally least bad weight, the two pointwise geometric identities
cannot simultaneously hold for any actual finite correspondence. -/
theorem firstFailure_forbids_ghost_adjoint_scaled_return
    (F : FirstAtomicDefectWeight V H)
    (hp : F.weight = p + 1)
    {A : GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor G T (p + 1)}
    {E : TraceZeroPrimitiveTomographyGhost A D}
    {K : FiniteClosedCorrespondence V}
    {P : PerfectHodgeFiberPairing (V := V) (H := H) (p + 1)}
    {Q : PerfectHodgeFiberPairing (V := V) (H := H) p}
    (R : FirstGhostAdjointScaledCorrespondenceReturn A E K P Q) : False :=
  R.toPolarizedReturn.firstFailure_forbids_polarized_ghost_return F hp

end FirstGhostAdjointScaledCorrespondenceReturn

#check orthogonalDownHodgeClass
#check FirstGhostAdjointScaledCorrespondenceReturn
#check FirstGhostAdjointScaledCorrespondenceReturn.ghost_roundtrip_orthogonal
#check FirstGhostAdjointScaledCorrespondenceReturn.toPolarizedReturn
#check FirstGhostAdjointScaledCorrespondenceReturn.impossible_of_predecessor_defect_zero
#check FirstGhostAdjointScaledCorrespondenceReturn.firstFailure_forbids_ghost_adjoint_scaled_return

#print axioms FirstGhostAdjointScaledCorrespondenceReturn.ghost_roundtrip_orthogonal
#print axioms FirstGhostAdjointScaledCorrespondenceReturn.toPolarizedReturn
#print axioms FirstGhostAdjointScaledCorrespondenceReturn.impossible_of_predecessor_defect_zero
#print axioms FirstGhostAdjointScaledCorrespondenceReturn.firstFailure_forbids_ghost_adjoint_scaled_return

end GSTClassicalHodgeFirstGhostAdjointScaledCriterion
