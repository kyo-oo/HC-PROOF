import GSTClassicalHodgeFirstGhostAdjointScaledCriterion
import GSTClassicalHodgeFiniteClosedCorrespondenceTranspose

/-!
# GST CLASSICAL HODGE — FIRST GHOST TRANSPOSE ADJOINT GEOMETRY

The first-ghost adjoint/scaled criterion still presents adjointness as a scalar
pairing identity.  This file exposes the actual correspondence geometry behind
that identity.

Take a bi-finite closed correspondence `K` from the first bad weight `p+1` down
to `p`.  Its genuine algebraic transpose `Kᵗ` was constructed independently by
swapping the factors of `X ×_C X`.

For the single distinguished ghost `E`, require only:

* graded pointwise cycle-class naturality for `K` from `p+1` to `p`;
* graded pointwise cycle-class naturality for `Kᵗ` from `p` to `p+1`;
* Hodge preservation by `K` on `E` and on algebraic-orthogonal test vectors;
* equality of `Kᵗ(K(E))` with the genuine principal-cut return `L(K(E))`
  on that one ghost-down state;
* the projection-formula pairing identity only for orthogonal test vectors and
  the fixed ghost-down state.

These fields imply the previous one-ghost adjoint law.  No global projection
formula, no global Hard-Lefschetz inverse, and no basis realization is stored.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeFirstGhostTransposeAdjointGeometry

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeProjectiveDegreeTrace
open GSTClassicalHodgePrimitiveAtomicDefectReduction
open GSTClassicalHodgeTraceZeroPrimitiveTomographyGhost
open GSTClassicalHodgeFiniteClosedCorrespondence
open GSTClassicalHodgeGradedFiniteClosedCorrespondence
open GSTClassicalHodgeFiniteClosedCorrespondenceTranspose
open GSTClassicalHodgePolarizedHodgeGhost
open GSTClassicalHodgeFirstGhostPolarizedCorrespondenceCriterion
open GSTClassicalHodgeFirstGhostAdjointScaledCriterion
open GSTClassicalHodgeFirstPrimitiveProjectiveFailure

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {G : GeometricCycleClassSpine V H}
variable {D : LefschetzPrimitiveDecomposition G}
variable {T : ProjectiveDegreeTraceSemantics V H}
variable {p : Nat}

/-- Genuine downward/upward graded naturality data for one bi-finite
correspondence and its actual transpose. -/
structure BiFiniteTransposeNaturality
    (K : BiFiniteClosedCorrespondence V)
    (p q : Nat) where
  forward :
    GradedCorrespondencePointNaturality
      K.toFiniteClosedCorrespondence H p q
  transpose :
    GradedCorrespondencePointNaturality K.transpose H q p

/-- The ghost-down Hodge vector for the forward half of a bi-finite
correspondence. -/
noncomputable def biFiniteGhostDownHodgeClass
    {A : GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor G T (p + 1)}
    {E : TraceZeroPrimitiveTomographyGhost A D}
    {K : BiFiniteClosedCorrespondence V}
    (N : BiFiniteTransposeNaturality K (p + 1) p)
    (hdown : N.forward.cohomologyOperator E.traceZeroClass.1 ∈
      rationalHodgeSubspace (H.hodgeBigrading p)) :
    ClassicalHodgeFiber V H p :=
  ghostDownHodgeClass (G := G) (D := D) (T := T)
    N.forward hdown

/-- **ONE-GHOST TRANSPOSE ADJOINT GEOMETRY.**
The transpose is used only on the fixed ghost-down state, and the projection
formula is requested only against algebraic-orthogonal test vectors. -/
structure FirstGhostTransposeAdjointGeometry
    (A : GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor G T (p + 1))
    (E : TraceZeroPrimitiveTomographyGhost A D)
    (K : BiFiniteClosedCorrespondence V)
    (P : PerfectHodgeFiberPairing (V := V) (H := H) (p + 1))
    (Q : PerfectHodgeFiberPairing (V := V) (H := H) p) where
  naturality : BiFiniteTransposeNaturality K (p + 1) p
  ghost_down_hodge :
    naturality.forward.cohomologyOperator E.traceZeroClass.1 ∈
      rationalHodgeSubspace (H.hodgeBigrading p)
  orthogonal_down_hodge :
    ∀ u : ClassicalHodgeFiber V H (p + 1),
      OrthogonalToAlgebraicHodge P u →
        naturality.forward.cohomologyOperator u.1 ∈
          rationalHodgeSubspace (H.hodgeBigrading p)
  transpose_ghost_down_hodge :
    naturality.transpose.cohomologyOperator
        (naturality.forward.cohomologyOperator E.traceZeroClass.1) ∈
      rationalHodgeSubspace (H.hodgeBigrading (p + 1))
  transpose_matches_principalCut_on_ghost :
    naturality.transpose.cohomologyOperator
        (naturality.forward.cohomologyOperator E.traceZeroClass.1) =
      (G.principalCutPair p).cohomologyOperator
        (naturality.forward.cohomologyOperator E.traceZeroClass.1)
  ghost_projection_formula :
    ∀ u : ClassicalHodgeFiber V H (p + 1),
      ∀ hu : OrthogonalToAlgebraicHodge P u,
        P.pair u
          (⟨naturality.transpose.cohomologyOperator
              (naturality.forward.cohomologyOperator E.traceZeroClass.1),
            transpose_ghost_down_hodge⟩ : ClassicalHodgeFiber V H (p + 1)) =
          Q.pair
            (orthogonalDownHodgeClass (G := G) (D := D) (T := T)
              naturality.forward orthogonal_down_hodge u hu)
            (biFiniteGhostDownHodgeClass (G := G) (D := D) (T := T)
              naturality ghost_down_hodge)

namespace FirstGhostTransposeAdjointGeometry

/-- The genuine transpose geometry supplies exactly the one-ghost adjoint law
needed by the previous criterion. -/
theorem ghost_adjoint
    {A : GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor G T (p + 1)}
    {E : TraceZeroPrimitiveTomographyGhost A D}
    {K : BiFiniteClosedCorrespondence V}
    {P : PerfectHodgeFiberPairing (V := V) (H := H) (p + 1)}
    {Q : PerfectHodgeFiberPairing (V := V) (H := H) p}
    (R : FirstGhostTransposeAdjointGeometry A E K P Q) :
    ∀ u : ClassicalHodgeFiber V H (p + 1),
      ∀ hu : OrthogonalToAlgebraicHodge P u,
        P.pair u
            (principalCutHodgeMap G p
              (ghostDownHodgeClass (G := G) (D := D) (T := T)
                R.naturality.forward R.ghost_down_hodge)) =
          Q.pair
            (orthogonalDownHodgeClass (G := G) (D := D) (T := T)
              R.naturality.forward R.orthogonal_down_hodge u hu)
            (ghostDownHodgeClass (G := G) (D := D) (T := T)
              R.naturality.forward R.ghost_down_hodge) := by
  intro u hu
  have hproj := R.ghost_projection_formula u hu
  rw [R.transpose_matches_principalCut_on_ghost] at hproj
  exact hproj

end FirstGhostTransposeAdjointGeometry

/-- Add only the remaining one-ghost scaled pairing law to the genuine
transpose geometry. -/
structure FirstGhostTransposeAdjointScaledGeometry
    (A : GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor G T (p + 1))
    (E : TraceZeroPrimitiveTomographyGhost A D)
    (K : BiFiniteClosedCorrespondence V)
    (P : PerfectHodgeFiberPairing (V := V) (H := H) (p + 1))
    (Q : PerfectHodgeFiberPairing (V := V) (H := H) p)
    extends FirstGhostTransposeAdjointGeometry A E K P Q where
  scalar : ℚ
  scalar_ne_zero : scalar ≠ 0
  ghost_scaled :
    ∀ u : ClassicalHodgeFiber V H (p + 1),
      ∀ hu : OrthogonalToAlgebraicHodge P u,
        Q.pair
            (orthogonalDownHodgeClass (G := G) (D := D) (T := T)
              toFirstGhostTransposeAdjointGeometry.naturality.forward
              toFirstGhostTransposeAdjointGeometry.orthogonal_down_hodge u hu)
            (ghostDownHodgeClass (G := G) (D := D) (T := T)
              toFirstGhostTransposeAdjointGeometry.naturality.forward
              toFirstGhostTransposeAdjointGeometry.ghost_down_hodge) =
          scalar * P.pair u E.traceZeroClass

namespace FirstGhostTransposeAdjointScaledGeometry

/-- The transpose-geometric packet manufactures the previous pointwise
adjoint/scaled correspondence packet. -/
noncomputable def toAdjointScaledReturn
    {A : GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor G T (p + 1)}
    {E : TraceZeroPrimitiveTomographyGhost A D}
    {K : BiFiniteClosedCorrespondence V}
    {P : PerfectHodgeFiberPairing (V := V) (H := H) (p + 1)}
    {Q : PerfectHodgeFiberPairing (V := V) (H := H) p}
    (R : FirstGhostTransposeAdjointScaledGeometry A E K P Q) :
    FirstGhostAdjointScaledCorrespondenceReturn
      (G := G) (D := D) (T := T) (p := p)
      A E K.toFiniteClosedCorrespondence P Q where
  naturality := R.naturality.forward
  ghost_down_hodge := R.ghost_down_hodge
  orthogonal_down_hodge := R.orthogonal_down_hodge
  scalar := R.scalar
  scalar_ne_zero := R.scalar_ne_zero
  ghost_adjoint := R.toFirstGhostTransposeAdjointGeometry.ghost_adjoint
  ghost_scaled := R.ghost_scaled

/-- Hence no first failure can support the genuine transpose geometry together
with the one-ghost nonzero scale law. -/
theorem firstFailure_forbids_transpose_adjoint_scaled_geometry
    (F : FirstAtomicDefectWeight V H)
    (hp : F.weight = p + 1)
    {A : GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor G T (p + 1)}
    {E : TraceZeroPrimitiveTomographyGhost A D}
    {K : BiFiniteClosedCorrespondence V}
    {P : PerfectHodgeFiberPairing (V := V) (H := H) (p + 1)}
    {Q : PerfectHodgeFiberPairing (V := V) (H := H) p}
    (R : FirstGhostTransposeAdjointScaledGeometry A E K P Q) : False :=
  R.toAdjointScaledReturn.firstFailure_forbids_ghost_adjoint_scaled_return F hp

end FirstGhostTransposeAdjointScaledGeometry

#check BiFiniteTransposeNaturality
#check FirstGhostTransposeAdjointGeometry
#check FirstGhostTransposeAdjointGeometry.ghost_adjoint
#check FirstGhostTransposeAdjointScaledGeometry
#check FirstGhostTransposeAdjointScaledGeometry.toAdjointScaledReturn
#check FirstGhostTransposeAdjointScaledGeometry.firstFailure_forbids_transpose_adjoint_scaled_geometry

#print axioms FirstGhostTransposeAdjointGeometry.ghost_adjoint
#print axioms FirstGhostTransposeAdjointScaledGeometry.toAdjointScaledReturn
#print axioms FirstGhostTransposeAdjointScaledGeometry.firstFailure_forbids_transpose_adjoint_scaled_geometry

end GSTClassicalHodgeFirstGhostTransposeAdjointGeometry
