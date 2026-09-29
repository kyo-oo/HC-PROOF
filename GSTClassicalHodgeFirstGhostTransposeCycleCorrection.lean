import GSTClassicalHodgeFirstGhostTransposeAdjointGeometry
import GSTClassicalHodgeAtomicSpan

/-!
# GST CLASSICAL HODGE — FIRST GHOST TRANSPOSE CYCLE CORRECTION

The transpose-adjoint frontier previously retained one scalar-valued pairing
law on the distinguished first ghost.  This file removes that functional law
from the geometric interface.

Instead, require one completely concrete equality in the Hodge fiber:

  L(K(E)) = lambda * E + cl(Z),

where

* `K` is the genuine bi-finite downward correspondence;
* `L` is the already-constructed projective principal cut;
* `lambda` is nonzero;
* `Z` is one actual codimension-(p+1) algebraic cycle.

The atomic-range theorem proves that `cl(Z)` is algebraic.  Therefore every
Hodge vector orthogonal to algebraic classes kills the correction term.  The
transpose projection formula then converts the displayed cycle equality into
the one-ghost scaled pairing law automatically.

This is a strict geometric reformulation of the remaining frontier: no global
scaled pairing law, no matrix-unit realization, no projective irreducibility,
and no Hodge-surjectivity assumption is introduced.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeFirstGhostTransposeCycleCorrection

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeProjectiveDegreeTrace
open GSTClassicalHodgePrimitiveAtomicDefectReduction
open GSTClassicalHodgeTraceZeroPrimitiveTomographyGhost
open GSTClassicalHodgeFiniteClosedCorrespondenceTranspose
open GSTClassicalHodgePolarizedHodgeGhost
open GSTClassicalHodgeFirstGhostPolarizedCorrespondenceCriterion
open GSTClassicalHodgeFirstGhostTransposeAdjointGeometry
open GSTClassicalHodgeFirstPrimitiveProjectiveFailure

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {G : GeometricCycleClassSpine V H}
variable {D : LefschetzPrimitiveDecomposition G}
variable {T : ProjectiveDegreeTraceSemantics V H}
variable {p : Nat}

/-- The Hodge-fiber class of one genuine algebraic correction cycle. -/
noncomputable def cycleCorrectionHodgeClass
    (G : GeometricCycleClassSpine V H)
    (Z : codimensionCycles V.X (p + 1)) :
    ClassicalHodgeFiber V H (p + 1) :=
  ⟨H.cycleClass (p + 1) Z, G.algebraic_is_hodge (p + 1) Z⟩

/-- A genuine cycle correction is algebraic in the atomic-span sense used by
`OrthogonalToAlgebraicHodge`. -/
theorem cycleCorrectionHodgeClass_isAlgebraic
    (G : GeometricCycleClassSpine V H)
    (Z : codimensionCycles V.X (p + 1)) :
    IsAlgebraicHodge (cycleCorrectionHodgeClass (p := p) G Z) := by
  change H.cycleClass (p + 1) Z ∈
    pointCycleClassSpan (p + 1) (H.cycleClass (p + 1))
  rw [← smoothProjective_cycleClass_range_eq_atomic_span V H (p + 1)]
  exact ⟨Z, rfl⟩

/-- **ONE-GHOST TRANSPOSE CYCLE-CORRECTION GEOMETRY.**

The remaining scalar pairing identity is replaced by an equality with one
actual algebraic correction cycle. -/
structure FirstGhostTransposeCycleCorrectionGeometry
    (A : GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor G T (p + 1))
    (E : TraceZeroPrimitiveTomographyGhost A D)
    (K : BiFiniteClosedCorrespondence V)
    (P : PerfectHodgeFiberPairing (V := V) (H := H) (p + 1))
    (Q : PerfectHodgeFiberPairing (V := V) (H := H) p)
    extends FirstGhostTransposeAdjointGeometry A E K P Q where
  scalar : ℚ
  scalar_ne_zero : scalar ≠ 0
  correctionCycle : codimensionCycles V.X (p + 1)
  ghost_roundtrip_cycle_correction :
    principalCutHodgeMap G p
        (ghostDownHodgeClass (G := G) (D := D) (T := T)
          toFirstGhostTransposeAdjointGeometry.naturality.forward
          toFirstGhostTransposeAdjointGeometry.ghost_down_hodge) =
      scalar • E.traceZeroClass +
        cycleCorrectionHodgeClass (p := p) G correctionCycle

namespace FirstGhostTransposeCycleCorrectionGeometry

/-- Orthogonal tests kill the explicit algebraic correction cycle. -/
theorem pair_cycleCorrection_eq_zero
    {A : GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor G T (p + 1)}
    {E : TraceZeroPrimitiveTomographyGhost A D}
    {K : BiFiniteClosedCorrespondence V}
    {P : PerfectHodgeFiberPairing (V := V) (H := H) (p + 1)}
    {Q : PerfectHodgeFiberPairing (V := V) (H := H) p}
    (R : FirstGhostTransposeCycleCorrectionGeometry A E K P Q)
    (u : ClassicalHodgeFiber V H (p + 1))
    (hu : OrthogonalToAlgebraicHodge P u) :
    P.pair u (cycleCorrectionHodgeClass (p := p) G R.correctionCycle) = 0 :=
  hu _ (cycleCorrectionHodgeClass_isAlgebraic
    (p := p) G R.correctionCycle)

/-- The concrete cycle equation plus transpose adjointness automatically
manufactures the formerly supplied one-ghost scaled pairing law. -/
theorem ghost_scaled
    {A : GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor G T (p + 1)}
    {E : TraceZeroPrimitiveTomographyGhost A D}
    {K : BiFiniteClosedCorrespondence V}
    {P : PerfectHodgeFiberPairing (V := V) (H := H) (p + 1)}
    {Q : PerfectHodgeFiberPairing (V := V) (H := H) p}
    (R : FirstGhostTransposeCycleCorrectionGeometry A E K P Q) :
    ∀ u : ClassicalHodgeFiber V H (p + 1),
      ∀ hu : OrthogonalToAlgebraicHodge P u,
        Q.pair
            (orthogonalDownHodgeClass (G := G) (D := D) (T := T)
              R.toFirstGhostTransposeAdjointGeometry.naturality.forward
              R.toFirstGhostTransposeAdjointGeometry.orthogonal_down_hodge u hu)
            (ghostDownHodgeClass (G := G) (D := D) (T := T)
              R.toFirstGhostTransposeAdjointGeometry.naturality.forward
              R.toFirstGhostTransposeAdjointGeometry.ghost_down_hodge) =
          R.scalar * P.pair u E.traceZeroClass := by
  intro u hu
  rw [← R.toFirstGhostTransposeAdjointGeometry.ghost_adjoint u hu]
  rw [R.ghost_roundtrip_cycle_correction]
  rw [map_add, map_smul]
  rw [R.pair_cycleCorrection_eq_zero u hu]
  ring

/-- Package the cycle-correction geometry into the previous transpose-scaled
interface.  The `ghost_scaled` field is now a theorem, not input data. -/
noncomputable def toTransposeAdjointScaledGeometry
    {A : GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor G T (p + 1)}
    {E : TraceZeroPrimitiveTomographyGhost A D}
    {K : BiFiniteClosedCorrespondence V}
    {P : PerfectHodgeFiberPairing (V := V) (H := H) (p + 1)}
    {Q : PerfectHodgeFiberPairing (V := V) (H := H) p}
    (R : FirstGhostTransposeCycleCorrectionGeometry A E K P Q) :
    FirstGhostTransposeAdjointScaledGeometry A E K P Q where
  toFirstGhostTransposeAdjointGeometry :=
    R.toFirstGhostTransposeAdjointGeometry
  scalar := R.scalar
  scalar_ne_zero := R.scalar_ne_zero
  ghost_scaled := R.ghost_scaled

/-- **FIRST-FAILURE CYCLE-CORRECTION COLLISION.**
No least Hodge-defect weight can support the genuine transpose geometry and a
nonzero-scaled round trip modulo one actual algebraic correction cycle. -/
theorem firstFailure_forbids_transpose_cycleCorrection
    (F : FirstAtomicDefectWeight V H)
    (hp : F.weight = p + 1)
    {A : GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor G T (p + 1)}
    {E : TraceZeroPrimitiveTomographyGhost A D}
    {K : BiFiniteClosedCorrespondence V}
    {P : PerfectHodgeFiberPairing (V := V) (H := H) (p + 1)}
    {Q : PerfectHodgeFiberPairing (V := V) (H := H) p}
    (R : FirstGhostTransposeCycleCorrectionGeometry A E K P Q) : False :=
  R.toTransposeAdjointScaledGeometry
    |>.firstFailure_forbids_transpose_adjoint_scaled_geometry F hp

end FirstGhostTransposeCycleCorrectionGeometry

#check cycleCorrectionHodgeClass
#check cycleCorrectionHodgeClass_isAlgebraic
#check FirstGhostTransposeCycleCorrectionGeometry
#check FirstGhostTransposeCycleCorrectionGeometry.pair_cycleCorrection_eq_zero
#check FirstGhostTransposeCycleCorrectionGeometry.ghost_scaled
#check FirstGhostTransposeCycleCorrectionGeometry.toTransposeAdjointScaledGeometry
#check FirstGhostTransposeCycleCorrectionGeometry.firstFailure_forbids_transpose_cycleCorrection

#print axioms cycleCorrectionHodgeClass_isAlgebraic
#print axioms FirstGhostTransposeCycleCorrectionGeometry.ghost_scaled
#print axioms FirstGhostTransposeCycleCorrectionGeometry.toTransposeAdjointScaledGeometry
#print axioms FirstGhostTransposeCycleCorrectionGeometry.firstFailure_forbids_transpose_cycleCorrection

end GSTClassicalHodgeFirstGhostTransposeCycleCorrection
