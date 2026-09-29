import GSTClassicalHodgeFirstGhostCycleCorrectionExtraction
import GSTClassicalHodgeFirstGhostTransposeCycleCorrection

/-!
# GST CLASSICAL HODGE — FIRST GHOST TRANSPOSE MOD-ATOMIC CLOSURE

The transpose route no longer needs an explicit correction cycle as input.

Assume the genuine one-ghost transpose/adjoint geometry and only the quotient
statement already used by the first-ghost correspondence collision:

  L(K(E)) - lambda E ∈ atomic cycle-class span,

with `lambda ≠ 0`.

The atomic-span range theorem supplies an actual codimension-(p+1) cycle `Z`
whose class is exactly the correction.  Hence the modulo-atomic packet upgrades
canonically to the explicit cycle-correction geometry.  The preceding
transpose theorem then derives the scaled polarized identity and contradicts a
least Hodge-defect weight.

This removes both of the formerly separate extra interfaces:

* no supplied `ghost_scaled` pairing law;
* no supplied correction cycle.

The only residual round-trip datum is the quotient-native geometric statement
that the one ghost returns to a nonzero scalar multiple of itself modulo actual
algebraic cycle classes.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeFirstGhostTransposeModAtomicClosure

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
open GSTClassicalHodgeFirstGhostTransposeCycleCorrection
open GSTClassicalHodgeFirstGhostCycleCorrectionExtraction
open GSTClassicalHodgeFirstPrimitiveProjectiveFailure

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {G : GeometricCycleClassSpine V H}
variable {D : LefschetzPrimitiveDecomposition G}
variable {T : ProjectiveDegreeTraceSemantics V H}
variable {p : Nat}

/-- Genuine transpose geometry together with only a one-state nonzero-scaled
round trip modulo the complete atomic cycle-class span. -/
structure FirstGhostTransposeModAtomicGeometry
    (A : GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor G T (p + 1))
    (E : TraceZeroPrimitiveTomographyGhost A D)
    (K : BiFiniteClosedCorrespondence V)
    (P : PerfectHodgeFiberPairing (V := V) (H := H) (p + 1))
    (Q : PerfectHodgeFiberPairing (V := V) (H := H) p)
    extends FirstGhostTransposeAdjointGeometry A E K P Q where
  scalar : ℚ
  scalar_ne_zero : scalar ≠ 0
  ghost_roundtrip_mod_atomic :
    (G.principalCutPair p).cohomologyOperator
        (toFirstGhostTransposeAdjointGeometry.naturality.forward.cohomologyOperator
          E.traceZeroClass.1) -
      scalar • E.traceZeroClass.1 ∈
        pointCycleClassSpan (p + 1) (H.cycleClass (p + 1))

namespace FirstGhostTransposeModAtomicGeometry

/-- The modulo-atomic correction is represented by one actual native cycle. -/
theorem exists_cycleCorrection
    {A : GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor G T (p + 1)}
    {E : TraceZeroPrimitiveTomographyGhost A D}
    {K : BiFiniteClosedCorrespondence V}
    {P : PerfectHodgeFiberPairing (V := V) (H := H) (p + 1)}
    {Q : PerfectHodgeFiberPairing (V := V) (H := H) p}
    (R : FirstGhostTransposeModAtomicGeometry A E K P Q) :
    ∃ Z : codimensionCycles V.X (p + 1),
      (G.principalCutPair p).cohomologyOperator
          (R.toFirstGhostTransposeAdjointGeometry.naturality.forward.cohomologyOperator
            E.traceZeroClass.1) =
        R.scalar • E.traceZeroClass.1 + H.cycleClass (p + 1) Z := by
  exact exists_nativeCycle_of_atomic_correction
    (p := p)
    ((G.principalCutPair p).cohomologyOperator
      (R.toFirstGhostTransposeAdjointGeometry.naturality.forward.cohomologyOperator
        E.traceZeroClass.1))
    (R.scalar • E.traceZeroClass.1)
    R.ghost_roundtrip_mod_atomic

/-- Canonically choose the native correction cycle represented by the atomic
round-trip error. -/
noncomputable def correctionCycle
    {A : GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor G T (p + 1)}
    {E : TraceZeroPrimitiveTomographyGhost A D}
    {K : BiFiniteClosedCorrespondence V}
    {P : PerfectHodgeFiberPairing (V := V) (H := H) (p + 1)}
    {Q : PerfectHodgeFiberPairing (V := V) (H := H) p}
    (R : FirstGhostTransposeModAtomicGeometry A E K P Q) :
    codimensionCycles V.X (p + 1) :=
  Classical.choose R.exists_cycleCorrection

/-- Exact ambient cohomological equation for the chosen native correction. -/
theorem correctionCycle_spec
    {A : GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor G T (p + 1)}
    {E : TraceZeroPrimitiveTomographyGhost A D}
    {K : BiFiniteClosedCorrespondence V}
    {P : PerfectHodgeFiberPairing (V := V) (H := H) (p + 1)}
    {Q : PerfectHodgeFiberPairing (V := V) (H := H) p}
    (R : FirstGhostTransposeModAtomicGeometry A E K P Q) :
    (G.principalCutPair p).cohomologyOperator
        (R.toFirstGhostTransposeAdjointGeometry.naturality.forward.cohomologyOperator
          E.traceZeroClass.1) =
      R.scalar • E.traceZeroClass.1 +
        H.cycleClass (p + 1) R.correctionCycle :=
  Classical.choose_spec R.exists_cycleCorrection

/-- Upgrade the quotient-native round-trip law to the explicit cycle-correction
geometry.  No extra mathematical datum is introduced. -/
noncomputable def toCycleCorrectionGeometry
    {A : GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor G T (p + 1)}
    {E : TraceZeroPrimitiveTomographyGhost A D}
    {K : BiFiniteClosedCorrespondence V}
    {P : PerfectHodgeFiberPairing (V := V) (H := H) (p + 1)}
    {Q : PerfectHodgeFiberPairing (V := V) (H := H) p}
    (R : FirstGhostTransposeModAtomicGeometry A E K P Q) :
    FirstGhostTransposeCycleCorrectionGeometry A E K P Q where
  toFirstGhostTransposeAdjointGeometry :=
    R.toFirstGhostTransposeAdjointGeometry
  scalar := R.scalar
  scalar_ne_zero := R.scalar_ne_zero
  correctionCycle := R.correctionCycle
  ghost_roundtrip_cycle_correction := by
    apply Subtype.ext
    exact R.correctionCycle_spec

/-- The one-state modulo-atomic law already manufactures the formerly supplied
scaled pairing law through the explicit native correction cycle. -/
theorem ghost_scaled
    {A : GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor G T (p + 1)}
    {E : TraceZeroPrimitiveTomographyGhost A D}
    {K : BiFiniteClosedCorrespondence V}
    {P : PerfectHodgeFiberPairing (V := V) (H := H) (p + 1)}
    {Q : PerfectHodgeFiberPairing (V := V) (H := H) p}
    (R : FirstGhostTransposeModAtomicGeometry A E K P Q) :
    ∀ u : ClassicalHodgeFiber V H (p + 1),
      ∀ hu : OrthogonalToAlgebraicHodge P u,
        Q.pair
            (orthogonalDownHodgeClass (G := G) (D := D) (T := T)
              R.toFirstGhostTransposeAdjointGeometry.naturality.forward
              R.toFirstGhostTransposeAdjointGeometry.orthogonal_down_hodge u hu)
            (ghostDownHodgeClass (G := G) (D := D) (T := T)
              R.toFirstGhostTransposeAdjointGeometry.naturality.forward
              R.toFirstGhostTransposeAdjointGeometry.ghost_down_hodge) =
          R.scalar * P.pair u E.traceZeroClass :=
  R.toCycleCorrectionGeometry.ghost_scaled

/-- **FIRST-FAILURE TRANSPOSE MOD-ATOMIC COLLISION.**
At the least bad Hodge weight, genuine transpose adjoint geometry cannot carry
the distinguished primitive ghost down and return it to a nonzero scalar
multiple modulo algebraic cycles. -/
theorem firstFailure_forbids_transpose_modAtomic_geometry
    (F : FirstAtomicDefectWeight V H)
    (hp : F.weight = p + 1)
    {A : GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor G T (p + 1)}
    {E : TraceZeroPrimitiveTomographyGhost A D}
    {K : BiFiniteClosedCorrespondence V}
    {P : PerfectHodgeFiberPairing (V := V) (H := H) (p + 1)}
    {Q : PerfectHodgeFiberPairing (V := V) (H := H) p}
    (R : FirstGhostTransposeModAtomicGeometry A E K P Q) : False :=
  R.toCycleCorrectionGeometry
    |>.firstFailure_forbids_transpose_cycleCorrection F hp

end FirstGhostTransposeModAtomicGeometry

#check FirstGhostTransposeModAtomicGeometry
#check FirstGhostTransposeModAtomicGeometry.exists_cycleCorrection
#check FirstGhostTransposeModAtomicGeometry.correctionCycle
#check FirstGhostTransposeModAtomicGeometry.correctionCycle_spec
#check FirstGhostTransposeModAtomicGeometry.toCycleCorrectionGeometry
#check FirstGhostTransposeModAtomicGeometry.ghost_scaled
#check FirstGhostTransposeModAtomicGeometry.firstFailure_forbids_transpose_modAtomic_geometry

#print axioms FirstGhostTransposeModAtomicGeometry.exists_cycleCorrection
#print axioms FirstGhostTransposeModAtomicGeometry.toCycleCorrectionGeometry
#print axioms FirstGhostTransposeModAtomicGeometry.ghost_scaled
#print axioms FirstGhostTransposeModAtomicGeometry.firstFailure_forbids_transpose_modAtomic_geometry

end GSTClassicalHodgeFirstGhostTransposeModAtomicClosure
