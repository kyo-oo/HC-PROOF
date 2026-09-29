import GSTClassicalHodgeFirstGhostCorrespondenceCollision
import GSTClassicalHodgeFirstGhostTransposeCycleCorrection

/-!
# GST CLASSICAL HODGE — FIRST GHOST CYCLE-CORRECTION EXTRACTION

The one-ghost correspondence collision was originally stated modulo the atomic
point-cycle span.  The atomic-span machinery already proves that this span lies
inside the range of the genuine native cycle-class map.

Therefore every one-ghost modulo-atomic round-trip equation has an actual
codimension cycle witnessing its correction term.  This file makes that
conversion explicit.

No compactness converse and no Hodge-surjectivity statement are needed: the
inclusion `pointCycleClassSpan_le_cycleClass_range` alone is sufficient.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeFirstGhostCycleCorrectionExtraction

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgePrimitiveAtomicDefectReduction
open GSTClassicalHodgeTraceZeroPrimitiveTomographyGhost
open GSTClassicalHodgeFirstGhostCorrespondenceCollision

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {G : GeometricCycleClassSpine V H}
variable {D : LefschetzPrimitiveDecomposition G}
variable {T : GSTClassicalHodgeProjectiveDegreeTrace.ProjectiveDegreeTraceSemantics V H}
variable {p : Nat}

/-- Any correction lying in the atomic point-cycle span is represented by one
actual native codimension cycle. -/
theorem exists_nativeCycle_of_atomic_correction
    (x y : RationalSingularCohomology H.analytification (2 * (p + 1)))
    (hxy : x - y ∈ pointCycleClassSpan (p + 1) (H.cycleClass (p + 1))) :
    ∃ Z : codimensionCycles V.X (p + 1),
      x = y + H.cycleClass (p + 1) Z := by
  have hrange :
      x - y ∈ LinearMap.range (H.cycleClass (p + 1)) :=
    pointCycleClassSpan_le_cycleClass_range
      (p + 1) (H.cycleClass (p + 1)) hxy
  rcases hrange with ⟨Z, hZ⟩
  refine ⟨Z, ?_⟩
  rw [hZ]
  abel

namespace FirstGhostCorrespondenceReturn

/-- The old modulo-atomic first-ghost round trip automatically has an explicit
native cycle correction witness. -/
theorem exists_cycleCorrection
    {A : GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor G T (p + 1)}
    {E : TraceZeroPrimitiveTomographyGhost A D}
    {K : GSTClassicalHodgeFiniteClosedCorrespondence.FiniteClosedCorrespondence V}
    (R : FirstGhostCorrespondenceReturn A E K) :
    ∃ Z : codimensionCycles V.X (p + 1),
      (G.principalCutPair p).cohomologyOperator
          (R.naturality.cohomologyOperator E.traceZeroClass.1) =
        R.scalar • E.traceZeroClass.1 + H.cycleClass (p + 1) Z := by
  exact exists_nativeCycle_of_atomic_correction
    (p := p)
    ((G.principalCutPair p).cohomologyOperator
      (R.naturality.cohomologyOperator E.traceZeroClass.1))
    (R.scalar • E.traceZeroClass.1)
    R.ghost_roundtrip_mod_atomic

/-- Chosen concrete correction cycle for a one-ghost return packet. -/
noncomputable def correctionCycle
    {A : GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor G T (p + 1)}
    {E : TraceZeroPrimitiveTomographyGhost A D}
    {K : GSTClassicalHodgeFiniteClosedCorrespondence.FiniteClosedCorrespondence V}
    (R : FirstGhostCorrespondenceReturn A E K) :
    codimensionCycles V.X (p + 1) :=
  Classical.choose R.exists_cycleCorrection

/-- The chosen correction cycle satisfies the exact cohomological round-trip
equation. -/
theorem correctionCycle_spec
    {A : GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor G T (p + 1)}
    {E : TraceZeroPrimitiveTomographyGhost A D}
    {K : GSTClassicalHodgeFiniteClosedCorrespondence.FiniteClosedCorrespondence V}
    (R : FirstGhostCorrespondenceReturn A E K) :
    (G.principalCutPair p).cohomologyOperator
        (R.naturality.cohomologyOperator E.traceZeroClass.1) =
      R.scalar • E.traceZeroClass.1 +
        H.cycleClass (p + 1) R.correctionCycle :=
  Classical.choose_spec R.exists_cycleCorrection

end FirstGhostCorrespondenceReturn

#check exists_nativeCycle_of_atomic_correction
#check FirstGhostCorrespondenceReturn.exists_cycleCorrection
#check FirstGhostCorrespondenceReturn.correctionCycle
#check FirstGhostCorrespondenceReturn.correctionCycle_spec

#print axioms exists_nativeCycle_of_atomic_correction
#print axioms FirstGhostCorrespondenceReturn.exists_cycleCorrection
#print axioms FirstGhostCorrespondenceReturn.correctionCycle_spec

end GSTClassicalHodgeFirstGhostCycleCorrectionExtraction
