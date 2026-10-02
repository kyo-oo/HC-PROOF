import GSTClassicalHodgeFirstFailureReturnExactness
import GSTClassicalHodgeFirstGhostTransposeModAtomicClosure

/-!
# GST CLASSICAL HODGE — FIRST-GHOST PACKET EXACTNESS

The transpose/mod-atomic packet contains far more data than is needed for the
first-failure contradiction.  Its decisive field is already

    L(K(E)) - lambda E in AtomicSpan,
    lambda != 0,

with K(E) certified to lie in the predecessor Hodge fiber.

At a first bad weight the predecessor Hodge fiber has zero atomic defect.
`GSTClassicalHodgeFirstFailureReturnExactness` proves that the displayed return
is equivalent to E itself being algebraic.  Therefore the full transpose,
perfect-pairing, projection-formula, and correction-cycle machinery is not
needed to see the contradiction once this return field has been supplied.

This file makes that logical collapse explicit.  It is useful both as a proof
compression and as an audit rule: constructing a
`FirstGhostTransposeModAtomicGeometry` at a genuine first failure has already
constructed the missing algebraicity of the first ghost.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeFirstGhostPacketExactness

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeAtomicDefectDuality
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeProjectiveDegreeTrace
open GSTClassicalHodgePrimitiveAtomicDefectReduction
open GSTClassicalHodgeTraceZeroPrimitiveTomographyGhost
open GSTClassicalHodgePolarizedHodgeGhost
open GSTClassicalHodgeFirstGhostTransposeAdjointGeometry
open GSTClassicalHodgeFirstGhostTransposeModAtomicClosure
open GSTClassicalHodgeFirstFailureReturnExactness
open GSTClassicalHodgeFiniteClosedCorrespondenceTranspose

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {G : GeometricCycleClassSpine V H}
variable {D : LefschetzPrimitiveDecomposition G}
variable {T : ProjectiveDegreeTraceSemantics V H}
variable {p : Nat}

/-- Forget all surplus transpose/adjoint structure and retain only the bare
nonzero principal-cut return modulo atomic classes. -/
theorem FirstGhostTransposeModAtomicGeometry.toBarePrincipalCutReturn
    {A : GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor G T (p + 1)}
    {E : TraceZeroPrimitiveTomographyGhost A D}
    {K : BiFiniteClosedCorrespondence V}
    {P : PerfectHodgeFiberPairing (V := V) (H := H) (p + 1)}
    {Q : PerfectHodgeFiberPairing (V := V) (H := H) p}
    (R : FirstGhostTransposeModAtomicGeometry A E K P Q) :
    HasNonzeroPrincipalCutReturnModuloAtomic (p := p) G E.traceZeroClass := by
  let beta : ClassicalHodgeFiber V H p :=
    ⟨R.toFirstGhostTransposeAdjointGeometry.naturality.forward.cohomologyOperator
        E.traceZeroClass.1,
      R.toFirstGhostTransposeAdjointGeometry.ghost_down_hodge⟩
  refine ⟨beta, R.scalar, R.scalar_ne_zero, ?_⟩
  simpa [beta, principalCutHodgeMap_coe] using R.ghost_roundtrip_mod_atomic

/-- **PACKET -> FIRST-GHOST ALGEBRAICITY.**
At a first successor (source defect zero), the complete transpose/mod-atomic
packet already forces the canonical ghost into the actual atomic cycle-class
span. -/
theorem FirstGhostTransposeModAtomicGeometry.ghost_mem_atomicSpan
    {A : GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor G T (p + 1)}
    {E : TraceZeroPrimitiveTomographyGhost A D}
    {K : BiFiniteClosedCorrespondence V}
    {P : PerfectHodgeFiberPairing (V := V) (H := H) (p + 1)}
    {Q : PerfectHodgeFiberPairing (V := V) (H := H) p}
    (hsource : atomicDefectLinearMap V H p = 0)
    (R : FirstGhostTransposeModAtomicGeometry A E K P Q) :
    E.traceZeroClass.1 ∈
      pointCycleClassSpan (p + 1) (H.cycleClass (p + 1)) := by
  exact (nonzeroPrincipalCutReturnModuloAtomic_iff_target_atomic
    G hsource E.traceZeroClass).1 R.toBarePrincipalCutReturn

/-- Defect-zero form. -/
theorem FirstGhostTransposeModAtomicGeometry.ghost_defect_zero
    {A : GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor G T (p + 1)}
    {E : TraceZeroPrimitiveTomographyGhost A D}
    {K : BiFiniteClosedCorrespondence V}
    {P : PerfectHodgeFiberPairing (V := V) (H := H) (p + 1)}
    {Q : PerfectHodgeFiberPairing (V := V) (H := H) p}
    (hsource : atomicDefectLinearMap V H p = 0)
    (R : FirstGhostTransposeModAtomicGeometry A E K P Q) :
    atomicDefectLinearMap V H (p + 1) E.traceZeroClass = 0 := by
  exact (nonzeroPrincipalCutReturnModuloAtomic_iff_target_defect_zero
    G hsource E.traceZeroClass).1 R.toBarePrincipalCutReturn

/-- **DIRECT PACKET IMPOSSIBILITY AT A FIRST GHOST.**
No perfect-pairing calculation is required: source defect zero plus the packet's
own mod-atomic return contradicts the defining nonzero defect of the ghost. -/
theorem no_firstGhostTransposeModAtomicGeometry_of_source_zero
    {A : GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor G T (p + 1)}
    {E : TraceZeroPrimitiveTomographyGhost A D}
    {K : BiFiniteClosedCorrespondence V}
    {P : PerfectHodgeFiberPairing (V := V) (H := H) (p + 1)}
    {Q : PerfectHodgeFiberPairing (V := V) (H := H) p}
    (hsource : atomicDefectLinearMap V H p = 0) :
    IsEmpty (FirstGhostTransposeModAtomicGeometry A E K P Q) := by
  refine ⟨?_⟩
  intro R
  exact E.defect_ne_zero (R.ghost_defect_zero hsource)

/-- Any proposed constructor for the packet at a predecessor-zero / target-bad
step immediately closes that target ghost's defect.  This is the exact audit
form useful for future construction attempts. -/
theorem packet_constructor_closes_ghost
    {A : GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor G T (p + 1)}
    {E : TraceZeroPrimitiveTomographyGhost A D}
    (hsource : atomicDefectLinearMap V H p = 0)
    (build : ∃ K : BiFiniteClosedCorrespondence V,
      ∃ P : PerfectHodgeFiberPairing (V := V) (H := H) (p + 1),
      ∃ Q : PerfectHodgeFiberPairing (V := V) (H := H) p,
        Nonempty (FirstGhostTransposeModAtomicGeometry A E K P Q)) :
    atomicDefectLinearMap V H (p + 1) E.traceZeroClass = 0 := by
  rcases build with ⟨K, P, Q, ⟨R⟩⟩
  exact R.ghost_defect_zero hsource

#check FirstGhostTransposeModAtomicGeometry.toBarePrincipalCutReturn
#check FirstGhostTransposeModAtomicGeometry.ghost_mem_atomicSpan
#check FirstGhostTransposeModAtomicGeometry.ghost_defect_zero
#check no_firstGhostTransposeModAtomicGeometry_of_source_zero
#check packet_constructor_closes_ghost

#print axioms FirstGhostTransposeModAtomicGeometry.toBarePrincipalCutReturn
#print axioms FirstGhostTransposeModAtomicGeometry.ghost_mem_atomicSpan
#print axioms FirstGhostTransposeModAtomicGeometry.ghost_defect_zero
#print axioms no_firstGhostTransposeModAtomicGeometry_of_source_zero
#print axioms packet_constructor_closes_ghost

end GSTClassicalHodgeFirstGhostPacketExactness
