import GSTClassicalHodgeSchemeFiniteCorrespondenceFirewall
import GSTClassicalHodgePrincipalCutFlagCorrespondenceDescent
import GSTClassicalHodgeFirstGhostPacketExactness

/-!
# GST CLASSICAL HODGE — SCHEME-FINITE FIRST-GHOST GATE

This file upgrades the geometric carrier required by the first-ghost incidence
route.  The old `BiFiniteClosedCorrespondence` is retained only as the native
point-kernel shadow.  Any object advertised here as an ACTUAL bi-finite
correspondence is required to be finite as a scheme morphism over both factors.

Two strict packets are installed:

* a scheme-finite principal-cut flag realization, whose transition equations
  are stated after forgetting to the established native kernel;
* a scheme-finite first-ghost transpose/mod-atomic packet, whose mathematical
  payload is the existing packet for the forgotten carrier.

The forgetful maps are canonical.  Thus every old theorem remains reusable,
but no future construction can satisfy the new gate merely by proving that the
underlying sets of fiber points happen to be finite.

The final theorem combines this semantic strengthening with the exactness
result from `GSTClassicalHodgeFirstGhostPacketExactness`: at a predecessor-zero
first failure, even the STRICT scheme-finite packet is empty unless the ghost
has already become algebraic.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeSchemeFiniteFirstGhostGate

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgePrincipalCutSuccessorOperator
open GSTClassicalHodgePrincipalCutIncidenceTransposeCosmology
open GSTClassicalHodgePrincipalCutFlagCorrespondenceDescent
open GSTClassicalHodgePrincipalCutFlagCorrespondenceDescent.PrincipalCutFlagBiFiniteRealization
open GSTClassicalHodgeSchemeFiniteCorrespondenceFirewall
open GSTClassicalHodgeSchemeFiniteCorrespondenceFirewall.SchemeBiFiniteClosedCorrespondence
open GSTClassicalHodgeFiniteClosedCorrespondenceTranspose
open GSTClassicalHodgeGradedFiniteClosedCorrespondence
open GSTClassicalHodgeAtomicDefectDuality
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeProjectiveDegreeTrace
open GSTClassicalHodgePrimitiveAtomicDefectReduction
open GSTClassicalHodgeTraceZeroPrimitiveTomographyGhost
open GSTClassicalHodgePolarizedHodgeGhost
open GSTClassicalHodgeFirstGhostTransposeModAtomicClosure
open GSTClassicalHodgeFirstGhostPacketExactness

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Strict scheme-theoretic version of one finite principal-cut incidence
chart.  Only the computational transition equations are expressed through the
legacy point-finite shadow. -/
structure SchemeFinitePrincipalCutFlagRealization
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (sigma : Finset (CodimensionPoint V.X p)) where
  correspondence : SchemeBiFiniteClosedCorrespondence V
  forward_transition :
    ∀ x : CodimensionPoint V.X p,
      x ∈ sigma →
        correspondence.toBiFiniteClosedCorrespondence.toFiniteClosedCorrespondence.
            gradedTransition (p + 1) x =
          successorPresentation V p x
  transpose_transition :
    ∀ y : CodimensionPoint V.X (p + 1),
      correspondence.toBiFiniteClosedCorrespondence.transpose.
          gradedTransition p y =
        localTransposeColumn V p sigma y

namespace SchemeFinitePrincipalCutFlagRealization

/-- Forget the strict scheme-finite carrier to the established flag API. -/
noncomputable def toPrincipalCutFlagBiFiniteRealization
    {sigma : Finset (CodimensionPoint V.X p)}
    (R : SchemeFinitePrincipalCutFlagRealization V p sigma) :
    PrincipalCutFlagBiFiniteRealization V p sigma where
  correspondence := R.correspondence.toBiFiniteClosedCorrespondence
  forward_transition := R.forward_transition
  transpose_transition := R.transpose_transition

end SchemeFinitePrincipalCutFlagRealization

variable {G : GeometricCycleClassSpine V H}
variable {D : LefschetzPrimitiveDecomposition G}
variable {T : ProjectiveDegreeTraceSemantics V H}

/-- Strict scheme-finite first-ghost packet.  The old packet is retained as the
mathematical/cohomological payload, but its correspondence must now arise by
forgetting an honest scheme-bi-finite carrier. -/
structure SchemeFiniteFirstGhostTransposeModAtomicGeometry
    (A : GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor G T (p + 1))
    (E : TraceZeroPrimitiveTomographyGhost A D)
    (P : PerfectHodgeFiberPairing (V := V) (H := H) (p + 1))
    (Q : PerfectHodgeFiberPairing (V := V) (H := H) p) where
  correspondence : SchemeBiFiniteClosedCorrespondence V
  packet : FirstGhostTransposeModAtomicGeometry
    A E correspondence.toBiFiniteClosedCorrespondence P Q

namespace SchemeFiniteFirstGhostTransposeModAtomicGeometry

/-- The strict packet immediately forgets to the old packet. -/
noncomputable def toLegacyPacket
    {A : GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor G T (p + 1)}
    {E : TraceZeroPrimitiveTomographyGhost A D}
    {P : PerfectHodgeFiberPairing (V := V) (H := H) (p + 1)}
    {Q : PerfectHodgeFiberPairing (V := V) (H := H) p}
    (R : SchemeFiniteFirstGhostTransposeModAtomicGeometry A E P Q) :
    FirstGhostTransposeModAtomicGeometry
      A E R.correspondence.toBiFiniteClosedCorrespondence P Q :=
  R.packet

/-- At predecessor defect zero, a strict packet already forces the first ghost
into the actual algebraic span. -/
theorem ghost_mem_atomicSpan
    {A : GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor G T (p + 1)}
    {E : TraceZeroPrimitiveTomographyGhost A D}
    {P : PerfectHodgeFiberPairing (V := V) (H := H) (p + 1)}
    {Q : PerfectHodgeFiberPairing (V := V) (H := H) p}
    (hsource : atomicDefectLinearMap V H p = 0)
    (R : SchemeFiniteFirstGhostTransposeModAtomicGeometry A E P Q) :
    E.traceZeroClass.1 ∈
      GSTClassicalHodgeAtomicSpan.pointCycleClassSpan
        (p + 1) (H.cycleClass (p + 1)) :=
  R.packet.ghost_mem_atomicSpan hsource

/-- **STRICT FIRST-GHOST NO-GO.**
A predecessor-zero canonical ghost cannot carry even the strengthened
scheme-theoretic packet.  Constructing such a packet has already closed the
selected ghost's defect. -/
theorem isEmpty_of_source_defect_zero
    {A : GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor G T (p + 1)}
    {E : TraceZeroPrimitiveTomographyGhost A D}
    {P : PerfectHodgeFiberPairing (V := V) (H := H) (p + 1)}
    {Q : PerfectHodgeFiberPairing (V := V) (H := H) p}
    (hsource : atomicDefectLinearMap V H p = 0) :
    IsEmpty (SchemeFiniteFirstGhostTransposeModAtomicGeometry A E P Q) := by
  refine ⟨?_⟩
  intro R
  exact E.defect_ne_zero (R.packet.ghost_defect_zero hsource)

end SchemeFiniteFirstGhostTransposeModAtomicGeometry

#check SchemeFinitePrincipalCutFlagRealization
#check SchemeFinitePrincipalCutFlagRealization.toPrincipalCutFlagBiFiniteRealization
#check SchemeFiniteFirstGhostTransposeModAtomicGeometry
#check SchemeFiniteFirstGhostTransposeModAtomicGeometry.toLegacyPacket
#check SchemeFiniteFirstGhostTransposeModAtomicGeometry.ghost_mem_atomicSpan
#check SchemeFiniteFirstGhostTransposeModAtomicGeometry.isEmpty_of_source_defect_zero

#print axioms SchemeFinitePrincipalCutFlagRealization.toPrincipalCutFlagBiFiniteRealization
#print axioms SchemeFiniteFirstGhostTransposeModAtomicGeometry.ghost_mem_atomicSpan
#print axioms SchemeFiniteFirstGhostTransposeModAtomicGeometry.isEmpty_of_source_defect_zero

end GSTClassicalHodgeSchemeFiniteFirstGhostGate
