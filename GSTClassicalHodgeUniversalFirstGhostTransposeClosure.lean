import GSTClassicalHodgeFirstGhostTransposeModAtomicClosure
import GSTClassicalHodgeFirstGhostCorrespondenceFrontier

/-!
# GST CLASSICAL HODGE — UNIVERSAL FIRST-GHOST TRANSPOSE CLOSURE

The local first-failure theory has already reduced a hypothetical Hodge defect
to one distinguished trace-zero primitive ghost at a least bad successor
weight.  The transpose/mod-atomic geometry is still more concrete: it is
carried by one actual bi-finite closed correspondence and its genuine
transpose, and asks for a nonzero-scaled return only on that single ghost,
modulo the genuine atomic cycle-class span.

This file closes the global logical loop without re-expanding to whole-fiber
matrix units or assuming arbitrary Hodge-cycle representatives.

First, a `FirstGhostTransposeModAtomicGeometry` is forgotten to the exact
`FirstGhostCorrespondenceReturn` required by the established first-ghost
frontier.  Then the existing first-failure contradiction promotes a family of
such concrete transpose returns to the full Stage-2G Hodge statement.

No basis-cycle surjectivity, projective irreducibility, same-weight bare
Lefschetz realization, or global Hard-Lefschetz inverse is introduced here.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeUniversalFirstGhostTransposeClosure

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeAtomicDefectDuality
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeProjectiveDegreeTrace
open GSTClassicalHodgePrimitiveAtomicDefectReduction
open GSTClassicalHodgeTraceZeroPrimitiveTomographyGhost
open GSTClassicalHodgeHodgeFunctorialProjectiveDynamics
open GSTClassicalHodgePrimitiveProjectiveFailureCrown
open GSTClassicalHodgeFirstPrimitiveProjectiveFailure
open GSTClassicalHodgeFiniteClosedCorrespondence
open GSTClassicalHodgeFiniteClosedCorrespondenceTranspose
open GSTClassicalHodgeFirstGhostCorrespondenceCollision
open GSTClassicalHodgeFirstGhostCorrespondenceFrontier
open GSTClassicalHodgePolarizedHodgeGhost
open GSTClassicalHodgeFirstGhostTransposeAdjointGeometry
open GSTClassicalHodgeFirstGhostTransposeModAtomicClosure

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

namespace FirstGhostTransposeModAtomicGeometry

/-- Forget the transpose/adjoint witnesses while retaining the exact one-state
finite-correspondence return used by the minimal first-ghost collision.

This is a genuine weakening map: the forward correspondence is the forward
half of the supplied bi-finite correspondence, Hodge preservation is the
already supplied ghost-down law, and the modulo-atomic return equation is
literally the one stored in the transpose packet. -/
noncomputable def toFirstGhostCorrespondenceReturn
    {G : GeometricCycleClassSpine V H}
    {D : LefschetzPrimitiveDecomposition G}
    {T : ProjectiveDegreeTraceSemantics V H}
    {p : Nat}
    {A : GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor G T (p + 1)}
    {E : TraceZeroPrimitiveTomographyGhost A D}
    {K : BiFiniteClosedCorrespondence V}
    {P : PerfectHodgeFiberPairing (V := V) (H := H) (p + 1)}
    {Q : PerfectHodgeFiberPairing (V := V) (H := H) p}
    (R : FirstGhostTransposeModAtomicGeometry A E K P Q) :
    FirstGhostCorrespondenceReturn
      (G := G) (D := D) (T := T) (p := p)
      A E K.toFiniteClosedCorrespondence where
  naturality :=
    R.toFirstGhostTransposeAdjointGeometry.naturality.forward
  ghost_down_hodge :=
    R.toFirstGhostTransposeAdjointGeometry.ghost_down_hodge
  scalar := R.scalar
  scalar_ne_zero := R.scalar_ne_zero
  ghost_roundtrip_mod_atomic := R.ghost_roundtrip_mod_atomic

/-- At a least bad successor, the concrete transpose/mod-atomic packet is
already impossible because it forgets to the minimal one-ghost correspondence
return. -/
theorem firstFailure_forbids_via_correspondence
    {G : GeometricCycleClassSpine V H}
    {D : LefschetzPrimitiveDecomposition G}
    {T : ProjectiveDegreeTraceSemantics V H}
    {p : Nat}
    (F : FirstAtomicDefectWeight V H)
    (hp : F.weight = p + 1)
    {A : GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor G T (p + 1)}
    {E : TraceZeroPrimitiveTomographyGhost A D}
    {K : BiFiniteClosedCorrespondence V}
    {P : PerfectHodgeFiberPairing (V := V) (H := H) (p + 1)}
    {Q : PerfectHodgeFiberPairing (V := V) (H := H) p}
    (R : FirstGhostTransposeModAtomicGeometry A E K P Q) : False :=
  R.toFirstGhostCorrespondenceReturn
    |>.firstFailure_forbids_ghost_correspondence_return F hp

end FirstGhostTransposeModAtomicGeometry

/-- **GLOBAL UNIVERSAL FIRST-GHOST TRANSPOSE CLOSURE.**

For every hypothetical first bad successor, suppose the independently
geometric data produce one actual bi-finite correspondence whose transpose
packet returns the distinguished primitive ghost to a nonzero scalar multiple
of itself modulo genuine atomic cycle classes.  Then no first bad weight can
exist, hence the complete Stage-2G Hodge statement holds.

The hypothesis is deliberately local to the single canonical ghost selected
by the existing first-failure packet. -/
theorem bigradedBettiHodge_of_firstGhostTransposeModAtomicReturns
    (R : HodgeFunctorialGeometricSemantics V H)
    (T : ProjectiveDegreeTraceSemantics V H)
    (D : LefschetzPrimitiveDecomposition R.spine)
    (anchor : ∀ q : Nat,
      GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor R.spine T q)
    (pairing : ∀ q : Nat,
      PerfectHodgeFiberPairing (V := V) (H := H) q)
    (hzero : atomicDefectLinearMap V H 0 = 0)
    (returns :
      ∀ p : Nat,
      ∀ hsource : atomicDefectLinearMap V H p = 0,
      ∀ htarget : atomicDefectLinearMap V H (p + 1) ≠ 0,
        let P0 := packetOfNextWeightFailure
          R T D (anchor (p + 1)) hsource htarget
        ∃ K : BiFiniteClosedCorrespondence V,
          Nonempty
            (FirstGhostTransposeModAtomicGeometry
              (G := R.spine) (D := D) (T := T) (p := p)
              (anchor (p + 1)) P0.ghost K
              (pairing (p + 1)) (pairing p))) :
    BigradedBettiHodgeStatement V H := by
  apply bigradedBettiHodge_of_firstGhostCorrespondenceReturns
    R T D anchor hzero
  intro p hsource htarget
  let P0 := packetOfNextWeightFailure
    R T D (anchor (p + 1)) hsource htarget
  rcases returns p hsource htarget with ⟨K, hK⟩
  let Q := Classical.choice hK
  exact ⟨K.toFiniteClosedCorrespondence,
    ⟨Q.toFirstGhostCorrespondenceReturn⟩⟩

#check FirstGhostTransposeModAtomicGeometry.toFirstGhostCorrespondenceReturn
#check FirstGhostTransposeModAtomicGeometry.firstFailure_forbids_via_correspondence
#check bigradedBettiHodge_of_firstGhostTransposeModAtomicReturns

#print axioms FirstGhostTransposeModAtomicGeometry.toFirstGhostCorrespondenceReturn
#print axioms FirstGhostTransposeModAtomicGeometry.firstFailure_forbids_via_correspondence
#print axioms bigradedBettiHodge_of_firstGhostTransposeModAtomicReturns

end GSTClassicalHodgeUniversalFirstGhostTransposeClosure
