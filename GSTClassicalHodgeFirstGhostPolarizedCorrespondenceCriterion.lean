import GSTClassicalHodgeFirstGhostCorrespondenceFrontier
import GSTClassicalHodgePolarizedDefectReciprocity

/-!
# GST CLASSICAL HODGE — FIRST GHOST POLARIZED CORRESPONDENCE CRITERION

The concrete first-ghost correspondence collision asks that one round-trip
error be algebraic modulo the complete atomic cycle-class span.  That quotient
membership can be reduced further by the already-proved perfect-pairing
criterion on the genuine Hodge fiber.

For the distinguished trace-zero primitive ghost `E`, let one actual finite
closed correspondence send its class down from weight `p+1` to weight `p`.
Assume only that this one downward image remains Hodge.  Cutting it back up by
the genuine principal cut gives a Hodge class again.  The scaled round-trip
error

  err_E = L(K(E)) - lambda E

is therefore a genuine Hodge vector at weight `p+1`.

To prove `err_E` algebraic it is enough — and by the polarized
Double-orthogonal theorem exactly equivalent — to prove

  P(u, err_E) = 0

for every Hodge vector `u` orthogonal to all algebraic Hodge classes.

This file packages that *single-error pairing identity* and derives the
previous one-ghost modulo-atomic return automatically.  No adjointness or
scaled pairing law is required on arbitrary Hodge vectors, and no complete
Hard-Lefschetz inverse is postulated.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeFirstGhostPolarizedCorrespondenceCriterion

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeAtomicDefectDuality
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeProjectiveDegreeTrace
open GSTClassicalHodgePrimitiveAtomicDefectReduction
open GSTClassicalHodgeTraceZeroPrimitiveTomographyGhost
open GSTClassicalHodgeFiniteClosedCorrespondence
open GSTClassicalHodgeGradedFiniteClosedCorrespondence
open GSTClassicalHodgePolarizedHodgeGhost
open GSTClassicalHodgePolarizedDefectReciprocity
open GSTClassicalHodgeFirstPrimitiveProjectiveFailure
open GSTClassicalHodgeFirstGhostCorrespondenceCollision

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {G : GeometricCycleClassSpine V H}
variable {D : LefschetzPrimitiveDecomposition G}
variable {T : ProjectiveDegreeTraceSemantics V H}
variable {p : Nat}

/-- The single ghost after applying one genuine downward finite
correspondence. -/
noncomputable def ghostDownHodgeClass
    {A : GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor G T (p + 1)}
    {E : TraceZeroPrimitiveTomographyGhost A D}
    {K : FiniteClosedCorrespondence V}
    (N : GradedCorrespondencePointNaturality K H (p + 1) p)
    (hdown : N.cohomologyOperator E.traceZeroClass.1 ∈
      rationalHodgeSubspace (H.hodgeBigrading p)) :
    ClassicalHodgeFiber V H p :=
  ⟨N.cohomologyOperator E.traceZeroClass.1, hdown⟩

/-- The scaled up/down round-trip error is itself a genuine Hodge vector at
weight `p+1`. -/
noncomputable def ghostRoundtripError
    {A : GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor G T (p + 1)}
    {E : TraceZeroPrimitiveTomographyGhost A D}
    {K : FiniteClosedCorrespondence V}
    (N : GradedCorrespondencePointNaturality K H (p + 1) p)
    (hdown : N.cohomologyOperator E.traceZeroClass.1 ∈
      rationalHodgeSubspace (H.hodgeBigrading p))
    (scalar : ℚ) : ClassicalHodgeFiber V H (p + 1) := by
  let beta := ghostDownHodgeClass (G := G) (D := D) (T := T) N hdown
  refine ⟨
    (G.principalCutPair p).cohomologyOperator beta.1 -
      scalar • E.traceZeroClass.1,
    ?_⟩
  apply (rationalHodgeSubspace (H.hodgeBigrading (p + 1))).sub_mem
  · exact G.principalCut_hodge p beta.1 beta.2
  · exact (rationalHodgeSubspace (H.hodgeBigrading (p + 1))).smul_mem
      scalar E.traceZeroClass.2

@[simp]
theorem ghostRoundtripError_coe
    {A : GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor G T (p + 1)}
    {E : TraceZeroPrimitiveTomographyGhost A D}
    {K : FiniteClosedCorrespondence V}
    (N : GradedCorrespondencePointNaturality K H (p + 1) p)
    (hdown : N.cohomologyOperator E.traceZeroClass.1 ∈
      rationalHodgeSubspace (H.hodgeBigrading p))
    (scalar : ℚ) :
    (ghostRoundtripError (G := G) (D := D) (T := T)
      N hdown scalar).1 =
      (G.principalCutPair p).cohomologyOperator
          (N.cohomologyOperator E.traceZeroClass.1) -
        scalar • E.traceZeroClass.1 := by
  rfl

/-- One actual correspondence plus a single polarized orthogonality identity
for the distinguished ghost round-trip error. -/
structure FirstGhostPolarizedCorrespondenceReturn
    (A : GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor G T (p + 1))
    (E : TraceZeroPrimitiveTomographyGhost A D)
    (K : FiniteClosedCorrespondence V)
    (P : PerfectHodgeFiberPairing (V := V) (H := H) (p + 1)) where
  naturality : GradedCorrespondencePointNaturality K H (p + 1) p
  ghost_down_hodge :
    naturality.cohomologyOperator E.traceZeroClass.1 ∈
      rationalHodgeSubspace (H.hodgeBigrading p)
  scalar : ℚ
  scalar_ne_zero : scalar ≠ 0
  roundtrip_orthogonal :
    ∀ u : ClassicalHodgeFiber V H (p + 1),
      OrthogonalToAlgebraicHodge P u →
        P.pair u
          (ghostRoundtripError (G := G) (D := D) (T := T)
            naturality ghost_down_hodge scalar) = 0

namespace FirstGhostPolarizedCorrespondenceReturn

/-- The single polarized orthogonality law is exactly enough to show that the
ghost round-trip error belongs to the genuine atomic cycle-class span. -/
theorem ghost_roundtrip_error_mem_atomic
    {A : GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor G T (p + 1)}
    {E : TraceZeroPrimitiveTomographyGhost A D}
    {K : FiniteClosedCorrespondence V}
    {P : PerfectHodgeFiberPairing (V := V) (H := H) (p + 1)}
    (R : FirstGhostPolarizedCorrespondenceReturn A E K P) :
    (ghostRoundtripError (G := G) (D := D) (T := T)
      R.naturality R.ghost_down_hodge R.scalar).1 ∈
      pointCycleClassSpan (p + 1) (H.cycleClass (p + 1)) := by
  exact
    (hodge_mem_atomicSpan_iff_pair_orthogonalComplement_zero
      P
      (ghostRoundtripError (G := G) (D := D) (T := T)
        R.naturality R.ghost_down_hodge R.scalar)).2
      R.roundtrip_orthogonal

/-- Forget the pairing proof and obtain the earlier concrete one-ghost
correspondence-return packet. -/
noncomputable def toFirstGhostCorrespondenceReturn
    {A : GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor G T (p + 1)}
    {E : TraceZeroPrimitiveTomographyGhost A D}
    {K : FiniteClosedCorrespondence V}
    {P : PerfectHodgeFiberPairing (V := V) (H := H) (p + 1)}
    (R : FirstGhostPolarizedCorrespondenceReturn A E K P) :
    FirstGhostCorrespondenceReturn
      (G := G) (D := D) (T := T) (p := p) A E K where
  naturality := R.naturality
  ghost_down_hodge := R.ghost_down_hodge
  scalar := R.scalar
  scalar_ne_zero := R.scalar_ne_zero
  ghost_roundtrip_mod_atomic := by
    simpa [ghostRoundtripError_coe] using R.ghost_roundtrip_error_mem_atomic

/-- If the predecessor Hodge defect vanishes, the single polarized return is
already impossible. -/
theorem impossible_of_predecessor_defect_zero
    {A : GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor G T (p + 1)}
    {E : TraceZeroPrimitiveTomographyGhost A D}
    {K : FiniteClosedCorrespondence V}
    {P : PerfectHodgeFiberPairing (V := V) (H := H) (p + 1)}
    (R : FirstGhostPolarizedCorrespondenceReturn A E K P)
    (hsource : atomicDefectLinearMap V H p = 0) : False :=
  R.toFirstGhostCorrespondenceReturn.impossible_of_predecessor_defect_zero
    hsource

/-- At a globally least bad successor, no actual finite correspondence can
satisfy this one-ghost polarized return criterion. -/
theorem firstFailure_forbids_polarized_ghost_return
    (F : FirstAtomicDefectWeight V H)
    (hp : F.weight = p + 1)
    {A : GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor G T (p + 1)}
    {E : TraceZeroPrimitiveTomographyGhost A D}
    {K : FiniteClosedCorrespondence V}
    {P : PerfectHodgeFiberPairing (V := V) (H := H) (p + 1)}
    (R : FirstGhostPolarizedCorrespondenceReturn A E K P) : False := by
  exact R.impossible_of_predecessor_defect_zero
    (firstAtomicDefect_predecessor_zero F hp)

end FirstGhostPolarizedCorrespondenceReturn

/-- **POLARIZED SINGLE-GHOST CLOSURE CRITERION.**
If every local first primitive ghost admits one actual finite correspondence
satisfying the single-error orthogonality identity, then the full Stage-2G
Hodge statement follows. -/
theorem bigradedBettiHodge_of_firstGhostPolarizedCorrespondenceReturns
    (R : GSTClassicalHodgeHodgeFunctorialProjectiveDynamics.HodgeFunctorialGeometricSemantics V H)
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
        let P0 :=
          GSTClassicalHodgePrimitiveProjectiveFailureCrown.packetOfNextWeightFailure
            R T D (anchor (p + 1)) hsource htarget
        ∃ K : FiniteClosedCorrespondence V,
          Nonempty
            (FirstGhostPolarizedCorrespondenceReturn
              (G := R.spine) (D := D) (T := T) (p := p)
              (anchor (p + 1)) P0.ghost K (pairing (p + 1)))) :
    BigradedBettiHodgeStatement V H := by
  apply
    GSTClassicalHodgeFirstGhostCorrespondenceFrontier.bigradedBettiHodge_of_firstGhostCorrespondenceReturns
      R T D anchor hzero
  intro p hsource htarget
  let P0 :=
    GSTClassicalHodgePrimitiveProjectiveFailureCrown.packetOfNextWeightFailure
      R T D (anchor (p + 1)) hsource htarget
  rcases returns p hsource htarget with ⟨K, hK⟩
  let Q := Classical.choice hK
  exact ⟨K, ⟨Q.toFirstGhostCorrespondenceReturn⟩⟩

#check ghostDownHodgeClass
#check ghostRoundtripError
#check FirstGhostPolarizedCorrespondenceReturn
#check FirstGhostPolarizedCorrespondenceReturn.ghost_roundtrip_error_mem_atomic
#check FirstGhostPolarizedCorrespondenceReturn.toFirstGhostCorrespondenceReturn
#check FirstGhostPolarizedCorrespondenceReturn.impossible_of_predecessor_defect_zero
#check FirstGhostPolarizedCorrespondenceReturn.firstFailure_forbids_polarized_ghost_return
#check bigradedBettiHodge_of_firstGhostPolarizedCorrespondenceReturns

#print axioms FirstGhostPolarizedCorrespondenceReturn.ghost_roundtrip_error_mem_atomic
#print axioms FirstGhostPolarizedCorrespondenceReturn.toFirstGhostCorrespondenceReturn
#print axioms FirstGhostPolarizedCorrespondenceReturn.impossible_of_predecessor_defect_zero
#print axioms bigradedBettiHodge_of_firstGhostPolarizedCorrespondenceReturns

end GSTClassicalHodgeFirstGhostPolarizedCorrespondenceCriterion
