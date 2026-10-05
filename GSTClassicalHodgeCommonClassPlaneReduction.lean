import GSTClassicalHodgeCommonClassPlaneRealization
import GSTClassicalHodgeNativePointSeedDegreeUpgrade

/-!
# GST CLASSICAL HODGE — COMMON-CLASS PLANE REDUCTION

This module removes bookkeeping from the logical burden of GST plane
completeness.

A `CommonClassPlanePacket u v` does not contain geometric information beyond a
`StrictRelationEdgePacket u v`: from a strict relation packet, choose the
common carrier class to be the left pullback of the source itself.  The source
face is reflexive and the target face is exactly the symmetry of the strict
Betti relation.

Consequently the common-plane layer adds no new existence axiom beyond strict
relation geometry.  For a ghost-adaptive strike, a nonzero native Hodge seed
already supplies a live source coordinate through `event_to_arbitrary_target`.
Projective degree then removes the Hodge/nonzero fields from the seed packet:
once an actual codimension point exists at the ghost weight, the genuine
cycle-class spine makes its class Hodge and positive projective degree makes
that class nonzero.

Thus the strongest reduction proved here leaves exactly two independent
geometric existence laws:

1. an actual codimension point at each ghost-selected weight;
2. primitive strict-relation closure for the resulting targeted branch.

Everything else in the plane packet, target normalization, and ghost
contradiction is derived.
-/

set_option maxHeartbeats 180000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeCommonClassPlaneRealization

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeProjectiveDegreeTrace
open GSTClassicalHodgeNativePointSeedSaturation
open GSTClassicalHodgeOmniversalSeparatorGhostCrown
open GSTClassicalHodgeOmniverseCausalBranchPacket
open GSTClassicalHodgeOmniverseStrictRelationRayCompiler
open GSTClassicalHodgeOmniversalGhostBranchClosure
open GSTClassicalHodgeSchemeFiniteCorrespondenceFirewall
open GSTClassicalHodgeStrictCorrespondenceAnalyticSpan
open GSTClassicalHodgeStrictCorrespondenceBettiTracePushPull

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

namespace CommonClassPlanePacket

variable
  {u v : HodgeBranchNode (V := V) (H := H) (p := p)}

/-- **STRICT RELATION -> COMMON-CLASS PLANE.**

The intrinsic common class can be chosen canonically as the left pullback of
the source.  Hence the two face equations are not extra geometric hypotheses
once the strict relation is known. -/
noncomputable def ofStrictRelationEdgePacket
    (R : StrictRelationEdgePacket u v) :
    CommonClassPlanePacket u v where
  correspondence := R.correspondence
  trace := R.trace
  pointCompatibility := R.pointCompatibility
  planeClass :=
    leftCohomologyPullback H.analytification R.correspondence (2 * p)
      u.state.1
  source_face := rfl
  target_face := by
    change
      rightCohomologyPullback H.analytification R.correspondence (2 * p)
          v.state.1 =
        leftCohomologyPullback H.analytification R.correspondence (2 * p)
          u.state.1
    exact R.related.symm

/-- Common-class plane existence is exactly equivalent to raw strict-relation
packet existence for a fixed branch. -/
theorem nonempty_iff_strictRelationEdgePacket :
    Nonempty (CommonClassPlanePacket u v) ↔
      Nonempty (StrictRelationEdgePacket u v) := by
  constructor
  · rintro ⟨P⟩
    exact ⟨P.toStrictRelationEdgePacket⟩
  · rintro ⟨R⟩
    exact ⟨ofStrictRelationEdgePacket R⟩

end CommonClassPlanePacket

/-- **ONE SEED + STRICT CLOSURE CONSTRUCTS THE WHOLE GHOST PLANE STRIKE.**

The live source coordinate is not an additional hypothesis: it is extracted
from the nonzero seed by the existing limitless matrix-unit branch theorem.
The common plane packet is then reconstructed canonically from the strict
relation packet. -/
noncomputable def ghostCommonClassPlaneStrike_of_seed_strictClosure
    (G : GeometricCycleClassSpine V H)
    (E : OmniversalSeparatorGhost G)
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := E.weight))
    (C : PrimitiveStrictRelationCompiler
      (V := V) (H := H) (p := E.weight)) :
    GhostCommonClassPlaneStrike G E := by
  obtain ⟨i, hevent, _hi⟩ :=
    event_to_arbitrary_target
      (V := V) (H := H)
      S.hodge S.hodge_ne_zero Sector.gstPlus E.sheet
  let R : StrictRelationEdgePacket
      (⟨Sector.gstPlus, S.hodge⟩ :
        HodgeBranchNode (V := V) (H := H) (p := E.weight))
      (⟨Sector.gstPlus, hodgeMatrixUnit i.1 E.sheet S.hodge⟩ :
        HodgeBranchNode (V := V) (H := H) (p := E.weight)) :=
    Classical.choice (C hevent)
  exact {
    seed := S
    source := i
    plane := CommonClassPlanePacket.ofStrictRelationEdgePacket R
  }

/-- **PLANE COMPLETENESS HAS ONLY THE TWO CORE EXISTENCE BURDENS.**

Ghost-weight seed survival plus primitive strict-relation closure manufactures
ghost-adaptive common-class plane completeness itself; no independent common
carrier class, source face, target face, live coordinate, operator action, or
target cycle assumption remains. -/
theorem commonClassPlaneCompleteness_of_survival_and_strictClosure
    (G : GeometricCycleClassSpine V H)
    (hsurvive : GhostWeightNativeSeedSurvival G)
    (hclose : GhostWeightPrimitiveStrictClosure G) :
    GhostAdaptiveCommonClassPlaneCompleteness G := by
  intro E
  let S := Classical.choice (hsurvive E)
  exact ⟨ghostCommonClassPlaneStrike_of_seed_strictClosure G E S (hclose E)⟩

/-- **EXACT TWO-LAW REDUCTION OF GST PLANE COMPLETENESS.**

Projective degree strengthens the preceding theorem one layer further.  The
seed-survival package is no longer an input: an actual codimension point at the
ghost weight generates the synchronized nonzero Hodge seed canonically.
Therefore common-class Plane Completeness follows from exactly the two
remaining geometric existence laws visible in this theorem:

* ghost-weight codimension-point existence;
* ghost-weight primitive strict-relation closure.

No target cycle, target algebraicity, Hodge surjectivity, common plane class,
trace normalization equation, or source-action equation is assumed here. -/
theorem commonClassPlaneCompleteness_of_codimensionPoints_and_strictClosure
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (hpoint : ∀ E : OmniversalSeparatorGhost G,
      Nonempty (GSTNativeCodimensionCyclePresentation.CodimensionPoint
        V.X E.weight))
    (hclose : GhostWeightPrimitiveStrictClosure G) :
    GhostAdaptiveCommonClassPlaneCompleteness G := by
  exact commonClassPlaneCompleteness_of_survival_and_strictClosure G
    (ghostWeightNativeSeedSurvival_of_codimensionPoints G D hpoint)
    hclose

#check CommonClassPlanePacket.ofStrictRelationEdgePacket
#check CommonClassPlanePacket.nonempty_iff_strictRelationEdgePacket
#check ghostCommonClassPlaneStrike_of_seed_strictClosure
#check commonClassPlaneCompleteness_of_survival_and_strictClosure
#check commonClassPlaneCompleteness_of_codimensionPoints_and_strictClosure

#print axioms CommonClassPlanePacket.nonempty_iff_strictRelationEdgePacket
#print axioms ghostCommonClassPlaneStrike_of_seed_strictClosure
#print axioms commonClassPlaneCompleteness_of_survival_and_strictClosure
#print axioms commonClassPlaneCompleteness_of_codimensionPoints_and_strictClosure

end GSTClassicalHodgeCommonClassPlaneRealization
