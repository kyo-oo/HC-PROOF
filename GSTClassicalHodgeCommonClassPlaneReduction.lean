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
relation geometry.  A nonzero synchronized seed already contains a canonical
live source coordinate.  We therefore do not need a compiler for every causal
event: one strict relation from that canonical source to the single ghost
sheet is sufficient.  Projective degree removes the Hodge/nonzero fields from
the seed packet as well: once an actual codimension point exists at the ghost
weight, the genuine cycle-class spine makes its class Hodge and positive
projective degree makes that class nonzero.

Thus the strongest reduction proved here leaves exactly two genuinely
independent geometric existence laws:

1. an actual codimension point at each ghost-selected weight;
2. one strict source-to-ghost relation packet for the resulting canonical
   nonzero seed.

Everything else in the old plane packet, event fan, target normalization, and
ghost contradiction is derived.
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
open GSTClassicalHodgeConcreteRankFreeGeneration
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeProjectiveDegreeTrace
open GSTClassicalHodgeNativePointSeedSaturation
open GSTClassicalHodgeSynchronizedDefectOrbit
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

/-- **ONE SEED + UNIVERSAL STRICT CLOSURE CONSTRUCTS A GHOST PLANE STRIKE.**

This compatibility theorem keeps the older all-event compiler available, but
it is intentionally no longer the minimal interface below. -/
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

/-- **MINIMAL GHOST-TARGET STRICT CLOSURE.**

For each hypothetical ghost and each nonzero synchronized seed at its weight,
require only the one strict relation packet from the seed's canonical live
source coordinate to the sheet selected by that ghost.  No all-event fan or
causal-branch compiler is quantified here. -/
def GhostSeedTargetStrictClosure
    (G : GeometricCycleClassSpine V H) : Prop :=
  ∀ (E : OmniversalSeparatorGhost G)
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := E.weight)),
    Nonempty
      (StrictRelationEdgePacket
        (⟨Sector.gstPlus, S.hodge⟩ :
          HodgeBranchNode (V := V) (H := H) (p := E.weight))
        (⟨Sector.gstPlus,
          hodgeMatrixUnit S.sourceIndex E.sheet S.hodge⟩ :
          HodgeBranchNode (V := V) (H := H) (p := E.weight)))

/-- One canonical seed-target strict packet directly manufactures the entire
common-class plane strike.  The source support witness is already carried by
`chosenLiveSource`; no event search is needed. -/
noncomputable def ghostCommonClassPlaneStrike_of_seed_targetStrictClosure
    (G : GeometricCycleClassSpine V H)
    (E : OmniversalSeparatorGhost G)
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := E.weight))
    (C : GhostSeedTargetStrictClosure G) :
    GhostCommonClassPlaneStrike G E := by
  let i : HodgeSupportIndex S.hodge :=
    chosenLiveSource S.hodge S.hodge_ne_zero
  let R0 := Classical.choice (C E S)
  let R : StrictRelationEdgePacket
      (⟨Sector.gstPlus, S.hodge⟩ :
        HodgeBranchNode (V := V) (H := H) (p := E.weight))
      (⟨Sector.gstPlus, hodgeMatrixUnit i.1 E.sheet S.hodge⟩ :
        HodgeBranchNode (V := V) (H := H) (p := E.weight)) := by
    simpa [i, NativeHodgeOrbitSeed.sourceIndex] using R0
  exact {
    seed := S
    source := i
    plane := CommonClassPlanePacket.ofStrictRelationEdgePacket R
  }

/-- Ghost-weight seed survival plus the minimal one-target closure is enough
for Plane Completeness. -/
theorem commonClassPlaneCompleteness_of_survival_and_targetStrictClosure
    (G : GeometricCycleClassSpine V H)
    (hsurvive : GhostWeightNativeSeedSurvival G)
    (hclose : GhostSeedTargetStrictClosure G) :
    GhostAdaptiveCommonClassPlaneCompleteness G := by
  intro E
  let S := Classical.choice (hsurvive E)
  exact ⟨ghostCommonClassPlaneStrike_of_seed_targetStrictClosure G E S hclose⟩

/-- Compatibility with the older, stronger all-event closure theorem. -/
theorem commonClassPlaneCompleteness_of_survival_and_strictClosure
    (G : GeometricCycleClassSpine V H)
    (hsurvive : GhostWeightNativeSeedSurvival G)
    (hclose : GhostWeightPrimitiveStrictClosure G) :
    GhostAdaptiveCommonClassPlaneCompleteness G := by
  intro E
  let S := Classical.choice (hsurvive E)
  exact ⟨ghostCommonClassPlaneStrike_of_seed_strictClosure G E S (hclose E)⟩

/-- **EXACT TWO-LAW REDUCTION OF GST PLANE COMPLETENESS.**

Projective degree removes Hodge type and nonvanishing from the seed burden.
The universal primitive-event compiler is also removed.  The two remaining
independent geometric laws are now visible literally in the theorem
signature:

* existence of one actual codimension point at every ghost-selected weight;
* existence of the one canonical source-to-ghost strict relation packet.

No target cycle, target algebraicity, Hodge surjectivity, common plane class,
all-event fan, trace normalization equation, or supplied source-action equation
is assumed. -/
theorem commonClassPlaneCompleteness_of_codimensionPoints_and_targetStrictClosure
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (hpoint : ∀ E : OmniversalSeparatorGhost G,
      Nonempty (GSTNativeCodimensionCyclePresentation.CodimensionPoint
        V.X E.weight))
    (hclose : GhostSeedTargetStrictClosure G) :
    GhostAdaptiveCommonClassPlaneCompleteness G := by
  exact commonClassPlaneCompleteness_of_survival_and_targetStrictClosure G
    (ghostWeightNativeSeedSurvival_of_codimensionPoints G D hpoint)
    hclose

/-- Older stronger closure retained as a corollary. -/
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
#check GhostSeedTargetStrictClosure
#check ghostCommonClassPlaneStrike_of_seed_targetStrictClosure
#check commonClassPlaneCompleteness_of_survival_and_targetStrictClosure
#check commonClassPlaneCompleteness_of_codimensionPoints_and_targetStrictClosure

#print axioms CommonClassPlanePacket.nonempty_iff_strictRelationEdgePacket
#print axioms ghostCommonClassPlaneStrike_of_seed_targetStrictClosure
#print axioms commonClassPlaneCompleteness_of_survival_and_targetStrictClosure
#print axioms commonClassPlaneCompleteness_of_codimensionPoints_and_targetStrictClosure

end GSTClassicalHodgeCommonClassPlaneRealization
