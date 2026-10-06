import GSTClassicalHodgeCommonClassPlaneRealization
import GSTClassicalHodgeNativePointSeedDegreeUpgrade
import GSTClassicalHodgeCodimensionPointTower

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
the seed packet as well.

The canonical codimension-zero apex plus a uniform native principal-cut
survival HYPOTHESIS recursively generates an actual codimension-p point at
every finite weight.  The tower does not prove that survival hypothesis.
`nativeCutSearch` now constructs a finite path or a certified stopped cut
without it.  The strict target packet and positive-degree semantics below
also remain explicit premises, not established existence theorems.
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
open GSTClassicalHodgeCodimensionPointTower

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

/-- **A SURVIVING GHOST FORBIDS THE REQUESTED STRICT BRANCH PACKET.**

This is the exact negative face of the branch-packet plane realization law.
Fix a hypothetical omniversal ghost and an already genuine synchronized native
seed in the ghost's weight.  There cannot exist the strict relation packet from
the seed's canonical live GST source to the matrix-unit target detected by the
ghost: such a packet canonically gives a common-class plane strike, whose
normalized native target cycle is the detected basis sheet, contradicting the
ghost detector.

Thus the missing realization theorem is located at precisely the contradiction
point, with no intermediate Hodge-shaped wrapper. -/
theorem ghostSeedTargetStrictPacket_isEmpty
    (G : GeometricCycleClassSpine V H)
    (E : OmniversalSeparatorGhost G)
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := E.weight)) :
    IsEmpty
      (StrictRelationEdgePacket
        (⟨Sector.gstPlus, S.hodge⟩ :
          HodgeBranchNode (V := V) (H := H) (p := E.weight))
        (⟨Sector.gstPlus,
          hodgeMatrixUnit S.sourceIndex E.sheet S.hodge⟩ :
          HodgeBranchNode (V := V) (H := H) (p := E.weight))) := by
  refine ⟨?_⟩
  intro R
  let i : HodgeSupportIndex S.hodge :=
    chosenLiveSource S.hodge S.hodge_ne_zero
  have hRi :
      StrictRelationEdgePacket
        (⟨Sector.gstPlus, S.hodge⟩ :
          HodgeBranchNode (V := V) (H := H) (p := E.weight))
        (⟨Sector.gstPlus,
          hodgeMatrixUnit i.1 E.sheet S.hodge⟩ :
          HodgeBranchNode (V := V) (H := H) (p := E.weight)) := by
    simpa [i, NativeHodgeOrbitSeed.sourceIndex] using R
  let P : GhostCommonClassPlaneStrike G E := {
    seed := S
    source := i
    plane := CommonClassPlanePacket.ofStrictRelationEdgePacket hRi
  }
  exact P.contradiction

/-- **BRANCH-PACKET REALIZATION = NO-GHOST, ONCE THE NATIVE SOURCE EXISTS.**

This is the exact logical form of the handwritten GST plane derivation.
With ghost-weight native seed survival fixed, the sole remaining statement
`GhostSeedTargetStrictClosure` is equivalent to extinction of every
omniversal separator ghost.

Forward: choose the genuine seed at a hypothetical ghost weight, realize the
single source-to-detected-sheet strict packet, convert it to a common-carrier
plane, and invoke the already-proved one-plane contradiction.
Backward: when no ghost exists, the ghost-indexed strict-closure statement is
vacuous.

No Hodge statement occurs in this equivalence. -/
theorem targetStrictClosure_iff_noGhost_of_survival
    (G : GeometricCycleClassSpine V H)
    (hsurvive : GhostWeightNativeSeedSurvival G) :
    GhostSeedTargetStrictClosure G ↔
      IsEmpty (OmniversalSeparatorGhost G) := by
  constructor
  · intro hclose
    exact no_omniversalSeparatorGhost_of_commonClassPlanes G
      (commonClassPlaneCompleteness_of_survival_and_targetStrictClosure
        G hsurvive hclose)
  · intro hnone E S
    exact False.elim (isEmpty_iff.mp hnone E)

/-- **EXACT STATUS OF THE MINIMAL BRANCH-PACKET REALIZATION LAW.**

Once the source side is the already-existing ghost-weight native-seed survival
law, the genuinely minimal target-side statement is exactly
`GhostSeedTargetStrictClosure`: for the one canonical live source and the one
sheet detected by a hypothetical ghost, construct the strict correspondence
packet whose carrier pullbacks identify the GST branch faces.

This theorem proves that this two-piece package is not merely another compiler
waiting to be wired.  It is equivalent to the Stage-2G Hodge conclusion.
The forward implication is the branch-packet derivation:
strict packet -> common carrier plane -> exact target cycle -> no ghost -> Hodge.
The reverse implication is vacuous because Hodge leaves no ghost to quantify
over.  Thus any unconditional proof of the requested branch-packet plane
realization law is precisely the new mathematical content that closes Hodge;
it cannot be recovered by rearranging the already-green downstream wrappers. -/
theorem survival_and_targetStrictClosure_iff_hodge
    (G : GeometricCycleClassSpine V H) :
    (GhostWeightNativeSeedSurvival G ∧ GhostSeedTargetStrictClosure G) ↔
      BigradedBettiHodgeStatement V H := by
  constructor
  · rintro ⟨hsurvive, hclose⟩
    exact hodge_of_commonClassPlanes G
      (commonClassPlaneCompleteness_of_survival_and_targetStrictClosure
        G hsurvive hclose)
  · intro hHodge
    have hnone : IsEmpty (OmniversalSeparatorGhost G) :=
      (hodge_iff_no_omniversalSeparatorGhost G).1 hHodge
    constructor
    · intro E
      exact False.elim (isEmpty_iff.mp hnone E)
    · intro E S
      exact False.elim (isEmpty_iff.mp hnone E)

/-- Compatibility with the older, stronger all-event closure theorem. -/
theorem commonClassPlaneCompleteness_of_survival_and_strictClosure
    (G : GeometricCycleClassSpine V H)
    (hsurvive : GhostWeightNativeSeedSurvival G)
    (hclose : GhostWeightPrimitiveStrictClosure G) :
    GhostAdaptiveCommonClassPlaneCompleteness G := by
  intro E
  let S := Classical.choice (hsurvive E)
  exact ⟨ghostCommonClassPlaneStrike_of_seed_strictClosure G E S (hclose E)⟩

/-- **TWO-LAW REDUCTION WITH GHOST-INDEXED POINT EXISTENCE.**

Projective degree removes Hodge type and nonvanishing from the seed burden.
The universal primitive-event compiler is also removed.  This compatibility
form keeps the older point-existence interface. -/
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

/-- **CONDITIONAL UNIFORM-TOWER PLANE-COMPLETENESS REDUCTION.**

The ghost-indexed point-existence premise is replaced by a uniform survival
premise; it is not proved or eliminated.  The canonical codimension-zero apex
and this premise construct points at every finite weight.  This interface
requires:

* projective-degree trace semantics, used solely to certify nonvanishing of the
  genuine point-cycle seed;
* the uniform native principal-cut successor nonvanishing law;
* the one canonical source-to-ghost strict relation packet.

No ghost-indexed point-existence axiom, target cycle, target algebraicity,
all-event fan, common plane class, source-action equation, or Hodge conclusion
is supplied. -/
theorem commonClassPlaneCompleteness_of_nativePointTower_and_targetStrictClosure
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    [Nonempty V.X]
    (hstep : NativePointSuccessorNonvanishing V)
    (hclose : GhostSeedTargetStrictClosure G) :
    GhostAdaptiveCommonClassPlaneCompleteness G := by
  apply commonClassPlaneCompleteness_of_codimensionPoints_and_targetStrictClosure
    G D
  · exact ghostCodimensionPoints_of_nativePointSuccessorNonvanishing G hstep
  · exact hclose

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

#check targetStrictClosure_iff_noGhost_of_survival
#check ghostSeedTargetStrictPacket_isEmpty
#check survival_and_targetStrictClosure_iff_hodge
#check CommonClassPlanePacket.ofStrictRelationEdgePacket
#check CommonClassPlanePacket.nonempty_iff_strictRelationEdgePacket
#check GhostSeedTargetStrictClosure
#check ghostCommonClassPlaneStrike_of_seed_targetStrictClosure
#check commonClassPlaneCompleteness_of_survival_and_targetStrictClosure
#check commonClassPlaneCompleteness_of_codimensionPoints_and_targetStrictClosure
#check commonClassPlaneCompleteness_of_nativePointTower_and_targetStrictClosure

#print axioms targetStrictClosure_iff_noGhost_of_survival
#print axioms ghostSeedTargetStrictPacket_isEmpty
#print axioms survival_and_targetStrictClosure_iff_hodge
#print axioms CommonClassPlanePacket.nonempty_iff_strictRelationEdgePacket
#print axioms ghostCommonClassPlaneStrike_of_seed_targetStrictClosure
#print axioms commonClassPlaneCompleteness_of_survival_and_targetStrictClosure
#print axioms commonClassPlaneCompleteness_of_codimensionPoints_and_targetStrictClosure
#print axioms commonClassPlaneCompleteness_of_nativePointTower_and_targetStrictClosure

end GSTClassicalHodgeCommonClassPlaneRealization
