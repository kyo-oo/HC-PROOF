import GSTClassicalHodgePlaneCompletenessMinimality

/-!
# GST CLASSICAL HODGE — CANONICAL GENERATOR PLANE KERNEL

This file removes the last unnecessary quantification from the repaired GST
plane-completeness route.

The omniverse already proves that every primitive Hodge branch event is an
augmented support-plus-target GST matrix unit.  Therefore a geometric compiler
does not need to be postulated for arbitrary pairs of source/target nodes.  It
is enough to materialize the canonical GST generator itself:

  x  -->  augmentedConcreteHodgeMatrixUnit x j i.

The target of an arbitrary primitive event is definitionally one of these
canonical generators.  Raw strict relations are the lowest geometric interface
already present in the repository: their operator action is derived downstream
from right-trace injectivity and relation uniqueness, rather than assumed.

Accordingly this module proves:

* canonical-generator raw relations are exactly equivalent to the full
  primitive strict-relation compiler;
* hence canonical-generator relations are exactly equivalent to primitive
  common-class-plane compilation;
* one live native seed plus the canonical generators yields the minimal
  seed-to-target strict-relation law;
* the all-live-weight version yields the minimal plane law and therefore the
  exact Hodge statement;
* every historical ghost-indexed completeness/closure package is consequently
  derived above this lower kernel rather than used as a foundation.

No target cycle, Hodge surjectivity witness, separator ghost, or edge operator
identity occurs in the canonical-generator hypothesis.
-/

set_option maxHeartbeats 180000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry

namespace GSTClassicalHodgeCanonicalGeneratorPlaneKernel

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeSynchronizedDefectOrbit
open GSTClassicalHodgeOmniversalSeparatorGhostCrown
open GSTClassicalHodgeAugmentedTargetMatrixUnit
open GSTClassicalHodgeOmniverseCausalBranchPacket
open GSTClassicalHodgeOmniverseStrictRelationRayCompiler
open GSTClassicalHodgeCommonClassPlaneRealization
open GSTClassicalHodgePlaneCompletenessNonCircularity
open GSTClassicalHodgePlaneCompletenessMinimality

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-! ## 1. Canonical generator kernel -/

/-- The exact geometric burden for one Hodge weight, stated only on the
canonical GST matrix-unit generators that the omniverse has already
constructed.

There is deliberately no arbitrary target node in this definition and no
operator-action equation.  The packet contains only an actual strict
correspondence, finite trace, point compatibility, and the intrinsic Betti
pullback relation. -/
def CanonicalGSTGeneratorRelationCompleteness : Prop :=
  ∀ (x : HodgeBranchNode (V := V) (H := H) (p := p))
    (j : ClassicalHodgeBasisIndex V H p)
    (i : HodgeSupportIndex x.state),
      Nonempty
        (StrictRelationEdgePacket
          x
          (⟨Sector.gstPlus,
              augmentedConcreteHodgeMatrixUnit x.state j i⟩ :
            HodgeBranchNode (V := V) (H := H) (p := p)))

/-- Any full primitive strict-relation compiler restricts to the canonical GST
generators.  This is the easy necessity direction. -/
theorem canonicalGSTGeneratorRelations_of_primitiveCompiler
    (C : PrimitiveStrictRelationCompiler (V := V) (H := H) (p := p)) :
    CanonicalGSTGeneratorRelationCompleteness
      (V := V) (H := H) (p := p) := by
  intro x j i
  let y : HodgeBranchNode (V := V) (H := H) (p := p) :=
    ⟨Sector.gstPlus, augmentedConcreteHodgeMatrixUnit x.state j i⟩
  have hevent : HodgeBranchEvent x y := by
    exact ⟨j, i, rfl⟩
  simpa [y] using C hevent

/-- **CANONICAL GENERATORS COMPILE EVERY PRIMITIVE EVENT.**

A primitive event already carries witnesses `j,i` and an equality saying that
its target state is the canonical augmented GST generator.  Rebuild the raw
strict-relation packet with that equality substituted into its right face.
No new geometry or action law is introduced. -/
theorem primitiveCompiler_of_canonicalGSTGeneratorRelations
    (C : CanonicalGSTGeneratorRelationCompleteness
      (V := V) (H := H) (p := p)) :
    PrimitiveStrictRelationCompiler (V := V) (H := H) (p := p) := by
  intro u v huv
  rcases huv with ⟨j, i, hv⟩
  obtain ⟨R⟩ := C u j i
  refine ⟨{
    correspondence := R.correspondence
    trace := R.trace
    pointCompatibility := R.pointCompatibility
    related := ?_
  }⟩
  simpa [hv] using R.related

/-- **EXACT GENERATOR REDUCTION.**
The apparently stronger assertion that every primitive omniverse edge carries a
raw strict relation has precisely the same existence strength as relations on
the canonical augmented GST generators alone. -/
theorem canonicalGSTGeneratorRelations_iff_primitiveCompiler :
    CanonicalGSTGeneratorRelationCompleteness
        (V := V) (H := H) (p := p) ↔
      PrimitiveStrictRelationCompiler (V := V) (H := H) (p := p) := by
  constructor
  · exact primitiveCompiler_of_canonicalGSTGeneratorRelations
  · exact canonicalGSTGeneratorRelations_of_primitiveCompiler

/-- The canonical generator kernel is also exactly equivalent to eventwise
common-class-plane compilation.  The plane class itself therefore contributes
no hidden foundational strength: it is a theorem-level presentation of the
same raw relation kernel. -/
theorem canonicalGSTGeneratorRelations_iff_commonClassPlaneCompiler :
    CanonicalGSTGeneratorRelationCompleteness
        (V := V) (H := H) (p := p) ↔
      PrimitiveCommonClassPlaneCompiler (V := V) (H := H) (p := p) :=
  canonicalGSTGeneratorRelations_iff_primitiveCompiler.trans
    primitiveCommonClassPlaneCompiler_iff_strictRelationCompiler.symm

/-! ## 2. Exact seed-to-target reduction -/

/-- One synchronized nonzero native/Hodge seed plus the canonical generator
kernel yields every strict relation actually consumed by basis reconstruction.
The GST event itself is theorem-level (`event_to_arbitrary_target`). -/
theorem seedTargetStrictRelations_of_canonicalGSTGenerators
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (C : CanonicalGSTGeneratorRelationCompleteness
      (V := V) (H := H) (p := p)) :
    SeedTargetStrictRelationCompleteness S := by
  let P : PrimitiveStrictRelationCompiler (V := V) (H := H) (p := p) :=
    primitiveCompiler_of_canonicalGSTGeneratorRelations C
  intro j
  obtain ⟨i, hevent, _hi⟩ :=
    event_to_arbitrary_target
      (V := V) (H := H)
      S.hodge S.hodge_ne_zero Sector.gstPlus j
  exact ⟨i, hevent, P hevent⟩

/-- The same canonical generator kernel therefore gives the common-class plane
family, but only as a derived presentation of the strict relations. -/
theorem seedTargetCommonClassPlanes_of_canonicalGSTGenerators
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (C : CanonicalGSTGeneratorRelationCompleteness
      (V := V) (H := H) (p := p)) :
    SeedTargetCommonClassPlaneCompleteness S := by
  exact
    (seedTargetCommonClassPlanes_iff_strictRelations S).2
      (seedTargetStrictRelations_of_canonicalGSTGenerators S C)

/-! ## 3. Live-weight kernel and direct finale -/

/-- Canonical generator materialization is required only in a genuinely live
Hodge weight.  Dead weights need no source and no geometric spokes. -/
def LiveWeightCanonicalGSTGeneratorRelationCompleteness : Prop :=
  ∀ q : Nat,
    rationalHodgeSubspace (H.hodgeBigrading q) ≠ ⊥ →
      CanonicalGSTGeneratorRelationCompleteness
        (V := V) (H := H) (p := q)

/-- The two irreducible noncircular ingredients -- a genuine synchronized
source in each live weight and raw relations on canonical GST generators --
derive the minimal seed-to-target strict-relation completeness law. -/
theorem liveWeightSeedTargetStrictRelations_of_nativeSeeds_and_canonicalGenerators
    (S : LiveWeightNativeSeedExistence (V := V) (H := H))
    (C : LiveWeightCanonicalGSTGeneratorRelationCompleteness
      (V := V) (H := H)) :
    LiveWeightSeedTargetStrictRelationCompleteness (V := V) (H := H) := by
  intro q hq
  obtain ⟨seed⟩ := S q hq
  exact
    ⟨seed,
      seedTargetStrictRelations_of_canonicalGSTGenerators
        seed (C q hq)⟩

/-- Consequently the minimal common-class plane law is a theorem above the
canonical generator relation kernel. -/
theorem liveWeightSeedTargetCommonClassPlanes_of_nativeSeeds_and_canonicalGenerators
    (S : LiveWeightNativeSeedExistence (V := V) (H := H))
    (C : LiveWeightCanonicalGSTGeneratorRelationCompleteness
      (V := V) (H := H)) :
    LiveWeightSeedTargetCommonClassPlaneCompleteness (V := V) (H := H) := by
  exact
    (liveWeightSeedTargetCommonClassPlanes_iff_strictRelations
      (V := V) (H := H)).2
      (liveWeightSeedTargetStrictRelations_of_nativeSeeds_and_canonicalGenerators
        S C)

/-- **CANONICAL GENERATOR GST PLANE FINALE.**

No plane-completeness axiom remains in the premise.  The proof consumes only
(1) a true synchronized native source in each live weight and (2) raw strict
relations for the canonical augmented GST generators.  All target planes,
operator actions, target cycles, and basis reconstruction are derived by the
existing omniverse/correspondence compilers. -/
theorem hodge_of_nativeSeeds_and_canonicalGSTGenerators
    (S : LiveWeightNativeSeedExistence (V := V) (H := H))
    (C : LiveWeightCanonicalGSTGeneratorRelationCompleteness
      (V := V) (H := H)) :
    BigradedBettiHodgeStatement V H := by
  exact
    hodge_of_liveWeightSeedTargetStrictRelations
      (liveWeightSeedTargetStrictRelations_of_nativeSeeds_and_canonicalGenerators
        S C)

/-! ## 4. Historical completeness packages become consequences -/

/-- The old ghost-adaptive plane package is now derived strictly above the
canonical relation kernel. -/
theorem ghostAdaptiveCommonClassPlanes_of_nativeSeeds_and_canonicalGenerators
    (G : GeometricCycleClassSpine V H)
    (S : LiveWeightNativeSeedExistence (V := V) (H := H))
    (C : LiveWeightCanonicalGSTGeneratorRelationCompleteness
      (V := V) (H := H)) :
    GhostAdaptiveCommonClassPlaneCompleteness G := by
  exact
    ghostAdaptiveCommonClassPlaneCompleteness_of_minimalPlanes G
      (liveWeightSeedTargetCommonClassPlanes_of_nativeSeeds_and_canonicalGenerators
        S C)

/-- Separator ghosts are eliminated as a theorem, not used as an index for a
foundational completeness assumption. -/
theorem no_omniversalSeparatorGhost_of_nativeSeeds_and_canonicalGenerators
    (G : GeometricCycleClassSpine V H)
    (S : LiveWeightNativeSeedExistence (V := V) (H := H))
    (C : LiveWeightCanonicalGSTGeneratorRelationCompleteness
      (V := V) (H := H)) :
    IsEmpty (OmniversalSeparatorGhost G) := by
  exact
    no_omniversalSeparatorGhost_of_minimalPlanes G
      (liveWeightSeedTargetCommonClassPlanes_of_nativeSeeds_and_canonicalGenerators
        S C)

/-- Historical ghost-weight native survival is vacuous only *after* the lower
canonical generator geometry has proved ghost extinction. -/
theorem ghostWeightNativeSeedSurvival_of_nativeSeeds_and_canonicalGenerators
    (G : GeometricCycleClassSpine V H)
    (S : LiveWeightNativeSeedExistence (V := V) (H := H))
    (C : LiveWeightCanonicalGSTGeneratorRelationCompleteness
      (V := V) (H := H)) :
    GhostWeightNativeSeedSurvival G := by
  exact
    ghostWeightNativeSeedSurvival_of_minimalPlanes G
      (liveWeightSeedTargetCommonClassPlanes_of_nativeSeeds_and_canonicalGenerators
        S C)

/-- Historical ghost-weight strict closure is likewise derived. -/
theorem ghostWeightPrimitiveStrictClosure_of_nativeSeeds_and_canonicalGenerators
    (G : GeometricCycleClassSpine V H)
    (S : LiveWeightNativeSeedExistence (V := V) (H := H))
    (C : LiveWeightCanonicalGSTGeneratorRelationCompleteness
      (V := V) (H := H)) :
    GhostWeightPrimitiveStrictClosure G := by
  exact
    ghostWeightPrimitiveStrictClosure_of_minimalPlanes G
      (liveWeightSeedTargetCommonClassPlanes_of_nativeSeeds_and_canonicalGenerators
        S C)

/-- Historical ghost-weight common-class closure is likewise derived. -/
theorem ghostWeightPrimitiveCommonClassClosure_of_nativeSeeds_and_canonicalGenerators
    (G : GeometricCycleClassSpine V H)
    (S : LiveWeightNativeSeedExistence (V := V) (H := H))
    (C : LiveWeightCanonicalGSTGeneratorRelationCompleteness
      (V := V) (H := H)) :
    GhostWeightPrimitiveCommonClassClosure G := by
  exact
    ghostWeightPrimitiveCommonClassClosure_of_minimalPlanes G
      (liveWeightSeedTargetCommonClassPlanes_of_nativeSeeds_and_canonicalGenerators
        S C)

/-! ## 5. Necessity firewall -/

/-- A live zero-cycle-class semantic model cannot satisfy the combined lower
kernel.  In particular the source half of the kernel is genuinely geometric
and cannot be manufactured from unconstrained Stage-2G semantics. -/
theorem not_nativeSeeds_and_canonicalGenerators_of_live_zeroCycleClass
    (q : Nat)
    (alpha : RationalSingularCohomology H.analytification (2 * q))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading q))
    (halpha_ne : alpha ≠ 0)
    (hzero : H.cycleClass q = 0) :
    ¬ (LiveWeightNativeSeedExistence (V := V) (H := H) ∧
       LiveWeightCanonicalGSTGeneratorRelationCompleteness
         (V := V) (H := H)) := by
  rintro ⟨S, _C⟩
  exact
    not_liveWeightNativeSeedExistence_of_live_zeroCycleClass
      q alpha halpha halpha_ne hzero S

#check CanonicalGSTGeneratorRelationCompleteness
#check canonicalGSTGeneratorRelations_of_primitiveCompiler
#check primitiveCompiler_of_canonicalGSTGeneratorRelations
#check canonicalGSTGeneratorRelations_iff_primitiveCompiler
#check canonicalGSTGeneratorRelations_iff_commonClassPlaneCompiler
#check seedTargetStrictRelations_of_canonicalGSTGenerators
#check seedTargetCommonClassPlanes_of_canonicalGSTGenerators
#check LiveWeightCanonicalGSTGeneratorRelationCompleteness
#check liveWeightSeedTargetStrictRelations_of_nativeSeeds_and_canonicalGenerators
#check liveWeightSeedTargetCommonClassPlanes_of_nativeSeeds_and_canonicalGenerators
#check hodge_of_nativeSeeds_and_canonicalGSTGenerators
#check ghostAdaptiveCommonClassPlanes_of_nativeSeeds_and_canonicalGenerators
#check no_omniversalSeparatorGhost_of_nativeSeeds_and_canonicalGenerators
#check ghostWeightNativeSeedSurvival_of_nativeSeeds_and_canonicalGenerators
#check ghostWeightPrimitiveStrictClosure_of_nativeSeeds_and_canonicalGenerators
#check ghostWeightPrimitiveCommonClassClosure_of_nativeSeeds_and_canonicalGenerators
#check not_nativeSeeds_and_canonicalGenerators_of_live_zeroCycleClass

#print axioms canonicalGSTGeneratorRelations_iff_primitiveCompiler
#print axioms canonicalGSTGeneratorRelations_iff_commonClassPlaneCompiler
#print axioms seedTargetStrictRelations_of_canonicalGSTGenerators
#print axioms hodge_of_nativeSeeds_and_canonicalGSTGenerators
#print axioms ghostAdaptiveCommonClassPlanes_of_nativeSeeds_and_canonicalGenerators
#print axioms not_nativeSeeds_and_canonicalGenerators_of_live_zeroCycleClass

end GSTClassicalHodgeCanonicalGeneratorPlaneKernel
