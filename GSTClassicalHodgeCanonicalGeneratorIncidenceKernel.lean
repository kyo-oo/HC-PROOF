import GSTClassicalHodgeCanonicalGeneratorPlaneKernel
import GSTClassicalHodgePrimitiveIncidencePlaneCompleteness

/-!
# GST CLASSICAL HODGE — CANONICAL GENERATOR INCIDENCE KERNEL

The previous primitive-incidence route still stated its global geometric input
as a compiler for every primitive omniverse event.  That quantification is not
fundamental.  By definition every primitive event already factors through one
canonical augmented GST matrix-unit generator.

This file lowers the public incidence boundary to exactly those generators.
For a node `x`, target basis address `j`, and live support address `i`, the only
local obligation is to materialize

  augmentedConcreteHodgeMatrixUnit x.state j i

by the repository's genuine bi-finite correspondence / Betti-kernel /
point-incidence packet `StrictlyMaterializedBranch`.

The arbitrary-event compiler is reconstructed from this canonical kernel by
substituting the event's theorem-level target equality.  Conversely, any old
arbitrary-event compiler restricts to the canonical generators, so the two
forms are exactly equivalent.

At the all-weight level the source premise is also removed whenever the
existing conserved-spine or native-mass cosmology is supplied: those modules
already construct the synchronized nonzero native/Hodge seed.  Thus the only
new local geometric task left by this file is the canonical GST generator
incidence realization itself.
-/

set_option maxHeartbeats 180000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry

namespace GSTClassicalHodgeCanonicalGeneratorIncidenceKernel

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
open GSTClassicalHodgeOmniverseStrictEventStability
open GSTClassicalHodgePlaneCompletenessMinimality
open GSTClassicalHodgePrimitiveIncidencePlaneCompleteness

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-! ## 1. Canonical primitive-incidence kernel -/

/-- Primitive incidence materialization only for the canonical GST generators.

Unlike the old eventwise statement there is no arbitrary target `y`; unlike a
strict-relation packet there is no supplied finite trace or `BettiRelated`
relation.  The witness is exactly the low-level incidence packet already used
by `StrictlyMaterializedBranch`. -/
def CanonicalGSTGeneratorPrimitiveIncidenceCompleteness : Prop :=
  ∀ (x : HodgeBranchNode (V := V) (H := H) (p := p))
    (j : ClassicalHodgeBasisIndex V H p)
    (i : HodgeSupportIndex x.state),
      StrictlyMaterializedBranch
        x
        (⟨Sector.gstPlus,
            augmentedConcreteHodgeMatrixUnit x.state j i⟩ :
          HodgeBranchNode (V := V) (H := H) (p := p))

/-- Restriction of an arbitrary-event incidence compiler to the canonical GST
generators. -/
theorem canonicalPrimitiveIncidence_of_eventMaterialization
    (M : ∀ {x y : HodgeBranchNode (V := V) (H := H) (p := p)},
      HodgeBranchEvent x y → StrictlyMaterializedBranch x y) :
    CanonicalGSTGeneratorPrimitiveIncidenceCompleteness
      (V := V) (H := H) (p := p) := by
  intro x j i
  let y : HodgeBranchNode (V := V) (H := H) (p := p) :=
    ⟨Sector.gstPlus, augmentedConcreteHodgeMatrixUnit x.state j i⟩
  have hevent : HodgeBranchEvent x y := by
    exact ⟨j, i, rfl⟩
  simpa [y] using M hevent

/-- **CANONICAL INCIDENCE -> EVERY PRIMITIVE EVENT.**

The event witness itself supplies the equality from the arbitrary target state
to its canonical augmented generator.  Substitute that theorem into the final
action face of the independently built incidence packet.  All geometric data
are reused unchanged. -/
theorem eventMaterialization_of_canonicalPrimitiveIncidence
    (C : CanonicalGSTGeneratorPrimitiveIncidenceCompleteness
      (V := V) (H := H) (p := p)) :
    ∀ {x y : HodgeBranchNode (V := V) (H := H) (p := p)},
      HodgeBranchEvent x y → StrictlyMaterializedBranch x y := by
  intro x y hxy
  rcases hxy with ⟨j, i, hy⟩
  rcases C x j i with ⟨d, P, K, kappa, pt, hpoint, I, haction⟩
  refine ⟨d, P, K, kappa, pt, hpoint, I, ?_⟩
  rw [hy]
  exact haction

/-- **EXACT INCIDENCE REDUCTION.**
Quantifying over all primitive event targets has no additional mathematical
strength.  It is exactly the same proposition as materializing the canonical
augmented GST generators. -/
theorem canonicalPrimitiveIncidence_iff_eventMaterialization :
    CanonicalGSTGeneratorPrimitiveIncidenceCompleteness
        (V := V) (H := H) (p := p) ↔
      (∀ {x y : HodgeBranchNode (V := V) (H := H) (p := p)},
        HodgeBranchEvent x y → StrictlyMaterializedBranch x y) := by
  constructor
  · exact eventMaterialization_of_canonicalPrimitiveIncidence
  · exact canonicalPrimitiveIncidence_of_eventMaterialization

/-! ## 2. Seed-target planes are derived from the canonical kernel -/

/-- For one synchronized native/Hodge seed, the canonical incidence kernel
produces exactly the target star used by basis reconstruction. -/
theorem seedTargetPrimitiveIncidencePlanes_of_canonicalGenerators
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (C : CanonicalGSTGeneratorPrimitiveIncidenceCompleteness
      (V := V) (H := H) (p := p)) :
    SeedTargetPrimitiveIncidencePlaneCompleteness S := by
  exact
    seedTargetPrimitiveIncidencePlanes_of_eventMaterialization S
      (eventMaterialization_of_canonicalPrimitiveIncidence C)

/-- Direct fixed-weight Hodge range from one true source and canonical
primitive-incidence materialization. -/
theorem hodge_weight_of_seed_and_canonicalPrimitiveIncidence
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (C : CanonicalGSTGeneratorPrimitiveIncidenceCompleteness
      (V := V) (H := H) (p := p)) :
    rationalHodgeSubspace (H.hodgeBigrading p) ≤
      LinearMap.range (H.cycleClass p) := by
  exact
    hodge_weight_of_seedTargetPrimitiveIncidencePlanes S
      (seedTargetPrimitiveIncidencePlanes_of_canonicalGenerators S C)

/-! ## 3. Minimal all-weight canonical incidence law -/

/-- Canonical primitive-incidence materialization is needed only in live Hodge
weights. -/
def LiveWeightCanonicalGSTGeneratorPrimitiveIncidenceCompleteness : Prop :=
  ∀ q : Nat,
    rationalHodgeSubspace (H.hodgeBigrading q) ≠ ⊥ →
      CanonicalGSTGeneratorPrimitiveIncidenceCompleteness
        (V := V) (H := H) (p := q)

/-- Live sources plus the canonical incidence kernel derive the complete
minimal primitive-incidence plane law.  Thus the latter is not foundational. -/
theorem liveWeightPrimitiveIncidencePlanes_of_nativeSeeds_and_canonicalGenerators
    (S : LiveWeightNativeSeedExistence (V := V) (H := H))
    (C : LiveWeightCanonicalGSTGeneratorPrimitiveIncidenceCompleteness
      (V := V) (H := H)) :
    LiveWeightSeedTargetPrimitiveIncidencePlaneCompleteness
      (V := V) (H := H) := by
  intro q hq
  obtain ⟨seed⟩ := S q hq
  exact
    ⟨seed,
      seedTargetPrimitiveIncidencePlanes_of_canonicalGenerators
        seed (C q hq)⟩

/-- **CANONICAL PRIMITIVE-INCIDENCE GST PLANE FINALE.** -/
theorem hodge_of_nativeSeeds_and_canonicalPrimitiveIncidence
    (S : LiveWeightNativeSeedExistence (V := V) (H := H))
    (C : LiveWeightCanonicalGSTGeneratorPrimitiveIncidenceCompleteness
      (V := V) (H := H)) :
    BigradedBettiHodgeStatement V H := by
  exact
    hodge_of_liveWeightSeedTargetPrimitiveIncidencePlanes
      (liveWeightPrimitiveIncidencePlanes_of_nativeSeeds_and_canonicalGenerators
        S C)

/-! ## 4. Existing omniverse cosmology removes the source axiom -/

/-- **CONSERVED-SPINE CANONICAL INCIDENCE FINALE.**
The live source is not assumed: the existing conserved GST spine constructs it
in every live weight.  Canonical generator incidence materialization is the
only remaining local geometric interface in this theorem. -/
theorem hodge_of_conservedSpine_and_canonicalPrimitiveIncidence
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge G)
    (C : LiveWeightCanonicalGSTGeneratorPrimitiveIncidenceCompleteness
      (V := V) (H := H)) :
    BigradedBettiHodgeStatement V H := by
  exact
    hodge_of_nativeSeeds_and_canonicalPrimitiveIncidence
      (liveWeightNativeSeedExistence_of_conservedSpine G D) C

/-- **NATIVE-MASS CANONICAL INCIDENCE FINALE.**
The native-mass bridge already implies the conserved charge and therefore the
live synchronized source. -/
theorem hodge_of_nativeMass_and_canonicalPrimitiveIncidence
    (G : GeometricCycleClassSpine V H)
    (N : NativeMassCycleClassBridge V H)
    (C : LiveWeightCanonicalGSTGeneratorPrimitiveIncidenceCompleteness
      (V := V) (H := H)) :
    BigradedBettiHodgeStatement V H := by
  exact
    hodge_of_nativeSeeds_and_canonicalPrimitiveIncidence
      (liveWeightNativeSeedExistence_of_nativeMass G N) C

/-! ## 5. Historical plane/ghost packages are all downstream -/

/-- The old ghost-adaptive common-class plane law is derived from canonical
primitive incidence plus the already-internal source cosmology. -/
theorem ghostAdaptiveCommonClassPlanes_of_conservedSpine_and_canonicalIncidence
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge G)
    (C : LiveWeightCanonicalGSTGeneratorPrimitiveIncidenceCompleteness
      (V := V) (H := H)) :
    GhostAdaptiveCommonClassPlaneCompleteness G := by
  exact
    (ghostAdaptiveCommonClassPlaneCompleteness_iff_hodge G).2
      (hodge_of_conservedSpine_and_canonicalPrimitiveIncidence G D C)

/-- Separator ghosts disappear as a consequence. -/
theorem no_omniversalSeparatorGhost_of_conservedSpine_and_canonicalIncidence
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge G)
    (C : LiveWeightCanonicalGSTGeneratorPrimitiveIncidenceCompleteness
      (V := V) (H := H)) :
    IsEmpty (OmniversalSeparatorGhost G) := by
  exact
    (hodge_iff_no_omniversalSeparatorGhost G).1
      (hodge_of_conservedSpine_and_canonicalPrimitiveIncidence G D C)

/-- Ghost-weight source survival becomes a theorem after ghost extinction. -/
theorem ghostWeightNativeSeedSurvival_of_conservedSpine_and_canonicalIncidence
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge G)
    (C : LiveWeightCanonicalGSTGeneratorPrimitiveIncidenceCompleteness
      (V := V) (H := H)) :
    GhostWeightNativeSeedSurvival G := by
  have hEmpty :=
    no_omniversalSeparatorGhost_of_conservedSpine_and_canonicalIncidence G D C
  intro E
  exact isEmptyElim E

/-- Ghost-weight strict closure becomes a theorem after ghost extinction. -/
theorem ghostWeightPrimitiveStrictClosure_of_conservedSpine_and_canonicalIncidence
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge G)
    (C : LiveWeightCanonicalGSTGeneratorPrimitiveIncidenceCompleteness
      (V := V) (H := H)) :
    GhostWeightPrimitiveStrictClosure G := by
  have hEmpty :=
    no_omniversalSeparatorGhost_of_conservedSpine_and_canonicalIncidence G D C
  intro E
  exact isEmptyElim E

/-- Ghost-weight common-class closure becomes a theorem after ghost extinction. -/
theorem ghostWeightPrimitiveCommonClassClosure_of_conservedSpine_and_canonicalIncidence
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge G)
    (C : LiveWeightCanonicalGSTGeneratorPrimitiveIncidenceCompleteness
      (V := V) (H := H)) :
    GhostWeightPrimitiveCommonClassClosure G := by
  have hEmpty :=
    no_omniversalSeparatorGhost_of_conservedSpine_and_canonicalIncidence G D C
  intro E
  exact isEmptyElim E

/-! ## 6. Necessity / noncircularity certificates -/

/-- Any old arbitrary-event primitive-incidence compiler necessarily contains
the canonical generator kernel.  This prevents a future proof from claiming a
weaker eventwise assumption while silently avoiding the actual generators. -/
theorem canonicalPrimitiveIncidence_is_necessary_for_eventMaterialization
    (M : ∀ {x y : HodgeBranchNode (V := V) (H := H) (p := p)},
      HodgeBranchEvent x y → StrictlyMaterializedBranch x y) :
    CanonicalGSTGeneratorPrimitiveIncidenceCompleteness
      (V := V) (H := H) (p := p) :=
  canonicalPrimitiveIncidence_of_eventMaterialization M

/-- A live zero-cycle-class semantic model cannot satisfy the conserved-spine
canonical-incidence finale's conclusion.  This is the internal semantic
firewall inherited from the exact Stage-2G target. -/
theorem not_hodge_of_live_zeroCycleClass_reaffirmed
    (q : Nat)
    (alpha : RationalSingularCohomology H.analytification (2 * q))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading q))
    (halpha_ne : alpha ≠ 0)
    (hzero : H.cycleClass q = 0) :
    ¬ BigradedBettiHodgeStatement V H :=
  GSTClassicalHodgePlaneCompletenessNonCircularity.not_hodge_of_live_zeroCycleClass
    q alpha halpha halpha_ne hzero

#check CanonicalGSTGeneratorPrimitiveIncidenceCompleteness
#check canonicalPrimitiveIncidence_of_eventMaterialization
#check eventMaterialization_of_canonicalPrimitiveIncidence
#check canonicalPrimitiveIncidence_iff_eventMaterialization
#check seedTargetPrimitiveIncidencePlanes_of_canonicalGenerators
#check hodge_weight_of_seed_and_canonicalPrimitiveIncidence
#check LiveWeightCanonicalGSTGeneratorPrimitiveIncidenceCompleteness
#check liveWeightPrimitiveIncidencePlanes_of_nativeSeeds_and_canonicalGenerators
#check hodge_of_nativeSeeds_and_canonicalPrimitiveIncidence
#check hodge_of_conservedSpine_and_canonicalPrimitiveIncidence
#check hodge_of_nativeMass_and_canonicalPrimitiveIncidence
#check ghostAdaptiveCommonClassPlanes_of_conservedSpine_and_canonicalIncidence
#check no_omniversalSeparatorGhost_of_conservedSpine_and_canonicalIncidence
#check canonicalPrimitiveIncidence_is_necessary_for_eventMaterialization
#check not_hodge_of_live_zeroCycleClass_reaffirmed

#print axioms canonicalPrimitiveIncidence_iff_eventMaterialization
#print axioms seedTargetPrimitiveIncidencePlanes_of_canonicalGenerators
#print axioms hodge_of_conservedSpine_and_canonicalPrimitiveIncidence
#print axioms hodge_of_nativeMass_and_canonicalPrimitiveIncidence
#print axioms ghostAdaptiveCommonClassPlanes_of_conservedSpine_and_canonicalIncidence
#print axioms canonicalPrimitiveIncidence_is_necessary_for_eventMaterialization

end GSTClassicalHodgeCanonicalGeneratorIncidenceKernel
