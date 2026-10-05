import GSTClassicalHodgePlaneCompletenessNonCircularity

/-!
# GST CLASSICAL HODGE — MINIMAL NONCIRCULAR PLANE COMPLETENESS

This module compresses the repaired plane route to the exact geometric data
consumed by the proof.

The previous eventwise compiler is intentionally stronger than necessary: it
realizes every primitive GST event.  Hodge reconstruction needs much less.  In
each live weight it needs only one genuine synchronized nonzero native/Hodge
seed and, from that seed, one realized common-class plane to each requested
Hodge basis sheet.

This yields the minimal ghost-free plane law below.  It has three important
properties.

1. It is stated without separator ghosts and is therefore not vacuous when the
   desired Hodge conclusion is true.
2. It contains no pre-supplied cycle representing a target basis sheet.  Such a
   cycle is constructed by the strict correspondence action and normalization.
3. It is strong enough to derive the historical ghost-adaptive completeness,
   ghost-weight survival, ghost-weight strict closure, and ghost-weight
   common-class closure packages as theorems rather than foundational inputs.

The zero-cycle-class semantic firewall is retained: on an arbitrary Stage-2G
semantic package with a live Hodge weight and zero cycle-class map, even the
source-seed law is impossible.  Thus no theorem below pretends that genuine
native geometry follows from the unconstrained semantic record alone.
-/

set_option maxHeartbeats 180000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry

namespace GSTClassicalHodgePlaneCompletenessMinimality

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeSynchronizedDefectOrbit
open GSTClassicalHodgeOmniversalSeparatorGhostCrown
open GSTClassicalHodgeOmniverseCausalBranchPacket
open GSTClassicalHodgeOmniverseStrictRelationRayCompiler
open GSTClassicalHodgeOmniversalGhostBranchClosure
open GSTClassicalHodgeCommonClassPlaneRealization
open GSTClassicalHodgePlaneCompletenessNonCircularity

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-! ## 1. Exact seed-level materialization burden -/

/-- Strict-relation form of the exact seed-to-target materialization law.

The event witness certifies that the target is an actual branch of the user's
GST omniverse.  The strict packet supplies the genuine correspondence geometry.
No separator, ghost, target cycle, or target algebraicity witness occurs. -/
def SeedTargetStrictRelationCompleteness
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p)) : Prop :=
  ∀ j : ClassicalHodgeBasisIndex V H p,
    ∃ i : HodgeSupportIndex S.hodge,
      HodgeBranchEvent
        (⟨Sector.gstPlus, S.hodge⟩ :
          HodgeBranchNode (V := V) (H := H) (p := p))
        (⟨Sector.gstPlus, hodgeMatrixUnit i.1 j S.hodge⟩ :
          HodgeBranchNode (V := V) (H := H) (p := p))
      ∧ Nonempty
        (StrictRelationEdgePacket
          (⟨Sector.gstPlus, S.hodge⟩ :
            HodgeBranchNode (V := V) (H := H) (p := p))
          (⟨Sector.gstPlus, hodgeMatrixUnit i.1 j S.hodge⟩ :
            HodgeBranchNode (V := V) (H := H) (p := p)))

/-- Hidden equivalence at the exact consumed boundary: common-class planes and
raw strict-relation packets carry precisely the same existence strength even
when indexed by the certified target branches of one live seed. -/
theorem seedTargetCommonClassPlanes_iff_strictRelations
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p)) :
    SeedTargetCommonClassPlaneCompleteness S ↔
      SeedTargetStrictRelationCompleteness S := by
  constructor
  · intro C j
    obtain ⟨i, hevent, ⟨P⟩⟩ := C j
    exact ⟨i, hevent, ⟨P.toStrictRelationEdgePacket⟩⟩
  · intro C j
    obtain ⟨i, hevent, ⟨R⟩⟩ := C j
    exact ⟨i, hevent, ⟨CommonClassPlanePacket.ofStrictRelation R⟩⟩

/-! ## 2. Minimal all-weight plane law -/

/-- **MINIMAL GHOST-FREE GST PLANE COMPLETENESS.**

Only live weights are constrained.  At such a weight, choose one genuine
synchronized nonzero native/Hodge seed and realize certified planes from that
single seed to every basis target.  This is exactly the amount of geometry
used by the direct basis reconstruction theorem and no more. -/
def LiveWeightSeedTargetCommonClassPlaneCompleteness : Prop :=
  ∀ q : Nat,
    rationalHodgeSubspace (H.hodgeBigrading q) ≠ ⊥ →
      ∃ S : NativeHodgeOrbitSeed (V := V) (H := H) (p := q),
        SeedTargetCommonClassPlaneCompleteness S

/-- Strict-relation normal form of the same minimal law. -/
def LiveWeightSeedTargetStrictRelationCompleteness : Prop :=
  ∀ q : Nat,
    rationalHodgeSubspace (H.hodgeBigrading q) ≠ ⊥ →
      ∃ S : NativeHodgeOrbitSeed (V := V) (H := H) (p := q),
        SeedTargetStrictRelationCompleteness S

/-- The common-class and strict-relation formulations of minimal completeness
are exactly equivalent.  This removes the possibility of hiding geometric
strength in the auxiliary plane class. -/
theorem liveWeightSeedTargetCommonClassPlanes_iff_strictRelations :
    LiveWeightSeedTargetCommonClassPlaneCompleteness (V := V) (H := H) ↔
      LiveWeightSeedTargetStrictRelationCompleteness (V := V) (H := H) := by
  constructor
  · intro C q hq
    obtain ⟨S, hS⟩ := C q hq
    exact ⟨S, (seedTargetCommonClassPlanes_iff_strictRelations S).1 hS⟩
  · intro C q hq
    obtain ⟨S, hS⟩ := C q hq
    exact ⟨S, (seedTargetCommonClassPlanes_iff_strictRelations S).2 hS⟩

/-- The previously separated source-survival plus all-event compiler laws imply
the minimal law.  Thus the new theorem is a genuine assumption reduction, not
an additional package layered on top. -/
theorem liveWeightSeedTargetCommonClassPlanes_of_liveSeed_and_eventwise
    (S : LiveWeightNativeSeedExistence (V := V) (H := H))
    (C : EventwiseCommonClassPlaneCompleteness (V := V) (H := H)) :
    LiveWeightSeedTargetCommonClassPlaneCompleteness (V := V) (H := H) := by
  intro q hq
  exact seedTargetPlanes_of_liveSeed_and_eventwiseCompleteness S C q hq

/-- Minimal plane completeness contains, in particular, the genuine source law
required in every live Hodge weight. -/
theorem liveWeightNativeSeedExistence_of_minimalPlanes
    (C : LiveWeightSeedTargetCommonClassPlaneCompleteness (V := V) (H := H)) :
    LiveWeightNativeSeedExistence (V := V) (H := H) := by
  intro q hq
  obtain ⟨S, _hplanes⟩ := C q hq
  exact ⟨S⟩

/-! ## 3. Direct noncircular finale -/

/-- **MINIMAL NONCIRCULAR GST PLANE FINALE.**

Every live weight is reconstructed directly from one synchronized seed and its
actual target planes.  There is no ghost contradiction and no supplied target
cycle anywhere in the premise. -/
theorem hodge_of_liveWeightSeedTargetCommonClassPlanes
    (C : LiveWeightSeedTargetCommonClassPlaneCompleteness (V := V) (H := H)) :
    BigradedBettiHodgeStatement V H := by
  intro q alpha halpha
  by_cases hq : rationalHodgeSubspace (H.hodgeBigrading q) = ⊥
  · have hzmem :
        alpha ∈
          (⊥ : Submodule ℚ
            (RationalSingularCohomology H.analytification (2 * q))) := by
      rw [← hq]
      exact halpha
    have hz : alpha = 0 := by
      simpa using hzmem
    subst alpha
    exact LinearMap.zero_mem _
  · obtain ⟨S, hplanes⟩ := C q hq
    exact hodge_weight_of_seedTargetCommonClassPlanes S hplanes halpha

/-- The strict-relation normal form proves the same finale without introducing
any additional hypothesis. -/
theorem hodge_of_liveWeightSeedTargetStrictRelations
    (C : LiveWeightSeedTargetStrictRelationCompleteness (V := V) (H := H)) :
    BigradedBettiHodgeStatement V H := by
  apply hodge_of_liveWeightSeedTargetCommonClassPlanes
  exact
    (liveWeightSeedTargetCommonClassPlanes_iff_strictRelations
      (V := V) (H := H)).2 C

/-! ## 4. Old ghost-indexed "axioms" are derived consequences -/

/-- Once the minimal ghost-free plane law is available, the historical
`GhostAdaptiveCommonClassPlaneCompleteness` is a theorem.  Its proof is routed
through the already-established circularity certificate only in the safe
consequence direction: minimal geometry -> Hodge -> historical ghost package. -/
theorem ghostAdaptiveCommonClassPlaneCompleteness_of_minimalPlanes
    (G : GeometricCycleClassSpine V H)
    (C : LiveWeightSeedTargetCommonClassPlaneCompleteness (V := V) (H := H)) :
    GhostAdaptiveCommonClassPlaneCompleteness G := by
  exact
    (ghostAdaptiveCommonClassPlaneCompleteness_iff_hodge G).2
      (hodge_of_liveWeightSeedTargetCommonClassPlanes C)

/-- Minimal geometry eliminates the ghost universe outright. -/
theorem no_omniversalSeparatorGhost_of_minimalPlanes
    (G : GeometricCycleClassSpine V H)
    (C : LiveWeightSeedTargetCommonClassPlaneCompleteness (V := V) (H := H)) :
    IsEmpty (OmniversalSeparatorGhost G) := by
  exact
    (hodge_iff_no_omniversalSeparatorGhost G).1
      (hodge_of_liveWeightSeedTargetCommonClassPlanes C)

/-- Ghost-weight native-seed survival is not foundational once the minimal
plane law has been proved: there are no ghosts left over which to quantify. -/
theorem ghostWeightNativeSeedSurvival_of_minimalPlanes
    (G : GeometricCycleClassSpine V H)
    (C : LiveWeightSeedTargetCommonClassPlaneCompleteness (V := V) (H := H)) :
    GhostWeightNativeSeedSurvival G := by
  have hEmpty := no_omniversalSeparatorGhost_of_minimalPlanes G C
  intro E
  exact isEmptyElim E

/-- The old ghost-weight strict-closure package is likewise a theorem, not a
primitive postulate, after the lower ghost-free geometry is established. -/
theorem ghostWeightPrimitiveStrictClosure_of_minimalPlanes
    (G : GeometricCycleClassSpine V H)
    (C : LiveWeightSeedTargetCommonClassPlaneCompleteness (V := V) (H := H)) :
    GhostWeightPrimitiveStrictClosure G := by
  have hEmpty := no_omniversalSeparatorGhost_of_minimalPlanes G C
  intro E
  exact isEmptyElim E

/-- The old ghost-weight common-class closure package is also derived and can
be removed from the foundational boundary. -/
theorem ghostWeightPrimitiveCommonClassClosure_of_minimalPlanes
    (G : GeometricCycleClassSpine V H)
    (C : LiveWeightSeedTargetCommonClassPlaneCompleteness (V := V) (H := H)) :
    GhostWeightPrimitiveCommonClassClosure G := by
  have hEmpty := no_omniversalSeparatorGhost_of_minimalPlanes G C
  intro E
  exact isEmptyElim E

/-! ## 5. Semantic necessity firewall -/

/-- A live Hodge sector with identically zero cycle-class map cannot possess the
source-survival law.  This uses only the repository's own synchronized-seed
identity `cycleClass(cycle) = hodge` and nonzero Hodge field. -/
theorem not_liveWeightNativeSeedExistence_of_live_zeroCycleClass
    (q : Nat)
    (alpha : RationalSingularCohomology H.analytification (2 * q))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading q))
    (halpha_ne : alpha ≠ 0)
    (hzero : H.cycleClass q = 0) :
    ¬ LiveWeightNativeSeedExistence (V := V) (H := H) := by
  intro S
  have hq : rationalHodgeSubspace (H.hodgeBigrading q) ≠ ⊥ := by
    intro hbot
    have hzmem :
        alpha ∈
          (⊥ : Submodule ℚ
            (RationalSingularCohomology H.analytification (2 * q))) := by
      rw [← hbot]
      exact halpha
    have hz : alpha = 0 := by
      simpa using hzmem
    exact halpha_ne hz
  obtain ⟨seed⟩ := S q hq
  have hclass := seed.class_eq
  rw [hzero] at hclass
  have hhodge : seed.hodge.1 = 0 := by
    simpa using hclass.symm
  apply seed.hodge_ne_zero
  apply Subtype.ext
  simpa using hhodge

/-- Therefore minimal plane completeness itself cannot be manufactured from an
arbitrary unconstrained Stage-2G semantic record.  A genuine native geometric
input is mathematically necessary. -/
theorem not_liveWeightSeedTargetCommonClassPlanes_of_live_zeroCycleClass
    (q : Nat)
    (alpha : RationalSingularCohomology H.analytification (2 * q))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading q))
    (halpha_ne : alpha ≠ 0)
    (hzero : H.cycleClass q = 0) :
    ¬ LiveWeightSeedTargetCommonClassPlaneCompleteness (V := V) (H := H) := by
  intro C
  exact
    not_liveWeightNativeSeedExistence_of_live_zeroCycleClass
      q alpha halpha halpha_ne hzero
      (liveWeightNativeSeedExistence_of_minimalPlanes C)

#check SeedTargetStrictRelationCompleteness
#check seedTargetCommonClassPlanes_iff_strictRelations
#check LiveWeightSeedTargetCommonClassPlaneCompleteness
#check LiveWeightSeedTargetStrictRelationCompleteness
#check liveWeightSeedTargetCommonClassPlanes_iff_strictRelations
#check liveWeightSeedTargetCommonClassPlanes_of_liveSeed_and_eventwise
#check liveWeightNativeSeedExistence_of_minimalPlanes
#check hodge_of_liveWeightSeedTargetCommonClassPlanes
#check hodge_of_liveWeightSeedTargetStrictRelations
#check ghostAdaptiveCommonClassPlaneCompleteness_of_minimalPlanes
#check no_omniversalSeparatorGhost_of_minimalPlanes
#check ghostWeightNativeSeedSurvival_of_minimalPlanes
#check ghostWeightPrimitiveStrictClosure_of_minimalPlanes
#check ghostWeightPrimitiveCommonClassClosure_of_minimalPlanes
#check not_liveWeightNativeSeedExistence_of_live_zeroCycleClass
#check not_liveWeightSeedTargetCommonClassPlanes_of_live_zeroCycleClass

#print axioms seedTargetCommonClassPlanes_iff_strictRelations
#print axioms liveWeightSeedTargetCommonClassPlanes_iff_strictRelations
#print axioms hodge_of_liveWeightSeedTargetCommonClassPlanes
#print axioms ghostAdaptiveCommonClassPlaneCompleteness_of_minimalPlanes
#print axioms ghostWeightNativeSeedSurvival_of_minimalPlanes
#print axioms ghostWeightPrimitiveStrictClosure_of_minimalPlanes
#print axioms ghostWeightPrimitiveCommonClassClosure_of_minimalPlanes
#print axioms not_liveWeightNativeSeedExistence_of_live_zeroCycleClass
#print axioms not_liveWeightSeedTargetCommonClassPlanes_of_live_zeroCycleClass

end GSTClassicalHodgePlaneCompletenessMinimality
