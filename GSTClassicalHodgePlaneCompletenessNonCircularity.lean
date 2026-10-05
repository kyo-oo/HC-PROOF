import GSTClassicalHodgeCommonClassPlaneRealization

/-!
# GST CLASSICAL HODGE — NONCIRCULAR PLANE COMPLETENESS

This module repairs the logical status of the common-class plane route.

The historical `GhostAdaptiveCommonClassPlaneCompleteness` quantifies over
hypothetical separator ghosts.  But every supplied strike already proves that
its ghost is impossible.  Consequently the historical definition is vacuous
when there are no ghosts and is in fact equivalent to ghost extinction itself.
It therefore cannot serve as a lower geometric premise for a proof of ghost
extinction.

There is a second hidden redundancy.  A `CommonClassPlanePacket` is exactly a
`StrictRelationEdgePacket` with the common class chosen canonically as the left
pullback of the source.  Thus the two-face formulation is geometrically useful
as an interpretation, but it does not weaken the strict-relation existence
problem.

The repaired notion below is non-vacuous.  It is stated before any separator or
ghost exists.  Fix a genuine nonzero synchronized native/Hodge seed.  For every
target Hodge sheet it asks for:

* the certified primitive GST branch already produced by the omniverse;
* one common-class plane packet materializing that actual branch.

From that data we construct the exact target basis cycle directly, with no
ghost argument.  Finite-support basis reconstruction then proves the complete
fixed-weight Hodge range.  The all-weight theorem needs such a seed/plane family
only in weights whose rational Hodge fiber is nonzero.

This is the correct noncircular boundary: plane materialization is an actual
geometric construction obligation on certified GST events, not a proposition
indexed by counterexamples to the theorem being proved.
-/

set_option maxHeartbeats 180000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry

namespace GSTClassicalHodgePlaneCompletenessNonCircularity

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
open GSTClassicalHodgeStrictCorrespondenceAnalyticSpan
open GSTClassicalHodgeCommonClassPlaneRealization

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-! ## 1. Hidden equivalence: common class = canonical strict relation -/

namespace CommonClassPlanePacket

variable
  {u v : HodgeBranchNode (V := V) (H := H) (p := p)}

/-- Every raw strict-relation packet has a canonical common carrier class:
namely the left pullback of the source.  The source face is reflexivity and the
target face is exactly the strict relation, read in the reverse direction.

This proves that introducing `planeClass` does not add an independent
geometric hypothesis. -/
noncomputable def ofStrictRelation
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
    unfold BettiRelated at R.related
    exact R.related.symm

/-- A common-class packet and a raw strict-relation packet are existence-wise
exactly equivalent.  Thus any proof claiming to have weakened the geometric
burden merely by inserting the common class has not yet discharged the real
materialization problem. -/
theorem nonempty_iff_strictRelation
    {u v : HodgeBranchNode (V := V) (H := H) (p := p)} :
    Nonempty (CommonClassPlanePacket u v) ↔
      Nonempty (StrictRelationEdgePacket u v) := by
  constructor
  · rintro ⟨P⟩
    exact ⟨P.toStrictRelationEdgePacket⟩
  · rintro ⟨R⟩
    exact ⟨ofStrictRelation R⟩

end CommonClassPlanePacket

/-- Primitive common-class plane compilation is exactly primitive strict
relation compilation.  This is the branch-level form of the preceding hidden
equivalence. -/
theorem primitiveCommonClassPlaneCompiler_iff_strictRelationCompiler :
    PrimitiveCommonClassPlaneCompiler (V := V) (H := H) (p := p) ↔
      PrimitiveStrictRelationCompiler (V := V) (H := H) (p := p) := by
  constructor
  · exact primitiveStrictRelationCompiler_of_commonClassPlanes
  · intro C u v huv
    obtain ⟨R⟩ := C huv
    exact ⟨CommonClassPlanePacket.ofStrictRelation R⟩

/-! ## 2. Circularity firewall for the historical ghost-adaptive definition -/

/-- The historical ghost-adaptive completeness proposition is logically
identical to saying that no omniversal separator ghost exists.

Forward direction is the existing plane-strike contradiction.  Reverse
direction is pure empty elimination: if there is no ghost, a proposition that
asks for a packet for every ghost is automatically true. -/
theorem ghostAdaptiveCommonClassPlaneCompleteness_iff_noGhost
    (G : GeometricCycleClassSpine V H) :
    GhostAdaptiveCommonClassPlaneCompleteness G ↔
      IsEmpty (OmniversalSeparatorGhost G) := by
  constructor
  · exact no_omniversalSeparatorGhost_of_commonClassPlanes G
  · intro hEmpty E
    exact isEmptyElim E

/-- **CIRCULARITY CERTIFICATE.**
The historical ghost-adaptive plane-completeness proposition is equivalent to
the exact Stage-2G Hodge target itself.  It is therefore a consequence-normal
form, not an admissible lower geometric axiom for proving Hodge. -/
theorem ghostAdaptiveCommonClassPlaneCompleteness_iff_hodge
    (G : GeometricCycleClassSpine V H) :
    GhostAdaptiveCommonClassPlaneCompleteness G ↔
      BigradedBettiHodgeStatement V H :=
  (ghostAdaptiveCommonClassPlaneCompleteness_iff_noGhost G).trans
    (hodge_iff_no_omniversalSeparatorGhost G).symm

/-- Internal semantic firewall: a live nonzero Hodge class together with a
zero cycle-class map makes the exact Hodge target impossible.  No outside
mathematics is used; this is immediate from the repository's own Stage-2G
semantics. -/
theorem not_hodge_of_live_zeroCycleClass
    (q : Nat)
    (alpha : RationalSingularCohomology H.analytification (2 * q))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading q))
    (halpha_ne : alpha ≠ 0)
    (hzero : H.cycleClass q = 0) :
    ¬ BigradedBettiHodgeStatement V H := by
  intro hHodge
  rcases hHodge q halpha with ⟨Z, hZ⟩
  have hclassZero : H.cycleClass q Z = 0 := by
    rw [hzero]
    rfl
  apply halpha_ne
  rw [← hZ, hclassZero]

/-- Hence the historical ghost-adaptive completeness proposition cannot hold
for the exact zero-cycle-class countermodel whenever its Hodge sector is live.
This prevents any future proof from silently deriving the old completeness
notion from arbitrary `HodgeBigradedBettiData`. -/
theorem not_ghostAdaptiveCommonClassPlaneCompleteness_of_live_zeroCycleClass
    (G : GeometricCycleClassSpine V H)
    (q : Nat)
    (alpha : RationalSingularCohomology H.analytification (2 * q))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading q))
    (halpha_ne : alpha ≠ 0)
    (hzero : H.cycleClass q = 0) :
    ¬ GhostAdaptiveCommonClassPlaneCompleteness G := by
  rw [ghostAdaptiveCommonClassPlaneCompleteness_iff_hodge G]
  exact not_hodge_of_live_zeroCycleClass q alpha halpha halpha_ne hzero

/-! ## 3. Non-vacuous replacement: planes over actual GST branches -/

/-- Non-vacuous plane completeness from one genuine synchronized native seed.

For each target sheet `j` we require a *real* certified GST branch from one
live source coordinate of `S`, together with a common-class plane packet for
that branch.  This proposition never mentions a separator, a ghost, failure of
Hodge, or a pre-existing target cycle. -/
def SeedTargetCommonClassPlaneCompleteness
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p)) : Prop :=
  ∀ j : ClassicalHodgeBasisIndex V H p,
    ∃ i : HodgeSupportIndex S.hodge,
      HodgeBranchEvent
        (⟨Sector.gstPlus, S.hodge⟩ :
          HodgeBranchNode (V := V) (H := H) (p := p))
        (⟨Sector.gstPlus, hodgeMatrixUnit i.1 j S.hodge⟩ :
          HodgeBranchNode (V := V) (H := H) (p := p))
      ∧ Nonempty
        (CommonClassPlanePacket
          (⟨Sector.gstPlus, S.hodge⟩ :
            HodgeBranchNode (V := V) (H := H) (p := p))
          (⟨Sector.gstPlus, hodgeMatrixUnit i.1 j S.hodge⟩ :
            HodgeBranchNode (V := V) (H := H) (p := p)))

/-- A genuine primitive eventwise plane compiler automatically gives the
non-vacuous target-plane family for any nonzero synchronized seed.  The branch
itself is supplied by the already-proved limitless omniverse theorem
`event_to_arbitrary_target`; only its geometric materialization is delegated to
the compiler. -/
theorem seedTargetCommonClassPlanes_of_primitiveCompiler
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (C : PrimitiveCommonClassPlaneCompiler (V := V) (H := H) (p := p)) :
    SeedTargetCommonClassPlaneCompleteness S := by
  intro j
  obtain ⟨i, hevent, _hi⟩ :=
    event_to_arbitrary_target
      (V := V) (H := H)
      S.hodge S.hodge_ne_zero Sector.gstPlus j
  exact ⟨i, hevent, C hevent⟩

/-- **ONE NON-VACUOUS PLANE -> EXACT TARGET BASIS CYCLE.**

There is no separator argument here.  The actual GST branch plane is compiled
to its strict relation; the existing native/cohomological commuting square is
executed on the genuine seed cycle; division by the live source coefficient
constructs the requested basis sheet exactly. -/
theorem targetBasisCycle_of_seedTargetCommonClassPlanes
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (C : SeedTargetCommonClassPlaneCompleteness S)
    (j : ClassicalHodgeBasisIndex V H p) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = (classicalHodgeBasis V H p j).1 := by
  obtain ⟨i, _hevent, ⟨P⟩⟩ := C j
  have hi : hodgeCoordinate i.1 S.hodge ≠ 0 := by
    have hsupp :
        i.1 ∈ ((classicalHodgeBasis V H p).repr S.hodge).support := i.2
    exact Finsupp.mem_support_iff.mp hsupp
  let R : StrictRelationEdgePacket
      (⟨Sector.gstPlus, S.hodge⟩ :
        HodgeBranchNode (V := V) (H := H) (p := p))
      (⟨Sector.gstPlus, hodgeMatrixUnit i.1 j S.hodge⟩ :
        HodgeBranchNode (V := V) (H := H) (p := p)) :=
    P.toStrictRelationEdgePacket
  exact ⟨normalizedStrictBranchTargetCycle S i R,
    normalizedStrictBranchTargetCycle_spec S i hi R⟩

/-- Every basis sheet lies in the genuine cycle-class range under the
non-vacuous seed-target plane law. -/
theorem targetBasis_mem_cycleClassRange_of_seedTargetCommonClassPlanes
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (C : SeedTargetCommonClassPlaneCompleteness S)
    (j : ClassicalHodgeBasisIndex V H p) :
    (classicalHodgeBasis V H p j).1 ∈ LinearMap.range (H.cycleClass p) := by
  obtain ⟨Z, hZ⟩ := targetBasisCycle_of_seedTargetCommonClassPlanes S C j
  exact ⟨Z, hZ⟩

/-- **NONCIRCULAR FIXED-WEIGHT PLANE COMPLETENESS THEOREM.**
One genuine nonzero synchronized native source plus actual common-class planes
for its certified target branches forces the complete rational Hodge weight
into the native cycle-class range.  This proof is direct basis reconstruction;
no ghost, separator, contradiction assumption, or target algebraicity premise
occurs. -/
theorem hodge_weight_of_seedTargetCommonClassPlanes
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (C : SeedTargetCommonClassPlaneCompleteness S) :
    rationalHodgeSubspace (H.hodgeBigrading p) ≤
      LinearMap.range (H.cycleClass p) := by
  intro alpha halpha
  let alphaH : ClassicalHodgeFiber V H p := ⟨alpha, halpha⟩
  have hbasis :
      ∀ j : ClassicalHodgeBasisIndex V H p,
        (classicalHodgeBasis V H p j).1 ∈
          LinearMap.range (H.cycleClass p) :=
    targetBasis_mem_cycleClassRange_of_seedTargetCommonClassPlanes S C
  change alphaH.1 ∈ LinearMap.range (H.cycleClass p)
  rw [show alphaH =
      ∑ j ∈ ((classicalHodgeBasis V H p).repr alphaH).support,
        ((classicalHodgeBasis V H p).repr alphaH j) •
          classicalHodgeBasis V H p j by
    exact (classicalHodgeBasis V H p).sum_repr alphaH]
  simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower]
  apply Submodule.sum_mem
  intro j hj
  exact (LinearMap.range (H.cycleClass p)).smul_mem
    ((classicalHodgeBasis V H p).repr alphaH j) (hbasis j)

/-- A live-weight source law contains only the source existence actually needed
by the non-vacuous plane theorem. -/
def LiveWeightNativeSeedExistence : Prop :=
  ∀ q : Nat,
    rationalHodgeSubspace (H.hodgeBigrading q) ≠ ⊥ →
      Nonempty (NativeHodgeOrbitSeed (V := V) (H := H) (p := q))

/-- Eventwise plane realization is the genuine geometric completeness burden:
every certified primitive GST event, at every weight, receives a common-class
strict correspondence carrier.  Unlike the historical ghost-adaptive notion,
this statement is not made vacuous by the desired conclusion. -/
def EventwiseCommonClassPlaneCompleteness : Prop :=
  ∀ q : Nat,
    PrimitiveCommonClassPlaneCompiler (V := V) (H := H) (p := q)

/-- Eventwise common-class completeness is exactly eventwise raw strict-relation
completeness.  This prevents future layers from disguising the same geometric
obligation under two interfaces. -/
theorem eventwiseCommonClassPlaneCompleteness_iff_strictRelationCompleteness :
    EventwiseCommonClassPlaneCompleteness (V := V) (H := H) ↔
      (∀ q : Nat,
        PrimitiveStrictRelationCompiler (V := V) (H := H) (p := q)) := by
  constructor
  · intro C q
    exact
      (primitiveCommonClassPlaneCompiler_iff_strictRelationCompiler
        (V := V) (H := H) (p := q)).1 (C q)
  · intro C q
    exact
      (primitiveCommonClassPlaneCompiler_iff_strictRelationCompiler
        (V := V) (H := H) (p := q)).2 (C q)

/-- Eventwise plane realization plus a genuine native source in each live Hodge
weight produces the non-vacuous seed-target completeness family. -/
theorem seedTargetPlanes_of_liveSeed_and_eventwiseCompleteness
    (S : LiveWeightNativeSeedExistence (V := V) (H := H))
    (C : EventwiseCommonClassPlaneCompleteness (V := V) (H := H))
    (q : Nat)
    (hq : rationalHodgeSubspace (H.hodgeBigrading q) ≠ ⊥) :
    ∃ seed : NativeHodgeOrbitSeed (V := V) (H := H) (p := q),
      SeedTargetCommonClassPlaneCompleteness seed := by
  let seed := Classical.choice (S q hq)
  exact ⟨seed,
    seedTargetCommonClassPlanes_of_primitiveCompiler seed (C q)⟩

/-- **NONCIRCULAR ALL-WEIGHT GST PLANE FINALE.**

The exact Stage-2G Hodge statement follows from two lower, independently
meaningful geometric laws:

1. a genuine synchronized native source exists whenever the Hodge weight is
   live;
2. every certified primitive GST event has an intrinsic common-class strict
   correspondence realization.

No premise quantifies over a hypothetical failure witness, and neither premise
contains a target cycle or a cycle-class-surjectivity statement. -/
theorem hodge_of_liveSeed_and_eventwiseCommonClassPlanes
    (S : LiveWeightNativeSeedExistence (V := V) (H := H))
    (C : EventwiseCommonClassPlaneCompleteness (V := V) (H := H)) :
    BigradedBettiHodgeStatement V H := by
  intro q alpha halpha
  by_cases hq : rationalHodgeSubspace (H.hodgeBigrading q) = ⊥
  · have hz : alpha = 0 := by
      have : alpha ∈
          (⊥ : Submodule ℚ
            (RationalSingularCohomology H.analytification (2 * q))) := by
        simpa [hq] using halpha
      simpa using this
    subst alpha
    exact LinearMap.zero_mem _
  · obtain ⟨seed, hplanes⟩ :=
      seedTargetPlanes_of_liveSeed_and_eventwiseCompleteness S C q hq
    exact hodge_weight_of_seedTargetCommonClassPlanes seed hplanes halpha

#check CommonClassPlanePacket.ofStrictRelation
#check CommonClassPlanePacket.nonempty_iff_strictRelation
#check primitiveCommonClassPlaneCompiler_iff_strictRelationCompiler
#check ghostAdaptiveCommonClassPlaneCompleteness_iff_noGhost
#check ghostAdaptiveCommonClassPlaneCompleteness_iff_hodge
#check not_hodge_of_live_zeroCycleClass
#check not_ghostAdaptiveCommonClassPlaneCompleteness_of_live_zeroCycleClass
#check SeedTargetCommonClassPlaneCompleteness
#check seedTargetCommonClassPlanes_of_primitiveCompiler
#check targetBasisCycle_of_seedTargetCommonClassPlanes
#check hodge_weight_of_seedTargetCommonClassPlanes
#check LiveWeightNativeSeedExistence
#check EventwiseCommonClassPlaneCompleteness
#check eventwiseCommonClassPlaneCompleteness_iff_strictRelationCompleteness
#check hodge_of_liveSeed_and_eventwiseCommonClassPlanes

#print axioms CommonClassPlanePacket.nonempty_iff_strictRelation
#print axioms ghostAdaptiveCommonClassPlaneCompleteness_iff_hodge
#print axioms targetBasisCycle_of_seedTargetCommonClassPlanes
#print axioms hodge_weight_of_seedTargetCommonClassPlanes
#print axioms hodge_of_liveSeed_and_eventwiseCommonClassPlanes

end GSTClassicalHodgePlaneCompletenessNonCircularity
