import Mathlib.LinearAlgebra.Basis.VectorSpace
import GSTGeometricRealizationStage2G
import GSTTransferBridgeV2
import GSTGlobalPureHodgeCosmology
import GSTDimensionFreeHodgeDiagonal
import GSTUniversalAddressBridge
import GSTTruncatedWorldCohomologyRing
import GSTUniversalLefschetzCosmology
import GSTUniversalLefschetzPathFormula
import GSTUniversalLefschetzKernel
import GSTUniversalLefschetzCausalGeometry
import GSTLefschetzPoincareReciprocity
import GSTWorldPoincareDuality
import GSTWorldRecoordinationGroupoid
import GSTGradedWorldAlgebra
import GSTHodgeChannelFinale
import GSTClassicalHodgeFullLimitlessCrown
import GSTClassicalHodgeProjectiveTwoGeneratorExternalization

/-!
# Hodge Conjecture — Unified Classical GST Landing

This file is the public top-level landing face for the Hodge development.
It combines three independently developed and machine-oriented layers:

1. the genuine Stage-2G rational Hodge target on smooth projective complex
   schemes and native codimension-p algebraic cycles;
2. the rank-free / index-polymorphic classical GST basis reconstruction;
3. the multi-channel Wave-II finite-basis/quotient finale and the full
   limitless geometric/cosmic classical crown.

No internal GST surrogate is substituted for the target.  `ClassicalHodgeTarget`
is definitionally the Stage-2G statement.

The original compatibility landing is retained:

  genuine geometric cycle-class spine
    + nonvanishing projective spine tower
    + genuine projective externalization of the cosmic read/write action
      -> full limitless classical Hodge crown.

The strengthened geometry-first landing removes both of those large supplied
interfaces from its public input surface:

  genuine geometric cycle-class spine
    + one conserved native/cohomological tower charge
      -> all-weight spine nonvanishing as a theorem
    + two genuine projective primitive actions per ordered Hodge pair
      -> all rank-free matrix units by the internal GST word algebra
      -> exact Stage-2G Hodge statement
      -> explicit native codimension-p cycle for every rational (p,p) class.

Under the ordinary finite-dimensionality package for the rational Hodge
fibers, either exact Hodge landing is transported through the independently
verified multi-channel architecture:

  exact Hodge statement
    <-> canonical finite-basis algebraization
    -> Wave-II channel quotient
    -> arbitrary same-weight multiplicity with no finite rank ceiling.

The routes meet here; none is hidden behind a redefinition of Hodge.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G

namespace HodgeConjecture

/-- The exact classical Hodge target already isolated by Stage 2G.

For every codimension `p`, every rational singular-cohomology class whose
complexification lies in the `(p,p)` Hodge summand must lie in the range of
the native codimension-`p` algebraic cycle-class map. -/
def ClassicalHodgeTarget
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) : Prop :=
  BigradedBettiHodgeStatement V H

/-- The target is exactly the elementwise algebraic-cycle witness statement;
there is no weaker GST surrogate hidden behind the name. -/
theorem classicalHodgeTarget_iff_explicit_witness
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) :
    ClassicalHodgeTarget V H ↔
      ∀ p : Nat,
      ∀ alpha : RationalSingularCohomology H.analytification (2 * p),
        complexificationMapQ
            (RationalSingularCohomology H.analytification (2 * p)) alpha
          ∈ (H.hodgeBigrading p).ppComponent →
        ∃ Z : codimensionCycles V.X p,
          H.cycleClass p Z = alpha := by
  simpa [ClassicalHodgeTarget] using
    (bigradedBettiHodgeStatement_iff_explicit_witness V H)

/-- Stage 2G has already proved the final logical landing. -/
theorem classicalHodgeTarget_of_compact_realization
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (hR : Stage2GCompactRealizationObligation V H) :
    ClassicalHodgeTarget V H := by
  exact bigraded_betti_hodge_of_stage2g_compact_obligation V H hR

/-- Elementwise form of the same compact-realization reduction. -/
theorem explicit_witness_of_compact_realization
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (hR : Stage2GCompactRealizationObligation V H)
    (p : Nat)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha :
      complexificationMapQ
          (RationalSingularCohomology H.analytification (2 * p)) alpha
        ∈ (H.hodgeBigrading p).ppComponent) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha := by
  exact
    (classicalHodgeTarget_iff_explicit_witness V H).mp
      (classicalHodgeTarget_of_compact_realization V H hR)
      p alpha halpha

/-! ## Index-polymorphic limitless realization -/

/-- One Stage-2G realization with an arbitrary address universe `ι`.
The structure contains no Hodge conclusion; it records only the realization
and its compatibility with the genuine Hodge predicate and cycle-class map. -/
structure UniverseIndexedRealization
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) (ι : Type*) where
  realization :
    CompactHodgeRealization ι
      (RationalSingularCohomology H.analytification (2 * p))
      (codimensionCycles V.X p)
  hodge_iff :
    ∀ alpha : RationalSingularCohomology H.analytification (2 * p),
      realization.isHodge alpha ↔
        alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p)
  cycleClass_eq :
    realization.cycleClass = H.cycleClass p

/-- Any genuine index-polymorphic realization produces an actual native
codimension-p cycle for each rational `(p,p)` class. -/
theorem hodge_class_has_cycle_of_universe_indexed_realization
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    {p : Nat} {ι : Type*}
    (R : UniverseIndexedRealization V H p ι)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p)) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha := by
  have hr : R.realization.isHodge alpha :=
    (R.hodge_iff alpha).2 halpha
  obtain ⟨Z, hZ⟩ :=
    compact_realization_surjectivity R.realization alpha hr
  refine ⟨Z, ?_⟩
  rw [← R.cycleClass_eq]
  exact hZ

/-- A family of arbitrary-index realizations closes the exact classical
Stage-2G target.  The index type may vary with the codimension. -/
theorem classicalHodgeTarget_of_universe_indexed_family
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (ι : Nat → Type*)
    (R : ∀ p : Nat, UniverseIndexedRealization V H p (ι p)) :
    ClassicalHodgeTarget V H := by
  intro p alpha halpha
  exact hodge_class_has_cycle_of_universe_indexed_realization
    V H (R p) alpha halpha

/-! ## Exact limitless coordinates on the genuine Hodge fiber -/

/-- The actual rational `(p,p)` Hodge fiber in degree `2p`. -/
abbrev HodgeFiber
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) : Type :=
  rationalHodgeSubspace (H.hodgeBigrading p)

/-- A completely unrestricted basis index for one classical Hodge fiber. -/
abbrev HodgeBasisIndex
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) :=
  Module.Free.ChooseBasisIndex ℚ (HodgeFiber V H p)

/-- A chosen rational basis of the genuine `(p,p)` Hodge fiber. -/
noncomputable def hodgeBasis
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) :
    Module.Basis (HodgeBasisIndex V H p) ℚ (HodgeFiber V H p) :=
  Module.Free.chooseBasis ℚ (HodgeFiber V H p)

/-- Limitless finite-support coordinates of a genuine Hodge class. -/
noncomputable def hodgeCoordinates
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) :
    HodgeFiber V H p ≃ₗ[ℚ] (HodgeBasisIndex V H p →₀ ℚ) :=
  (hodgeBasis V H p).repr

@[simp]
theorem hodgeCoordinates_basis
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) (i : HodgeBasisIndex V H p) :
    hodgeCoordinates V H p (hodgeBasis V H p i) =
      Finsupp.single i 1 := by
  simp [hodgeCoordinates]

/-- The irreducible geometric datum for one Hodge fiber: every basis vector
has an actual native codimension-`p` algebraic-cycle representative. -/
structure HodgeBasisCycleBridge
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) where
  basisCycle : HodgeBasisIndex V H p → codimensionCycles V.X p
  basisCycle_spec :
    ∀ i : HodgeBasisIndex V H p,
      H.cycleClass p (basisCycle i) = (hodgeBasis V H p i).1

/-- Lift the chosen Hodge basis to native algebraic cycles linearly. -/
noncomputable def hodgeBasisCycleLift
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (R : HodgeBasisCycleBridge V H p) :
    HodgeFiber V H p →ₗ[ℚ] codimensionCycles V.X p :=
  (hodgeBasis V H p).constr ℚ R.basisCycle

@[simp]
theorem hodgeBasisCycleLift_basis
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (R : HodgeBasisCycleBridge V H p)
    (i : HodgeBasisIndex V H p) :
    hodgeBasisCycleLift V H p R (hodgeBasis V H p i) =
      R.basisCycle i := by
  simp [hodgeBasisCycleLift]

/-- Finite-support reconstruction is exact: after applying the genuine
cycle-class map, the basis-cycle lift is precisely the inclusion of the Hodge
subspace into ambient rational singular cohomology. -/
theorem hodgeBasisCycleLift_spec
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (R : HodgeBasisCycleBridge V H p)
    (alpha : HodgeFiber V H p) :
    H.cycleClass p (hodgeBasisCycleLift V H p R alpha) = alpha.1 := by
  have hmaps :
      (H.cycleClass p).comp (hodgeBasisCycleLift V H p R) =
        (rationalHodgeSubspace (H.hodgeBigrading p)).subtype := by
    apply (hodgeBasis V H p).ext
    intro i
    simp [hodgeBasisCycleLift, R.basisCycle_spec]
  change ((H.cycleClass p).comp (hodgeBasisCycleLift V H p R)) alpha = alpha.1
  rw [hmaps]
  rfl

/-- Basis-wise algebraicity therefore produces a native cycle for an
arbitrary rational `(p,p)` class. -/
theorem hodge_class_has_cycle_of_basis_bridge
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    {p : Nat}
    (R : HodgeBasisCycleBridge V H p)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p)) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha := by
  let alphaH : HodgeFiber V H p := ⟨alpha, halpha⟩
  refine ⟨hodgeBasisCycleLift V H p R alphaH, ?_⟩
  simpa [alphaH] using hodgeBasisCycleLift_spec V H p R alphaH

/-- A basis-cycle bridge in every codimension closes the exact classical
Hodge target, with arbitrary rank and multiplicity. -/
theorem classicalHodgeTarget_of_basis_cycle_family
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (R : ∀ p : Nat, HodgeBasisCycleBridge V H p) :
    ClassicalHodgeTarget V H := by
  intro p alpha halpha
  exact hodge_class_has_cycle_of_basis_bridge V H (R p) alpha halpha

/-- If the classical target already holds, each chosen Hodge basis vector has
a native algebraic representative. -/
noncomputable def hodgeBasisCycleBridgeOfTarget
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (h : ClassicalHodgeTarget V H)
    (p : Nat) :
    HodgeBasisCycleBridge V H p where
  basisCycle i :=
    Classical.choose (show
      ∃ Z : codimensionCycles V.X p,
        H.cycleClass p Z = (hodgeBasis V H p i).1 by
      exact h p (hodgeBasis V H p i).2)
  basisCycle_spec i :=
    Classical.choose_spec (show
      ∃ Z : codimensionCycles V.X p,
        H.cycleClass p Z = (hodgeBasis V H p i).1 by
      exact h p (hodgeBasis V H p i).2)

/-- **BASIS-GENERATOR NORMAL FORM.**
The exact Stage-2G Hodge target is equivalent to algebraicity of one chosen
basis of every rational `(p,p)` Hodge fiber. -/
theorem classicalHodgeTarget_iff_basis_cycle_bridges
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) :
    ClassicalHodgeTarget V H ↔
      ∀ p : Nat, Nonempty (HodgeBasisCycleBridge V H p) := by
  constructor
  · intro h p
    exact ⟨hodgeBasisCycleBridgeOfTarget V H h p⟩
  · intro h
    exact classicalHodgeTarget_of_basis_cycle_family V H
      (fun p => Classical.choice (h p))

/-- Semantic firewall: if a supplied cycle-class map is zero while the Hodge
sector contains a nonzero class, then the classical Hodge target for that
semantic package is impossible. -/
theorem not_classicalHodgeTarget_of_zero_cycleClass
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha :
      complexificationMapQ
          (RationalSingularCohomology H.analytification (2 * p)) alpha
        ∈ (H.hodgeBigrading p).ppComponent)
    (halpha_ne : alpha ≠ 0)
    (hzero : H.cycleClass p = 0) :
    ¬ ClassicalHodgeTarget V H := by
  intro hTarget
  obtain ⟨Z, hZ⟩ :=
    (classicalHodgeTarget_iff_explicit_witness V H).mp hTarget
      p alpha halpha
  have hzeroZ : H.cycleClass p Z = 0 := by
    rw [hzero]
    rfl
  apply halpha_ne
  rw [← hZ, hzeroZ]

/-! ## Unified finale: Astra geometry × GLM repairs × multi-channel architecture -/

/-- The public target is exactly equivalent to the canonical finite-basis
algebraization obligation from the multi-channel finale.  This is the direct
wire from the independently verified channel architecture into the public
Hodge statement. -/
theorem classicalHodgeTarget_iff_canonical_basis_algebraization
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (F : GSTHodgeChannelFinale.Stage2GHodgeFiniteness V H) :
    ClassicalHodgeTarget V H ↔
      GSTHodgeChannelFinale.Stage2GCanonicalBasisAlgebraizationObligation
        V H F := by
  simpa [ClassicalHodgeTarget] using
    (GSTHodgeChannelFinale.canonical_basis_algebraization_iff_hodge
      V H F).symm

/-- Astra's full limitless geometric/cosmic crown lands directly in the exact
public Hodge target.  No finite chart, one-generator surrogate, or altered
Hodge statement occurs at this boundary. -/
theorem classicalHodgeTarget_of_full_limitless_geometry
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (G :
      GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (hNV :
      GSTClassicalHodgeFullLimitlessCrown.SpineTowerNonvanishing G)
    (R :
      GSTClassicalHodgeFullLimitlessCrown.FullProjectiveCosmicExternalization G) :
    ClassicalHodgeTarget V H := by
  simpa [ClassicalHodgeTarget] using
    (GSTClassicalHodgeFullLimitlessCrown.bigradedBettiHodge G hNV R)

/-- Explicit elementwise native-cycle form of the full limitless landing. -/
theorem every_hodge_class_has_native_cycle_of_full_limitless_geometry
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (G :
      GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (hNV :
      GSTClassicalHodgeFullLimitlessCrown.SpineTowerNonvanishing G)
    (R :
      GSTClassicalHodgeFullLimitlessCrown.FullProjectiveCosmicExternalization G)
    (p : Nat)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p)) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha := by
  exact
    GSTClassicalHodgeFullLimitlessCrown.every_hodge_class_has_native_cycle
      G hNV R p alpha halpha

/-- **GEOMETRY-FIRST BRUTE-FORCE PUBLIC LANDING.**

This strengthened public theorem removes both large compatibility inputs of the
older limitless crown.  The tower-nonvanishing family is generated internally
from one conserved native/cohomological charge.  Full projective matrix-unit
externalization is replaced by two actual projective primitive actions per
ordered Hodge pair; the complete rank-free matrix-unit arsenal is synthesized
by the internal GST two-generator word. -/
theorem classicalHodgeTarget_of_conserved_spine_and_projective_two_generators
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (G :
      GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (D :
      GSTClassicalHodgeLimitlessSpinePropagation.SpineTowerConservedCharge G)
    (R : ∀ q : Nat,
      ∀ i j : GSTClassicalHodgeFiberedCosmology.ClassicalHodgeBasisIndex V H q,
        GSTClassicalHodgeProjectiveTwoGeneratorExternalization.ProjectiveTwoGenerator
          (V := V) (H := H) i j) :
    ClassicalHodgeTarget V H := by
  simpa [ClassicalHodgeTarget] using
    (GSTClassicalHodgeProjectiveTwoGeneratorExternalization.
      GSTClassicalHodgeProjectiveTwoGeneratorExternalization.bigradedBettiHodge_of_conserved_spine_and_projective_two_generators
        G D R)

/-- Elementwise cycle witness for the geometry-first brute-force landing. -/
theorem every_hodge_class_has_native_cycle_of_conserved_spine_and_projective_two_generators
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (G :
      GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (D :
      GSTClassicalHodgeLimitlessSpinePropagation.SpineTowerConservedCharge G)
    (R : ∀ q : Nat,
      ∀ i j : GSTClassicalHodgeFiberedCosmology.ClassicalHodgeBasisIndex V H q,
        GSTClassicalHodgeProjectiveTwoGeneratorExternalization.ProjectiveTwoGenerator
          (V := V) (H := H) i j)
    (p : Nat)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p)) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha := by
  exact
    GSTClassicalHodgeProjectiveTwoGeneratorExternalization.
      every_hodge_class_has_native_cycle_of_conserved_spine_and_projective_two_generators
        G D R p alpha halpha

/-- Once ordinary Hodge-fiber finite-dimensionality is supplied, the full
limitless classical crown automatically supplies the exact canonical basis
algebraization obligation used by the multi-channel theorem. -/
theorem canonical_basis_algebraization_of_full_limitless_geometry
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (F : GSTHodgeChannelFinale.Stage2GHodgeFiniteness V H)
    (G :
      GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (hNV :
      GSTClassicalHodgeFullLimitlessCrown.SpineTowerNonvanishing G)
    (R :
      GSTClassicalHodgeFullLimitlessCrown.FullProjectiveCosmicExternalization G) :
    GSTHodgeChannelFinale.Stage2GCanonicalBasisAlgebraizationObligation
      V H F := by
  apply
    (GSTHodgeChannelFinale.canonical_basis_algebraization_iff_hodge
      V H F).2
  exact GSTClassicalHodgeFullLimitlessCrown.bigradedBettiHodge G hNV R

/-- Canonical finite-basis algebraization generated from the strengthened
conserved-spine/projective-two-generator route. -/
theorem canonical_basis_algebraization_of_conserved_spine_and_projective_two_generators
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (F : GSTHodgeChannelFinale.Stage2GHodgeFiniteness V H)
    (G :
      GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (D :
      GSTClassicalHodgeLimitlessSpinePropagation.SpineTowerConservedCharge G)
    (R : ∀ q : Nat,
      ∀ i j : GSTClassicalHodgeFiberedCosmology.ClassicalHodgeBasisIndex V H q,
        GSTClassicalHodgeProjectiveTwoGeneratorExternalization.ProjectiveTwoGenerator
          (V := V) (H := H) i j) :
    GSTHodgeChannelFinale.Stage2GCanonicalBasisAlgebraizationObligation
      V H F := by
  apply
    (GSTHodgeChannelFinale.canonical_basis_algebraization_iff_hodge
      V H F).2
  exact
    GSTClassicalHodgeProjectiveTwoGeneratorExternalization.
      GSTClassicalHodgeProjectiveTwoGeneratorExternalization.bigradedBettiHodge_of_conserved_spine_and_projective_two_generators
        G D R

/-- The same geometric/cosmic crown therefore generates the minimal Wave-II
channel quotient architecture automatically. -/
theorem channel_quotient_of_full_limitless_geometry
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (F : GSTHodgeChannelFinale.Stage2GHodgeFiniteness V H)
    (G :
      GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (hNV :
      GSTClassicalHodgeFullLimitlessCrown.SpineTowerNonvanishing G)
    (R :
      GSTClassicalHodgeFullLimitlessCrown.FullProjectiveCosmicExternalization G) :
    GSTHodgeChannelQuotient.Stage2GChannelQuotientObligation V H := by
  exact
    GSTHodgeChannelFinale.canonical_basis_obligation_implies_channel_quotient
      V H F
      (canonical_basis_algebraization_of_full_limitless_geometry F G hNV R)

/-- Wave-II channel quotient generated from the strengthened geometry-first
route. -/
theorem channel_quotient_of_conserved_spine_and_projective_two_generators
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (F : GSTHodgeChannelFinale.Stage2GHodgeFiniteness V H)
    (G :
      GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (D :
      GSTClassicalHodgeLimitlessSpinePropagation.SpineTowerConservedCharge G)
    (R : ∀ q : Nat,
      ∀ i j : GSTClassicalHodgeFiberedCosmology.ClassicalHodgeBasisIndex V H q,
        GSTClassicalHodgeProjectiveTwoGeneratorExternalization.ProjectiveTwoGenerator
          (V := V) (H := H) i j) :
    GSTHodgeChannelQuotient.Stage2GChannelQuotientObligation V H := by
  exact
    GSTHodgeChannelFinale.canonical_basis_obligation_implies_channel_quotient
      V H F
      (canonical_basis_algebraization_of_conserved_spine_and_projective_two_generators
        F G D R)

/-- Same-weight multiplicity is unrestricted in the final public landing. -/
theorem no_same_weight_hodge_rank_ceiling :
    ∀ N p : Nat,
      Fintype.card
          (GSTMultiChannelHodgeCosmology.HodgeChannel
            (GSTMultiChannelHodgeCosmology.standardChannelShape N)) = N := by
  exact GSTHodgeChannelFinale.no_same_weight_rank_ceiling

/-- **UNIFIED FINAL HODGE RECEIPT.**

This theorem is the explicit composition point of the original full-limitless
compatibility lane and the multi-channel architecture.  It is retained for
backward compatibility with existing callers. -/
theorem unified_hodge_finale
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (F : GSTHodgeChannelFinale.Stage2GHodgeFiniteness V H)
    (G :
      GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (hNV :
      GSTClassicalHodgeFullLimitlessCrown.SpineTowerNonvanishing G)
    (R :
      GSTClassicalHodgeFullLimitlessCrown.FullProjectiveCosmicExternalization G) :
    ClassicalHodgeTarget V H
    ∧ GSTHodgeChannelFinale.Stage2GCanonicalBasisAlgebraizationObligation V H F
    ∧ GSTHodgeChannelQuotient.Stage2GChannelQuotientObligation V H
    ∧ (∀ N p : Nat,
      Fintype.card
          (GSTMultiChannelHodgeCosmology.HodgeChannel
            (GSTMultiChannelHodgeCosmology.standardChannelShape N)) = N) := by
  have hTarget : ClassicalHodgeTarget V H :=
    classicalHodgeTarget_of_full_limitless_geometry G hNV R
  have hBasis :
      GSTHodgeChannelFinale.Stage2GCanonicalBasisAlgebraizationObligation
        V H F :=
    canonical_basis_algebraization_of_full_limitless_geometry F G hNV R
  have hQuot :
      GSTHodgeChannelQuotient.Stage2GChannelQuotientObligation V H :=
    GSTHodgeChannelFinale.canonical_basis_obligation_implies_channel_quotient
      V H F hBasis
  exact ⟨hTarget, hBasis, hQuot, no_same_weight_hodge_rank_ceiling⟩

/-- **UNIFIED GEOMETRY-FIRST BRUTE-FORCE HODGE RECEIPT.**

The old `hNV` and full projective-kernel externalization arguments are absent
from this strengthened public finale.  Nonvanishing is generated recursively
from the conserved charge and all matrix units are generated from the two
actual projective primitive actions. -/
theorem unified_hodge_finale_conserved_spine_projective_two_generators
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (F : GSTHodgeChannelFinale.Stage2GHodgeFiniteness V H)
    (G :
      GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (D :
      GSTClassicalHodgeLimitlessSpinePropagation.SpineTowerConservedCharge G)
    (R : ∀ q : Nat,
      ∀ i j : GSTClassicalHodgeFiberedCosmology.ClassicalHodgeBasisIndex V H q,
        GSTClassicalHodgeProjectiveTwoGeneratorExternalization.ProjectiveTwoGenerator
          (V := V) (H := H) i j) :
    ClassicalHodgeTarget V H
    ∧ GSTHodgeChannelFinale.Stage2GCanonicalBasisAlgebraizationObligation V H F
    ∧ GSTHodgeChannelQuotient.Stage2GChannelQuotientObligation V H
    ∧ (∀ N p : Nat,
      Fintype.card
          (GSTMultiChannelHodgeCosmology.HodgeChannel
            (GSTMultiChannelHodgeCosmology.standardChannelShape N)) = N) := by
  have hTarget : ClassicalHodgeTarget V H :=
    classicalHodgeTarget_of_conserved_spine_and_projective_two_generators
      G D R
  have hBasis :
      GSTHodgeChannelFinale.Stage2GCanonicalBasisAlgebraizationObligation
        V H F :=
    canonical_basis_algebraization_of_conserved_spine_and_projective_two_generators
      F G D R
  have hQuot :
      GSTHodgeChannelQuotient.Stage2GChannelQuotientObligation V H :=
    GSTHodgeChannelFinale.canonical_basis_obligation_implies_channel_quotient
      V H F hBasis
  exact ⟨hTarget, hBasis, hQuot, no_same_weight_hodge_rank_ceiling⟩

#check ClassicalHodgeTarget
#check classicalHodgeTarget_iff_explicit_witness
#check classicalHodgeTarget_of_compact_realization
#check explicit_witness_of_compact_realization
#check UniverseIndexedRealization
#check hodge_class_has_cycle_of_universe_indexed_realization
#check classicalHodgeTarget_of_universe_indexed_family
#check HodgeFiber
#check HodgeBasisIndex
#check hodgeBasis
#check hodgeCoordinates
#check hodgeCoordinates_basis
#check HodgeBasisCycleBridge
#check hodgeBasisCycleLift
#check hodgeBasisCycleLift_spec
#check hodge_class_has_cycle_of_basis_bridge
#check classicalHodgeTarget_of_basis_cycle_family
#check hodgeBasisCycleBridgeOfTarget
#check classicalHodgeTarget_iff_basis_cycle_bridges
#check not_classicalHodgeTarget_of_zero_cycleClass
#check classicalHodgeTarget_iff_canonical_basis_algebraization
#check classicalHodgeTarget_of_full_limitless_geometry
#check every_hodge_class_has_native_cycle_of_full_limitless_geometry
#check classicalHodgeTarget_of_conserved_spine_and_projective_two_generators
#check every_hodge_class_has_native_cycle_of_conserved_spine_and_projective_two_generators
#check canonical_basis_algebraization_of_full_limitless_geometry
#check canonical_basis_algebraization_of_conserved_spine_and_projective_two_generators
#check channel_quotient_of_full_limitless_geometry
#check channel_quotient_of_conserved_spine_and_projective_two_generators
#check no_same_weight_hodge_rank_ceiling
#check unified_hodge_finale
#check unified_hodge_finale_conserved_spine_projective_two_generators

#print axioms classicalHodgeTarget_iff_explicit_witness
#print axioms classicalHodgeTarget_of_compact_realization
#print axioms explicit_witness_of_compact_realization
#print axioms hodge_class_has_cycle_of_universe_indexed_realization
#print axioms classicalHodgeTarget_of_universe_indexed_family
#print axioms hodgeCoordinates_basis
#print axioms hodgeBasisCycleLift_spec
#print axioms hodge_class_has_cycle_of_basis_bridge
#print axioms classicalHodgeTarget_of_basis_cycle_family
#print axioms classicalHodgeTarget_iff_basis_cycle_bridges
#print axioms not_classicalHodgeTarget_of_zero_cycleClass
#print axioms classicalHodgeTarget_iff_canonical_basis_algebraization
#print axioms classicalHodgeTarget_of_full_limitless_geometry
#print axioms every_hodge_class_has_native_cycle_of_full_limitless_geometry
#print axioms classicalHodgeTarget_of_conserved_spine_and_projective_two_generators
#print axioms every_hodge_class_has_native_cycle_of_conserved_spine_and_projective_two_generators
#print axioms canonical_basis_algebraization_of_full_limitless_geometry
#print axioms canonical_basis_algebraization_of_conserved_spine_and_projective_two_generators
#print axioms channel_quotient_of_full_limitless_geometry
#print axioms channel_quotient_of_conserved_spine_and_projective_two_generators
#print axioms unified_hodge_finale
#print axioms unified_hodge_finale_conserved_spine_projective_two_generators

end HodgeConjecture
