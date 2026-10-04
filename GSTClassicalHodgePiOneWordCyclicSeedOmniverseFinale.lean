import GSTClassicalHodgePiProjectiveSpectralOmniverseFinale
import GSTClassicalHodgePrincipalCutSpectralFusion
import GSTClassicalHodgeRecoordinationArsenalCrown
import GSTClassicalHodgeThreeUniverseSeedIdentification

/-!
# GST CLASSICAL HODGE — PI ONE-WORD / ONE-CYCLIC-SEED OMNIVERSE FINALE

The preceding Pi/projective-spectral crown still exposed coordinatewise
visibility as a family of geometric witnesses. The handwritten Pi/GST route
is intrinsically one-source: a finite live observation is born from one
algebraic state, the GST arsenal separates its active branches, and the finite
rational collapse returns to the same projective carrier.

For one nonzero Hodge state `alpha`, the geometric input is compressed to:

* ONE genuine finite projective operator word whose canonical cohomological
  action is the canonical zero-complement GST observable on `supp(alpha)`;
* ONE genuine native codimension-p cycle whose class is a cyclic vector on
  exactly those live basis directions, with every live coefficient nonzero.

There is no coordinatewise family of visible algebraic witnesses. The single
native cyclic vector feeds the one-word spectral calculus, and the canonical
Lagrange projectors recover every live Hodge basis sheet. The finite support
sum then reconstructs `alpha` as one genuine native cycle.

The same finite packet is simultaneously tied to the canonical live-support
GST chart and all recoordination charts, the exact N-cohomology packet, all
three GST sectors and the unbounded higher-causal tower, and the limitless
native-cycle transfer address of the one cyclic source.
-/

set_option maxHeartbeats 200000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry

namespace GSTClassicalHodgePiOneWordCyclicSeedOmniverseFinale

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeCanonicalSpectralObservable
open GSTClassicalHodgeFiniteSupportArsenalConjugation
open GSTClassicalHodgeRecoordinationArsenalCrown
open GSTClassicalHodgeProjectiveWordOrbit
open GSTClassicalHodgeProjectiveSpectralCover
open GSTClassicalHodgePrincipalCutSpectralFusion
open GSTClassicalHodgePiOmniverseCanonicalSupportSpectral
open GSTClassicalHodgePiProjectiveSpectralOmniverseFinale
open GSTClassicalHodgeOmniverseCausalBranchPacket
open GSTClassicalHodgePiUnboundedOmniverseCrown
open GSTClassicalHodgeNativeCycleCosmicShadow
open GSTClassicalHodgeNativeTransferAddressIdentification
open GSTClassicalHodgeTransferSeedUniverse
open GSTTransferBridgeV2
open GSTGraphV2OmniversalCore

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- One projective word and one actual native cyclic source on the exact live
support. No coordinatewise family of algebraic witnesses is stored. -/
structure CanonicalOneWordCyclicSeedPacket
    (G : GeometricCycleClassSpine V H)
    (alpha : ClassicalHodgeFiber V H p) where
  word : ProjectiveOperatorWord V p
  word_on_hodge :
    ∀ beta : ClassicalHodgeFiber V H p,
      (word.operatorPair G).cohomologyOperator beta.1 =
        (canonicalLiveWindow alpha).ambientObservable beta.1
  coefficient : Fin (liveRank alpha) → ℚ
  coefficient_ne_zero : ∀ i, coefficient i ≠ 0
  seedCycle : codimensionCycles V.X p
  seed_class :
    H.cycleClass p seedCycle =
      ∑ i : Fin (liveRank alpha),
        coefficient i •
          (classicalHodgeBasis V H p (liveBasisIndex alpha i)).1

namespace CanonicalOneWordCyclicSeedPacket

variable {G : GeometricCycleClassSpine V H}
variable {alpha : ClassicalHodgeFiber V H p}

/-- The one word automatically carries the canonical distinct spectral labels
on the exact live support. -/
noncomputable def spectral
    (P : CanonicalOneWordCyclicSeedPacket G alpha) :
    ProjectiveWordSpectralFamily
      (V := V) (H := H) (p := p) G (Fin (liveRank alpha)) where
  word := P.word
  basisIndex := liveBasisIndex alpha
  basisIndex_injective := by
    exact (canonicalLiveWindow alpha).basisIndex_injective
  eigenvalue := (canonicalLiveWindow alpha).eigenvalue
  eigenvalue_injective := (canonicalLiveWindow alpha).eigenvalue_injective
  eigenvector := by
    intro i
    rw [P.word_on_hodge (classicalHodgeBasis V H p (liveBasisIndex alpha i))]
    exact (canonicalLiveWindow alpha).ambientObservable_selected i

/-- The single native source is already one cyclic algebraic vector for the
canonical spectral family. -/
theorem cyclic_seed_atomic
    (P : CanonicalOneWordCyclicSeedPacket G alpha) :
    (∑ i : Fin (liveRank alpha),
      P.coefficient i •
        (classicalHodgeBasis V H p (liveBasisIndex alpha i)).1) ∈
      pointCycleClassSpan p (H.cycleClass p) := by
  have hrange :
      (∑ i : Fin (liveRank alpha),
        P.coefficient i •
          (classicalHodgeBasis V H p (liveBasisIndex alpha i)).1) ∈
        LinearMap.range (H.cycleClass p) := by
    exact ⟨P.seedCycle, P.seed_class⟩
  rwa [smoothProjective_cycleClass_range_eq_atomic_span V H p] at hrange

/-- One cyclic native source plus one projective spectral word extracts every
live basis sheet. -/
theorem live_basis_algebraic
    (P : CanonicalOneWordCyclicSeedPacket G alpha)
    (i : Fin (liveRank alpha)) :
    (classicalHodgeBasis V H p (liveBasisIndex alpha i)).1 ∈
      pointCycleClassSpan p (H.cycleClass p) := by
  exact P.spectral.toClassicalHodgeSpectralOperator
    |>.selected_basis_algebraic_of_cyclic_seed
      P.coefficient P.coefficient_ne_zero P.cyclic_seed_atomic i

/-- Every actual support index of `alpha` is therefore an algebraic basis
sheet. -/
theorem support_basis_algebraic
    (P : CanonicalOneWordCyclicSeedPacket G alpha)
    (i : HodgeSupportIndex alpha) :
    (classicalHodgeBasis V H p i.1).1 ∈
      pointCycleClassSpan p (H.cycleClass p) := by
  obtain ⟨r, hr⟩ := supportIndex_has_canonicalSlot alpha i
  have h := P.live_basis_algebraic r
  rw [show liveBasisIndex alpha r = i.1 by exact hr]
  exact h

/-- Finite support collapses back to one genuine native cycle on the original
projective carrier. -/
theorem target_cycle
    (P : CanonicalOneWordCyclicSeedPacket G alpha) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha.1 := by
  have hmem :
      alpha.1 ∈ pointCycleClassSpan p (H.cycleClass p) := by
    rw [hodgeClass_eq_support_sum alpha]
    apply Submodule.sum_mem
    intro i hi
    exact (pointCycleClassSpan p (H.cycleClass p)).smul_mem
      ((classicalHodgeBasis V H p).repr alpha i.1)
      (P.support_basis_algebraic i)
  exact pointCycleClassSpan_le_cycleClass_range
    p (H.cycleClass p) hmem

/-- The cyclic native source is tethered to the original limitless transfer
universe by its exact native mass. -/
theorem seed_limitless_address
    (P : CanonicalOneWordCyclicSeedPacket G alpha) :
    pureWeightToUniversalAddress
        (nativeCycleCosmicShadow V p P.seedCycle) =
      nativeCycleMass V p P.seedCycle •
        rationalizeCompactAddress (compactClMono p) := by
  exact nativeCycle_shadow_eq_mass_transfer V p P.seedCycle

end CanonicalOneWordCyclicSeedPacket

/-- Full Pi/GST crown: target cycle, exact N-cohomology packet, all-sector
branching with unbounded higher causality, arbitrary finite recoordination,
and the limitless native transfer tether occur simultaneously. -/
theorem oneWordCyclicSeed_pi_fullOmniverse_crown
    (G : GeometricCycleClassSpine V H)
    (depth : Nat)
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0)
    (P : CanonicalOneWordCyclicSeedPacket G alpha) :
    (∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha.1)
    ∧
    (∃ basis : Fin (liveRank alpha) →
        GSTNCohomology.nCohoClasses depth (liveSupportNShape alpha) 1,
      ∀ i : Fin (liveRank alpha),
        (basis i).1 i =
          GSTNCohomology.towerWindow depth
            ((liveSupportNShape alpha).channel i) 1)
    ∧
    (∀ s : Sector, ∀ j : ClassicalHodgeBasisIndex V H p,
      ∃ i : HodgeSupportIndex alpha,
        hodgeCoordinate i.1 alpha ≠ 0 ∧
        (hodgeBranchGraph (V := V) (H := H) (p := p)).Event
          ⟨Sector.gstPlus, alpha⟩
          ⟨s, hodgeMatrixUnit i.1 j alpha⟩
        ∧ ∀ n : Nat,
          ∃ c : (hodgeHigherCausalCosmos
            (V := V) (H := H) (p := p)).Cell n,
            c = ⟨s, hodgeMatrixUnit i.1 j alpha⟩)
    ∧
    (∀ T : GSTWorldShape (liveRank alpha),
      ∀ r : Fin (liveRank alpha),
        transportCoefQ (liveLinearShape alpha) T
            (codeSectorProjQ (liveLinearShape alpha) r.1
              (liveShapeCoefQ alpha)) =
          codeSectorProjQ T r.1
            (transportCoefQ (liveLinearShape alpha) T
              (liveShapeCoefQ alpha)))
    ∧
    pureWeightToUniversalAddress
        (nativeCycleCosmicShadow V p P.seedCycle) =
      nativeCycleMass V p P.seedCycle •
        rationalizeCompactAddress (compactClMono p) := by
  refine ⟨P.target_cycle,
    packet_has_exact_ncohomology depth alpha, ?_, ?_, P.seed_limitless_address⟩
  · intro s j
    exact supportBranch_has_unbounded_causal_certificate alpha halpha s j
  · intro T r
    exact live_projector_recoordination_natural alpha T r

/-- Pi-wide exact rational Hodge landing from one projective word and one
native cyclic source for every nonzero concrete Hodge state. -/
theorem bigradedBettiHodge_of_oneWordCyclicSeedPackets
    (G : GeometricCycleClassSpine V H)
    (packet :
      ∀ q : Nat, ∀ alpha : ClassicalHodgeFiber V H q,
        alpha ≠ 0 →
          Nonempty
            (CanonicalOneWordCyclicSeedPacket
              (V := V) (H := H) (p := q) G alpha)) :
    BigradedBettiHodgeStatement V H := by
  intro q x hx
  let alpha : ClassicalHodgeFiber V H q := ⟨x, hx⟩
  by_cases halpha : alpha = 0
  · have hx0 : x = 0 := congrArg Subtype.val halpha
    subst x
    exact LinearMap.zero_mem _
  · exact (Classical.choice (packet q alpha halpha)).target_cycle

#check CanonicalOneWordCyclicSeedPacket
#check CanonicalOneWordCyclicSeedPacket.spectral
#check CanonicalOneWordCyclicSeedPacket.cyclic_seed_atomic
#check CanonicalOneWordCyclicSeedPacket.live_basis_algebraic
#check CanonicalOneWordCyclicSeedPacket.target_cycle
#check CanonicalOneWordCyclicSeedPacket.seed_limitless_address
#check oneWordCyclicSeed_pi_fullOmniverse_crown
#check bigradedBettiHodge_of_oneWordCyclicSeedPackets

#print axioms CanonicalOneWordCyclicSeedPacket.live_basis_algebraic
#print axioms CanonicalOneWordCyclicSeedPacket.target_cycle
#print axioms oneWordCyclicSeed_pi_fullOmniverse_crown
#print axioms bigradedBettiHodge_of_oneWordCyclicSeedPackets

end GSTClassicalHodgePiOneWordCyclicSeedOmniverseFinale
