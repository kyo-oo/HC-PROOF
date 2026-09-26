import GSTClassicalHodgeFullLimitlessExternalization
import GSTClassicalHodgeLimitlessSpinePropagation
import GSTClassicalHodgeCanonicalLimitlessNaturalityCrown
import HodgeConjecture

/-!
# GST CLASSICAL HODGE — FULL LIMITLESS CROWN

This is the final composition layer of the current limitless derivation.

All internal algebra has already been discharged upstream:

* unrestricted classical Hodge multiplicity coordinates;
* finite-support localization and arbitrary world recoordination;
* exact sheet projectors and spectral extraction;
* true limitless cosmic Poincare read/write matrix units;
* Lefschetz propagation with nonzero central-binomial coefficients;
* genuine projective native-cycle normal form and principal-cut operators;
* native/cosmic transfer-address identification;
* tensor commutation of multiplicity and projective actions;
* rank-free irreducibility/no-escape saturation.

The geometric cycle-class spine now generates the cross-weight algebraic tower
itself.  Thus the global Hodge statement follows as soon as two geometric facts
about the *genuine* classical cycle-class semantics are established:

1. the canonical spine tower is nonzero in every nonzero Hodge weight;
2. the true limitless cosmic read/write action is externalized by genuine
   projective-correspondence operators.

Neither item is a basis-cycle family or a surjectivity statement.  The theorem
below shows that after the entire limitless cosmology has been used, there are
no further internal GST obligations hiding behind the classical landing.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeFullLimitlessCrown

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeLimitlessTwoSlotFailureDichotomy
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeProjectiveCorrespondenceAlgebra
open GSTClassicalHodgeFullLimitlessExternalization
open GSTClassicalHodgeLimitlessSpinePropagation
open GSTClassicalHodgeCanonicalLimitlessNaturalityCrown

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- The canonical projective/Hodge spine tower does not vanish in a live Hodge
weight.  This is the standard geometric nonvanishing artery: the seed itself
is already constructed by `spineHodgeSeed`; only its nonvanishing is asserted
here. -/
def SpineTowerNonvanishing
    (G : GeometricCycleClassSpine V H) : Prop :=
  ∀ p : Nat,
    rationalHodgeSubspace (H.hodgeBigrading p) ≠ ⊥ →
      spineHodgeSeed G p ≠ 0

/-- Genuine projective realization of the one true limitless cosmic read/write
operator in every weight and every ordered multiplicity pair.  The operator is
not an abstract Hodge matrix unit: it must come from the actual projective
correspondence sector constructed from scheme geometry. -/
def FullProjectiveCosmicExternalization
    (G : GeometricCycleClassSpine V H) : Prop :=
  ∀ p : Nat,
  ∀ i j : ClassicalHodgeBasisIndex V H p,
    ∃ K : ProjectiveNativeKernel V p,
      AtomCosmicExternalization G i j K

/-- A full projective externalization gives canonical cosmic naturality in every
weight. -/
theorem canonicalCosmicNaturality_of_fullProjectiveExternalization
    (G : GeometricCycleClassSpine V H)
    (R : FullProjectiveCosmicExternalization G) :
    ∀ p : Nat, CanonicalCosmicNaturality (V := V) (H := H) p := by
  intro p
  let K : ∀ i j : ClassicalHodgeBasisIndex V H p,
      ProjectiveNativeKernel V p :=
    fun i j => Classical.choose (R p i j)
  have hK : ∀ i j : ClassicalHodgeBasisIndex V H p,
      AtomCosmicExternalization G i j (K i j) := by
    intro i j
    exact Classical.choose_spec (R p i j)
  exact canonicalCosmicNaturality_of_fullLimitlessExternalization G K hK

/-- Nonvanishing of the canonical spine tower supplies the one algebraic seed
required by the rank-free no-escape theorem in every live weight. -/
theorem algebraicFiber_ne_bot_of_spineTower
    (G : GeometricCycleClassSpine V H)
    (hNV : SpineTowerNonvanishing G)
    (p : Nat)
    (hH : rationalHodgeSubspace (H.hodgeBigrading p) ≠ ⊥) :
    AlgebraicFiber (V := V) (H := H) (p := p) ≠ ⊥ := by
  have hseed : spineHodgeSeed G p ≠ 0 := hNV p hH
  have halg : spineHodgeSeed G p ∈ AlgebraicHodgeSubspace V H p :=
    spineHodgeSeed_algebraic G p
  intro hbot
  have hz : spineHodgeSeed G p = 0 := by
    have hm : spineHodgeSeed G p ∈
        (⊥ : Submodule ℚ (ClassicalHodgeFiber V H p)) := by
      rw [← hbot]
      exact halg
    simpa using hm
  exact hseed hz

/-- **FULL LIMITLESS CLASSICAL HODGE CROWN.**
The genuine cycle-class spine, nonvanishing of its canonical projective tower,
and geometric externalization of the already-constructed cosmic read/write
operator imply the exact Stage-2G rational Hodge statement. -/
theorem bigradedBettiHodge
    (G : GeometricCycleClassSpine V H)
    (hNV : SpineTowerNonvanishing G)
    (R : FullProjectiveCosmicExternalization G) :
    BigradedBettiHodgeStatement V H := by
  intro p alpha halpha
  by_cases hH : rationalHodgeSubspace (H.hodgeBigrading p) = ⊥
  · have hz : alpha = 0 := by
      have : alpha ∈ (⊥ : Submodule ℚ
          (RationalSingularCohomology H.analytification (2 * p))) := by
        simpa [hH] using halpha
      simpa using this
    subst alpha
    exact LinearMap.zero_mem _
  · exact hodge_weight
      (algebraicFiber_ne_bot_of_spineTower G hNV p hH)
      (canonicalCosmicNaturality_of_fullProjectiveExternalization G R p)
      halpha

/-- The same crown lands directly in the exact public target isolated by
`HodgeConjecture.lean`. -/
theorem classicalHodgeTarget
    (G : GeometricCycleClassSpine V H)
    (hNV : SpineTowerNonvanishing G)
    (R : FullProjectiveCosmicExternalization G) :
    HodgeConjecture.ClassicalHodgeTarget V H :=
  bigradedBettiHodge G hNV R

/-- Elementwise form: every genuine rational `(p,p)` class receives an actual
native codimension-p algebraic cycle. -/
theorem every_hodge_class_has_native_cycle
    (G : GeometricCycleClassSpine V H)
    (hNV : SpineTowerNonvanishing G)
    (R : FullProjectiveCosmicExternalization G)
    (p : Nat)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p)) :
    ∃ Z : GSTGeometricRealizationStage2D.codimensionCycles V.X p,
      H.cycleClass p Z = alpha := by
  exact bigradedBettiHodge G hNV R p alpha halpha

/-- There is no remaining finite-rank/countability restriction in the final
crown: every Hodge fiber uses its unrestricted basis index and every actual
class is handled through finite support locally. -/
theorem full_limitless_rank_free_crown
    (G : GeometricCycleClassSpine V H)
    (hNV : SpineTowerNonvanishing G)
    (R : FullProjectiveCosmicExternalization G) :
    (∀ p : Nat,
      rationalHodgeSubspace (H.hodgeBigrading p) ≤
        LinearMap.range (H.cycleClass p))
    ∧ HodgeConjecture.ClassicalHodgeTarget V H := by
  have h := bigradedBettiHodge G hNV R
  exact ⟨h, h⟩

#check SpineTowerNonvanishing
#check FullProjectiveCosmicExternalization
#check canonicalCosmicNaturality_of_fullProjectiveExternalization
#check algebraicFiber_ne_bot_of_spineTower
#check bigradedBettiHodge
#check classicalHodgeTarget
#check every_hodge_class_has_native_cycle
#check full_limitless_rank_free_crown

#print axioms canonicalCosmicNaturality_of_fullProjectiveExternalization
#print axioms algebraicFiber_ne_bot_of_spineTower
#print axioms bigradedBettiHodge
#print axioms classicalHodgeTarget
#print axioms full_limitless_rank_free_crown

end GSTClassicalHodgeFullLimitlessCrown
