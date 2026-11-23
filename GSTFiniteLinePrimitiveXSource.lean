import Mathlib
import GSTFiniteLinePointsGateDischarge
import GSTFiniteLineUnconditionalSource
import GSTFiniteLineHonestHodgeData
import GSTFiniteLineGeneralMLaw
import GSTFiniteLinePointAlgebra

/-
Copyright (c) 2026. The HC-PROOF campaign. All rights reserved.

# THE UNIVERSAL PRIMITIVE-X SOURCE — THE SOURCE-BASIS PACKAGE (wave 9)

THE FINAL MODULE of the finite-line unconditional round: the lane's second
promise ("THE UNCONDITIONAL LAW + universal primitive-X source"), executed
from the frozen statement design
`research/campaign/wave9-universal-source-battle-map.md`.

The mathematics (the classical content, at the honest data of
`GSTFiniteLineHonestHodgeData`): the finite-line world is `M` disjoint
projective lines; its rational Hodge sectors are carried by TWO EXPLICIT
families of honest atoms:

* weight zero — the component family: the generic-point atoms
  `finiteLineSourceZero M i` (the `R₀`-orbit of the honest seed), whose
  classes are the component classes — a ℚ-BASIS of the whole free weight-0
  fiber `H⁰ ≃ (Fin M → ℚ)` (independent unconditionally, spanning the whole
  sector, the compiler with the EXPLICIT coordinate readout);
* weight one — the closed-point family: the closed-point atoms
  `finiteLineSourceOne M i` (the `R₁`-orbit of the honest seed), whose
  classes are the honest point classes — independent at the fenced family
  index (`hω : ω ≠ 0`, the corpus's own liveness discipline) and spanning
  the weight-1 rational Hodge fiber (the span bigrading's own design);
* weights `p ≥ 2` — the honest vacuity: the fiber is the stash design's
  dead fiber (`⊥` by construction — NO cohomology vanishing is claimed or
  used), so every rational Hodge class there is zero.

The COMPILER: the uniform witness map — weight zero takes the EXPLICIT
coordinates (the `componentCohomologyZeroEquivFinM` readout, the honest
component H⁰ machine); weight one takes the §2-witness coordinates (the
Classical choice of the span certificate — the honest noncomputable
construction); the correctness receipts hold for EVERY class of the honest
data.  THE UNIVERSALITY: one recipe at every `M ≥ 1` — the ∀M master
package, conjoined with the gate-free law itself (the lane's first promise,
`native_GST_single_fold_orbit_law_finiteLine_unconditional_gatefree`), at
the constructed unconditional analytification.

HONESTY LEDGER.

Every statement is proved unconditionally (the one disclosed fence: the
weight-one INDEPENDENCE carries `hω : ω ≠ 0` — the corpus has NO green
canonical nonvanishing sphere class, and at `ω = 0` the family is
identically zero, so the unguarded statement is false; the fence is the
campaign's own liveness discipline).  No `sorry`, no new axioms, no
`native_decide`.  Disclosed items:

1. THE ω-FENCE (as above): the span, the compiler and the master package
   are ∀ω; ONLY the weight-one independence demands the nonzero family
   index.
2. THE VACUITY'S HONEST SHAPE: the `p ≥ 2` sector's emptiness is the
   STASH design's dead fiber (the kit's `rationalHodgeSubspace_stash_eq_bot`
   engine — the complexification injectivity), NOT a positive-degree
   vanishing theorem (the sphere machine stays fenced).
3. THE COMPILER'S COORDINATES: weight zero = the explicit E-readout
   (computable content); weight one = the Classical-choice witness of §2
   (noncomputable — the corpus has no green degree-two dual-basis machine);
   the expected `Classical.choice` axiom receipt is the designated honesty
   marker.
4. THE PACKAGE'S LAW CONJUNCT: stated at the CONSTRUCTED unconditional
   analytification (`finiteLineAnalytificationUnconditional M` at the
   constructed gate) — no arbitrary-A claim is smuggled in (the campaign's
   acceptance discipline).

The GitHub CI lane `gst-finite-line-primitive-x-source.yml` owns the kernel
check.
-/

set_option maxHeartbeats 200000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicTopology
open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra
open GSTClassicalHodgeRealizedCorrespondenceKrylovFinale
open GSTClassicalHodgeExactClayStatement
open GSTSphereUnionComponents
open GSTComponentCohomologyZero
open GSTNativeCodimensionCyclePresentation
open GSTSphereUnionPointClassGate
open GSTPositiveDimensionalLawLanding
open GSTPositiveDimensionalLiveCoreKit
open GSTFinitePointHodgeData
open GSTFiniteLineRing
open GSTFiniteLineWorldCarrier
open GSTFiniteLineClosedImmersion
open GSTFiniteLineGeneralMLaw
open GSTFiniteLineOverBase
open GSTFiniteLinePointAlgebra
open GSTFiniteLineHonestHodgeData
open GSTFiniteLineCycleCorrespondence
open GSTFiniteLineAnalytification
open GSTCompleteSingleFoldOrbitLaw
open GSTSingularCohomologyMaps
open GSTSphereCycleLegs
open GSTHodgeSingleHypothesisConditional
open GSTFiniteLinePointsGateDischarge

namespace GSTFiniteLinePrimitiveXSource

/-! ## §0 The local instance bridges (the wave-63 §0 discipline) -/

local instance (priority := high) instHModule
    {V : SmoothProjectiveComplexScheme} (A : AnalytificationData V) (n : Nat) :
    Module ℚ (RationalSingularCohomology A n) :=
  inferInstanceAs (Module ℚ (singularCohomologyOf A.space n))

local instance (priority := high) instHAddCommGroup
    {V : SmoothProjectiveComplexScheme} (A : AnalytificationData V) (n : Nat) :
    AddCommGroup (RationalSingularCohomology A n) :=
  inferInstanceAs (AddCommGroup (singularCohomologyOf A.space n))

/-! ## §1 The source families (the explicit carriers) -/

/-- **THE WEIGHT-ZERO SOURCE FAMILY** — the generic-point atom of line `i`
(the `R₀`-orbit of the honest seed `lineHonestSeedZero M`, at the honest
prime lattice's own atom): the unit codimension-zero cycle at the `i`-th
generic point. -/
noncomputable def finiteLineSourceZero (M : ℕ) [NeZero M] (i : Fin M) :
    codimensionCycles (finiteLineWorld M).X 0 :=
  codimensionPointCycle (finiteLineWorld M).X 0
    ⟨lineGenericPoint M i, lineGenericPoint_coheight M i⟩

/-- **THE WEIGHT-ONE SOURCE FAMILY** — the closed-point atom of line `i`
(the `R₁`-orbit of the honest seed `lineHonestSeedOne M`): the unit
codimension-one cycle at the `i`-th line's closed point. -/
noncomputable def finiteLineSourceOne (M : ℕ) [NeZero M] (i : Fin M) :
    codimensionCycles (finiteLineWorld M).X 1 :=
  codimensionPointCycle (finiteLineWorld M).X 1
    ⟨lineClosedPointAt M i, lineClosedPointAt_coheight M i⟩

/-! ## §2 The class equations (the atom formulas at every index) -/

/-- **THE CLASS EQUATION AT WEIGHT ZERO** — the `i`-th source carrier's
class under the honest data's cycle-class map IS the `i`-th component class
(the honest atom formula + the prime-lattice index receipt, the honest
data's own seed equation at general `i`). -/
theorem finiteLineSourceZero_class (M : ℕ) [NeZero M]
    (A : AnalytificationData (finiteLineWorld M))
    (hspace : A.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2) (i : Fin M) :
    (finiteLineHodgeDataHonest M A hspace ω).cycleClass 0
        (finiteLineSourceZero M i) =
      finiteLineComponentClass M (finiteLineWorld M) A hspace i := by
  show honestCycleClassZero M (finiteLineWorld M) A hspace
      (codimensionPointCycle (finiteLineWorld M).X 0
        ⟨lineGenericPoint M i, lineGenericPoint_coheight M i⟩) = _
  have hatom := honestCycleClassZero_atom M (finiteLineWorld M) A hspace
    ⟨lineGenericPoint M i, lineGenericPoint_coheight M i⟩
  rw [hatom]
  exact congrArg (finiteLineComponentClass M (finiteLineWorld M) A hspace)
    (lineIndexOfGeneric_lineGenericPoint M i)

/-- **THE CLASS EQUATION AT WEIGHT ONE** — the `i`-th source carrier's
class under the honest data's cycle-class map IS the `i`-th point class
(the honest atom formula + the component receipt + the index receipt, the
honest data's own seed equation at general `i`). -/
theorem finiteLineSourceOne_class (M : ℕ) [NeZero M]
    (A : AnalytificationData (finiteLineWorld M))
    (hspace : A.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2) (i : Fin M) :
    (finiteLineHodgeDataHonest M A hspace ω).cycleClass 1
        (finiteLineSourceOne M i) =
      finiteLinePointClass M (finiteLineWorld M) A hspace ω i := by
  show honestCycleClassOne M (finiteLineWorld M) A hspace ω
      (codimensionPointCycle (finiteLineWorld M).X 1
        ⟨lineClosedPointAt M i, lineClosedPointAt_coheight M i⟩) = _
  have hatom := honestCycleClassOne_atom M (finiteLineWorld M) A hspace ω
    ⟨lineClosedPointAt M i, lineClosedPointAt_coheight M i⟩
  rw [hatom]
  have hcomp : lineComponentOf M
      ⟨lineClosedPointAt M i, lineClosedPointAt_coheight M i⟩ =
      ⟨lineGenericPoint M i, lineGenericPoint_coheight M i⟩ :=
    lineClosedPointAt_component M i
  have hidx : lineIndexOfGeneric M
      (lineComponentOf M
        ⟨lineClosedPointAt M i, lineClosedPointAt_coheight M i⟩) = i := by
    rw [hcomp]
    exact lineIndexOfGeneric_lineGenericPoint M i
  exact congrArg (finiteLinePointClass M (finiteLineWorld M) A hspace ω) hidx

/-! ## §3 The independence (the basis certificates) -/

/-- **THE WEIGHT-ZERO INDEPENDENCE** — the component source family's
classes are linearly independent UNCONDITIONALLY: the transported standard
basis (the `Pi.basisFun` singles under the component H⁰ machine's linear
equiv — the green corpus's own route, `GSTPositiveDimensionalLiveCoreLaw`
§2's independence bullet verbatim). -/
theorem finiteLineSourceZero_independent (M : ℕ) [NeZero M]
    (A : AnalytificationData (finiteLineWorld M))
    (hspace : A.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2) :
    LinearIndependent ℚ (fun i : Fin M =>
      (finiteLineHodgeDataHonest M A hspace ω).cycleClass 0
        (finiteLineSourceZero M i)) := by
  have hfun : (fun i : Fin M =>
      (finiteLineHodgeDataHonest M A hspace ω).cycleClass 0
        (finiteLineSourceZero M i))
      = (fun i : Fin M =>
        finiteLineComponentClass M (finiteLineWorld M) A hspace i) :=
    funext fun i => finiteLineSourceZero_class M A hspace ω i
  rw [hfun]
  set E := componentCohomologyZeroEquivFinM A M
    (sphereUnion_cohomology_zero hspace) with hE
  have hbasis : LinearIndependent ℚ
      (fun i => Pi.single i (1 : ℚ) : Fin M → (Fin M → ℚ)) := by
    have hbf : LinearIndependent ℚ
        (fun i => (Pi.basisFun ℚ (Fin M)) i : Fin M → (Fin M → ℚ)) :=
      (Pi.basisFun ℚ (Fin M)).linearIndependent
    rwa [show (fun i => (Pi.basisFun ℚ (Fin M)) i : Fin M → (Fin M → ℚ))
        = fun i => Pi.single i (1 : ℚ) from by
      funext i
      exact Pi.basisFun_apply ℚ (Fin M) i] at hbf
  exact hbasis.map'
    (↑E.symm : (Fin M → ℚ) →ₗ[ℚ] RationalSingularCohomology A 0)
    (LinearMap.ker_eq_bot.mpr (EquivLike.injective E.symm))

/-- **THE WEIGHT-ONE INDEPENDENCE** — the closed-point source family's
classes are linearly independent at the FENCED family index: the green
`finiteLinePointClass_indep` receipt (the transported honest point-class
family) at `hω : ω ≠ 0`.  This is the campaign's disclosed liveness fence
(the corpus has no unconditional nonvanishing sphere class; at `ω = 0` the
family is identically zero). -/
theorem finiteLineSourceOne_independent (M : ℕ) [NeZero M]
    (A : AnalytificationData (finiteLineWorld M))
    (hspace : A.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2)
    (hω : ω ≠ 0) :
    LinearIndependent ℚ (fun i : Fin M =>
      (finiteLineHodgeDataHonest M A hspace ω).cycleClass 1
        (finiteLineSourceOne M i)) := by
  have hfun : (fun i : Fin M =>
      (finiteLineHodgeDataHonest M A hspace ω).cycleClass 1
        (finiteLineSourceOne M i))
      = (fun i : Fin M =>
        finiteLinePointClass M (finiteLineWorld M) A hspace ω i) :=
    funext fun i => finiteLineSourceOne_class M A hspace ω i
  rw [hfun]
  exact finiteLinePointClass_indep M (finiteLineWorld M) A hspace ω hω

/-! ## §4 The decomposition machinery (the weight-zero readout) -/

/-- The function-space decomposition: the standard basis expansion on
`Fin M → ℚ` (the single-evaluator identity). -/
private theorem pi_single_sum_eq (M : ℕ) (f : Fin M → ℚ) :
    ∑ i, f i • Pi.single i (1 : ℚ) = f := by
  funext j
  simp [Pi.single_apply]

/-- **THE E-READOUT DECOMPOSITION** — every degree-zero class is the
explicit combination of the component source family with its OWN
`componentCohomologyZeroEquivFinM` coordinates: the transported
standard-basis expansion (the machine's linearity both ways, the
`symm_apply_apply` round trip).  This is the weight-zero compiler's
correctness engine. -/
private theorem finiteLineComponentClass_decompose (M : ℕ) [NeZero M]
    (A : AnalytificationData (finiteLineWorld M))
    (hspace : A.space = TopCat.of (sphereUnionSpace M))
    (α : RationalSingularCohomology A 0) :
    ∑ i, (componentCohomologyZeroEquivFinM A M
        (sphereUnion_cohomology_zero hspace)) α i •
      finiteLineComponentClass M (finiteLineWorld M) A hspace i = α := by
  set E := componentCohomologyZeroEquivFinM A M
    (sphereUnion_cohomology_zero hspace) with hE
  have hper : ∀ i : Fin M, E (finiteLineComponentClass M
      (finiteLineWorld M) A hspace i) = Pi.single i (1 : ℚ) := by
    intro i
    show E (E.symm (Pi.single i (1 : ℚ))) = _
    exact E.apply_symm_apply (Pi.single i (1 : ℚ))
  have hfwd : E (∑ i, E α i •
      finiteLineComponentClass M (finiteLineWorld M) A hspace i) = E α := by
    calc E (∑ i, E α i •
          finiteLineComponentClass M (finiteLineWorld M) A hspace i)
        = ∑ i, E (E α i •
            finiteLineComponentClass M (finiteLineWorld M) A hspace i) := by
          rw [map_sum]
      _ = ∑ i, E α i • E (finiteLineComponentClass M
            (finiteLineWorld M) A hspace i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_smul]
      _ = ∑ i, E α i • Pi.single i (1 : ℚ) :=
          Finset.sum_congr rfl fun i _ => by rw [hper i]
      _ = E α := pi_single_sum_eq M (E α)
  calc ∑ i, E α i • finiteLineComponentClass M (finiteLineWorld M) A hspace i
      = E.symm (E (∑ i, E α i •
          finiteLineComponentClass M (finiteLineWorld M) A hspace i)) := by
        rw [E.symm_apply_apply]
    _ = E.symm (E α) := by rw [hfwd]
    _ = α := by rw [E.symm_apply_apply]

/-! ## §5 The span (the source theorem proper) -/

/-- **THE SOURCE THEOREM AT WEIGHT ZERO** — every rational Hodge class of
degree zero (the free weight-0 fiber: the single-slot forcing law makes
the whole `H⁰` the fiber) is an explicit finite rational combination of
the component source family, with the EXPLICIT E-readout coordinates. -/
theorem finiteLine_universal_primitive_X_source_zero (M : ℕ) [NeZero M]
    (A : AnalytificationData (finiteLineWorld M))
    (hspace : A.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2) :
    ∀ α : RationalSingularCohomology A 0,
      α ∈ rationalHodgeSubspace
        ((finiteLineHodgeDataHonest M A hspace ω).hodgeBigrading 0) →
        ∃ q : Fin M → ℚ,
          α = ∑ i, q i • (finiteLineHodgeDataHonest M A hspace ω).cycleClass 0
            (finiteLineSourceZero M i) := by
  intro α _hmem
  refine ⟨fun i => (componentCohomologyZeroEquivFinM A M
    (sphereUnion_cohomology_zero hspace)) α i, ?_⟩
  have hsum : ∑ i, (componentCohomologyZeroEquivFinM A M
        (sphereUnion_cohomology_zero hspace)) α i •
        (finiteLineHodgeDataHonest M A hspace ω).cycleClass 0
          (finiteLineSourceZero M i)
      = ∑ i, (componentCohomologyZeroEquivFinM A M
        (sphereUnion_cohomology_zero hspace)) α i •
        finiteLineComponentClass M (finiteLineWorld M) A hspace i :=
    Finset.sum_congr rfl fun i _ =>
      by rw [finiteLineSourceZero_class M A hspace ω i]
  rw [hsum]
  exact (finiteLineComponentClass_decompose M (finiteLineWorld M) A
    hspace α).symm

/-- **THE SOURCE THEOREM AT WEIGHT ONE** — every rational Hodge class of
the honest weight-one fiber (the span bigrading's own rational fiber: the
span of the honest point-class family) is an explicit finite rational
combination of the closed-point source family. -/
theorem finiteLine_universal_primitive_X_source_one (M : ℕ) [NeZero M]
    (A : AnalytificationData (finiteLineWorld M))
    (hspace : A.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2) :
    ∀ α : RationalSingularCohomology A 2,
      α ∈ rationalHodgeSubspace
        ((finiteLineHodgeDataHonest M A hspace ω).hodgeBigrading 1) →
        ∃ q : Fin M → ℚ,
          α = ∑ i, q i • (finiteLineHodgeDataHonest M A hspace ω).cycleClass 1
            (finiteLineSourceOne M i) := by
  intro α hmem
  have hun : (finiteLineHodgeDataHonest M A hspace ω).hodgeBigrading 1
      = spanBigrading (finiteLinePointClass M (finiteLineWorld M) A hspace ω)
        1 (by omega) := rfl
  rw [hun] at hmem
  rw [rationalHodgeSubspace_span_eq] at hmem
  rw [Submodule.mem_span_range_iff_exists_fun] at hmem
  obtain ⟨q, hq⟩ := hmem
  refine ⟨q, ?_⟩
  have hsum : ∑ i, q i • (finiteLineHodgeDataHonest M A hspace ω).cycleClass 1
        (finiteLineSourceOne M i)
      = ∑ i, q i • finiteLinePointClass M (finiteLineWorld M) A hspace ω i :=
    Finset.sum_congr rfl fun i _ =>
      by rw [finiteLineSourceOne_class M A hspace ω i]
  rw [hsum]
  exact hq.symm

/-- **THE SOURCE THEOREM ABOVE** — the vacuity: every rational Hodge class
of every weight `p ≥ 2` of the honest data is ZERO (the stash design's
dead fiber — the kit's injectivity engine; NO positive-degree cohomology
vanishing is claimed). -/
theorem finiteLine_universal_primitive_X_source_above (M : ℕ) [NeZero M]
    (A : AnalytificationData (finiteLineWorld M))
    (hspace : A.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2) :
    ∀ p : ℕ, 1 < p →
      ∀ α : RationalSingularCohomology A (2 * p),
        α ∈ rationalHodgeSubspace
          ((finiteLineHodgeDataHonest M A hspace ω).hodgeBigrading p) →
          α = 0 := by
  intro p hp α hmem
  rw [finiteLineHodgeDataHonest_hstash M A hspace ω p hp] at hmem
  rw [rationalHodgeSubspace_stash_eq_bot p (by omega)] at hmem
  exact (Submodule.mem_bot (R := ℚ)).mp hmem

/-! ## §6 The compiler (the uniform witness map) -/

/-- **THE WEIGHT-ZERO COMPILER** — the explicit readout: the cycle
assembled from the class's OWN component coordinates (the H⁰ machine's
readout, `E α`, times the source carriers).  The recipe takes NO data
beyond `M`, the honest analytification and the class. -/
noncomputable def finiteLineSourceCompilerZero (M : ℕ) [NeZero M]
    (A : AnalytificationData (finiteLineWorld M))
    (hspace : A.space = TopCat.of (sphereUnionSpace M)) :
    RationalSingularCohomology A 0 → codimensionCycles (finiteLineWorld M).X 0 :=
  fun α => ∑ i, (componentCohomologyZeroEquivFinM A M
    (sphereUnion_cohomology_zero hspace)) α i • finiteLineSourceZero M i

/-- **THE WEIGHT-ZERO COMPILER'S CORRECTNESS** — for EVERY degree-zero
class (the whole free sector): the class of the compiled cycle IS the
class (the linearity of the honest cycle-class map + the class equations +
the E-readout decomposition). -/
theorem finiteLineSourceCompilerZero_correct (M : ℕ) [NeZero M]
    (A : AnalytificationData (finiteLineWorld M))
    (hspace : A.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2) :
    ∀ α : RationalSingularCohomology A 0,
      (finiteLineHodgeDataHonest M A hspace ω).cycleClass 0
        (finiteLineSourceCompilerZero M A hspace α) = α := by
  intro α
  have hcls : ∀ i : Fin M,
      (honestCycleClassZero M (finiteLineWorld M) A hspace)
        (finiteLineSourceZero M i) =
      finiteLineComponentClass M (finiteLineWorld M) A hspace i :=
    fun i => finiteLineSourceZero_class M A hspace ω i
  show honestCycleClassZero M (finiteLineWorld M) A hspace
      (∑ i, (componentCohomologyZeroEquivFinM A M
        (sphereUnion_cohomology_zero hspace)) α i •
        finiteLineSourceZero M i) = α
  rw [map_sum]
  simp only [map_smul]
  have hsum : ∑ i, (componentCohomologyZeroEquivFinM A M
        (sphereUnion_cohomology_zero hspace)) α i •
        (honestCycleClassZero M (finiteLineWorld M) A hspace)
          (finiteLineSourceZero M i)
      = ∑ i, (componentCohomologyZeroEquivFinM A M
        (sphereUnion_cohomology_zero hspace)) α i •
        finiteLineComponentClass M (finiteLineWorld M) A hspace i :=
    Finset.sum_congr rfl fun i _ => by rw [hcls i]
  rw [hsum]
  exact finiteLineComponentClass_decompose M (finiteLineWorld M) A hspace α

/-- **THE WEIGHT-ONE COMPILER** — the witness map: for every class of the
honest weight-one fiber, the cycle assembled from the §5-witness
coordinates (the Classical choice of the span certificate — the honest
noncomputable construction; the corpus has no green degree-two
dual-basis machine). -/
noncomputable def finiteLineSourceCompilerOne (M : ℕ) [NeZero M]
    (A : AnalytificationData (finiteLineWorld M))
    (hspace : A.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2) :
    ∀ α : RationalSingularCohomology A 2,
      α ∈ rationalHodgeSubspace
        ((finiteLineHodgeDataHonest M A hspace ω).hodgeBigrading 1) →
        codimensionCycles (finiteLineWorld M).X 1 :=
  fun α _hmem =>
    ∑ i, (Classical.choose
      (finiteLine_universal_primitive_X_source_one M A hspace ω α _hmem)) i •
      finiteLineSourceOne M i

/-- **THE WEIGHT-ONE COMPILER'S CORRECTNESS** — for every class of the
honest weight-one fiber: the class of the compiled cycle IS the class (the
linearity + the chosen witness's own certificate). -/
theorem finiteLineSourceCompilerOne_correct (M : ℕ) [NeZero M]
    (A : AnalytificationData (finiteLineWorld M))
    (hspace : A.space = TopCat.of (sphereUnionSpace M))
    (ω : singularCohomologyOf (TopCat.of unitSphereType) 2) :
    ∀ α : RationalSingularCohomology A 2,
      ∀ hmem : α ∈ rationalHodgeSubspace
        ((finiteLineHodgeDataHonest M A hspace ω).hodgeBigrading 1),
        (finiteLineHodgeDataHonest M A hspace ω).cycleClass 1
          (finiteLineSourceCompilerOne M A hspace ω α hmem) = α := by
  intro α hmem
  show honestCycleClassOne M (finiteLineWorld M) A hspace ω
      (∑ i, (Classical.choose
        (finiteLine_universal_primitive_X_source_one M A hspace ω α hmem)) i •
        finiteLineSourceOne M i) = α
  rw [map_sum]
  simp only [map_smul]
  rw [Classical.choose_spec
    (finiteLine_universal_primitive_X_source_one M A hspace ω α hmem)]
  exact Finset.sum_congr rfl fun i _ => rfl

/-! ## §7 The master package (the ∀M claim) -/

/-- **THE UNIVERSAL PRIMITIVE-X SOURCE PACKAGE** — the master receipt at
the constructed unconditional data: at EVERY `M ≥ 1` and EVERY family
index `ω`, at the honest data of the constructed unconditional
analytification (`finiteLineAnalytificationUnconditional M` at the
constructed points gate),

* the component source family is linearly independent (unconditionally);
* the closed-point source family is linearly independent at the fenced
  index (`hω : ω ≠ 0`);
* every degree-zero rational Hodge class is an explicit combination of
  the component source family; every weight-one rational Hodge class is
  an explicit combination of the closed-point source family; every
  weight-`p ≥ 2` rational Hodge class is zero;
* the compilers are correct at both live sectors;
* AND the gate-free law itself holds (the lane's first promise, at the
  same data).

One recipe at every `M ≥ 1` — the universal source-basis package of the
finite-line world. -/
theorem the_universal_primitive_X_source_package :
    ∀ (M : ℕ) (hM : NeZero M)
      (ω : singularCohomologyOf (TopCat.of unitSphereType) 2),
      LinearIndependent ℚ (fun i : Fin M =>
        (finiteLineHodgeDataHonest M (finiteLineAnalytificationUnconditional M)
          (finiteLineAnalytificationUnconditional_space M) ω).cycleClass 0
          (finiteLineSourceZero M i)) ∧
      (∀ _hω : ω ≠ 0,
        LinearIndependent ℚ (fun i : Fin M =>
          (finiteLineHodgeDataHonest M (finiteLineAnalytificationUnconditional M)
            (finiteLineAnalytificationUnconditional_space M) ω).cycleClass 1
            (finiteLineSourceOne M i))) ∧
      (∀ α : RationalSingularCohomology
          (finiteLineAnalytificationUnconditional M) 0,
        α ∈ rationalHodgeSubspace
          ((finiteLineHodgeDataHonest M (finiteLineAnalytificationUnconditional M)
            (finiteLineAnalytificationUnconditional_space M) ω).hodgeBigrading 0) →
        ∃ q : Fin M → ℚ,
          α = ∑ i, q i • (finiteLineHodgeDataHonest M
            (finiteLineAnalytificationUnconditional M)
            (finiteLineAnalytificationUnconditional_space M) ω).cycleClass 0
            (finiteLineSourceZero M i)) ∧
      (∀ α : RationalSingularCohomology
          (finiteLineAnalytificationUnconditional M) 2,
        α ∈ rationalHodgeSubspace
          ((finiteLineHodgeDataHonest M (finiteLineAnalytificationUnconditional M)
            (finiteLineAnalytificationUnconditional_space M) ω).hodgeBigrading 1) →
        ∃ q : Fin M → ℚ,
          α = ∑ i, q i • (finiteLineHodgeDataHonest M
            (finiteLineAnalytificationUnconditional M)
            (finiteLineAnalytificationUnconditional_space M) ω).cycleClass 1
            (finiteLineSourceOne M i)) ∧
      (∀ p : ℕ, 1 < p →
        ∀ α : RationalSingularCohomology
          (finiteLineAnalytificationUnconditional M) (2 * p),
        α ∈ rationalHodgeSubspace
          ((finiteLineHodgeDataHonest M (finiteLineAnalytificationUnconditional M)
            (finiteLineAnalytificationUnconditional_space M) ω).hodgeBigrading p) →
        α = 0) ∧
      (∀ α : RationalSingularCohomology
          (finiteLineAnalytificationUnconditional M) 0,
        (finiteLineHodgeDataHonest M (finiteLineAnalytificationUnconditional M)
          (finiteLineAnalytificationUnconditional_space M) ω).cycleClass 0
          (finiteLineSourceCompilerZero M
            (finiteLineAnalytificationUnconditional M)
            (finiteLineAnalytificationUnconditional_space M) α) = α) ∧
      (∀ α : RationalSingularCohomology
          (finiteLineAnalytificationUnconditional M) 2,
        ∀ hmem : α ∈ rationalHodgeSubspace
          ((finiteLineHodgeDataHonest M (finiteLineAnalytificationUnconditional M)
            (finiteLineAnalytificationUnconditional_space M) ω).hodgeBigrading 1),
        (finiteLineHodgeDataHonest M (finiteLineAnalytificationUnconditional M)
          (finiteLineAnalytificationUnconditional_space M) ω).cycleClass 1
          (finiteLineSourceCompilerOne M
            (finiteLineAnalytificationUnconditional M)
            (finiteLineAnalytificationUnconditional_space M) ω α hmem) = α) ∧
      NativeGSTSingleFoldOrbitLaw (finiteLineWorld M)
        (finiteLineHodgeDataHonest M (finiteLineAnalytificationUnconditional M)
          (finiteLineAnalytificationUnconditional_space M) ω) := by
  intro M hM ω
  haveI : NeZero M := hM
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact finiteLineSourceZero_independent M
      (finiteLineAnalytificationUnconditional M)
      (finiteLineAnalytificationUnconditional_space M) ω
  · exact fun _hω => finiteLineSourceOne_independent M
      (finiteLineAnalytificationUnconditional M)
      (finiteLineAnalytificationUnconditional_space M) ω _hω
  · exact finiteLine_universal_primitive_X_source_zero M
      (finiteLineAnalytificationUnconditional M)
      (finiteLineAnalytificationUnconditional_space M) ω
  · exact finiteLine_universal_primitive_X_source_one M
      (finiteLineAnalytificationUnconditional M)
      (finiteLineAnalytificationUnconditional_space M) ω
  · exact finiteLine_universal_primitive_X_source_above M
      (finiteLineAnalytificationUnconditional M)
      (finiteLineAnalytificationUnconditional_space M) ω
  · exact finiteLineSourceCompilerZero_correct M
      (finiteLineAnalytificationUnconditional M)
      (finiteLineAnalytificationUnconditional_space M) ω
  · exact finiteLineSourceCompilerOne_correct M
      (finiteLineAnalytificationUnconditional M)
      (finiteLineAnalytificationUnconditional_space M) ω
  · exact native_GST_single_fold_orbit_law_finiteLine_unconditional_gatefree M ω

/-! ## Receipts -/

#check finiteLineSourceZero
#check finiteLineSourceOne
#check finiteLineSourceZero_class
#check finiteLineSourceOne_class
#check finiteLineSourceZero_independent
#check finiteLineSourceOne_independent
#check finiteLine_universal_primitive_X_source_zero
#check finiteLine_universal_primitive_X_source_one
#check finiteLine_universal_primitive_X_source_above
#check finiteLineSourceCompilerZero
#check finiteLineSourceCompilerOne
#check the_universal_primitive_X_source_package

#check native_GST_single_fold_orbit_law_finiteLine_unconditional_gatefree
#check finiteLineAnalytificationUnconditional
#check finiteLineAnalytificationUnconditional_space
#check finiteLineHodgeDataHonest

#print axioms finiteLineSourceZero_class
#print axioms finiteLineSourceOne_class
#print axioms finiteLineSourceZero_independent
#print axioms finiteLineSourceOne_independent
#print axioms finiteLine_universal_primitive_X_source_zero
#print axioms finiteLine_universal_primitive_X_source_one
#print axioms finiteLine_universal_primitive_X_source_above
#print axioms finiteLineSourceCompilerZero_correct
#print axioms finiteLineSourceCompilerOne_correct
#print axioms the_universal_primitive_X_source_package

end GSTFiniteLinePrimitiveXSource

end -- noncomputable section

/-
PORT NOTES (the designated CI repair points of this file):

* (SRC-1) `pi_single_sum_eq`'s `simp [Pi.single_apply]` (the ite-collapse
  on the applied sum): if the simp set stalls, the fallback is the
  `Finset.sum_eq_single j` route (the per-index evaluation receipt); the
  identity is the standard function-space basis expansion.
* (SRC-2) `Submodule.mem_span_range_iff_exists_fun` is consumed as a REWRITE
  (never applied bare) in `finiteLine_universal_primitive_X_source_one`:
  the rw's unification resolves the lemma's argument structure against the
  hypothesis's own type (the pin's `RingTheory_Ideal_Operations.lean:1370`
  receipt proves the name lives at v4.33.0-rc2; the corpus-green
  `rw`-discipline of the Clay statement's own sum handling).
* (SRC-3) the `show`-unfolds of the honest data's `cycleClass`
  (projection-then-match) and of `finiteLineComponentClass` /
  `finiteLineSourceCompiler*` (plain defs) are the wave-68
  default-transparency discipline; the honest data's own seed equations
  are the green precedent for every one of them.
* (SRC-4) `E.apply_symm_apply` / `E.symm_apply_apply` /
  `LinearMap.ker_eq_bot` / `EquivLike.injective` / `map_sum` / `map_smul`:
  every one consumed at the green corpus's own spelling
  (`GSTPositiveDimensionalLiveCoreLaw` §2 / `GSTFiniteLineGeneralMLaw`
  §2.1); the `set E := ... with hE` discipline matches the corpus's own.
* (SRC-5) the package's anonymous constructor flattens the 8-conjunct
  right-associated conjunction; if the elaborator miscounts, the fallback
  is the nested `refine ⟨_, ⟨_, ...⟩⟩` spelling.
-/
