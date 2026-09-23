import Mathlib
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Algebra.Module.Submodule.RestrictScalars
import Mathlib.Order.SupIndep
import GSTGeometricRealizationStage2F
import GSTGlobalPureHodgeCosmology
import GSTMultiAxisCosmology

/-!
# STAGE 2G — HODGE BIGRADING AND DERIVED RATIONAL (p,p)-CLASSES

Stage 2F replaced the arbitrary rational cohomology carrier by Mathlib's
actual rational singular cohomology of a supplied analytification.

Stage 2G removes the next arbitrary field: the rational Hodge subspace.

For a rational vector space V_Q we form the genuine scalar extension

  V_C = C tensor_Q V_Q.

A weight-n Hodge bigrading is represented by complex submodules

  H^(a,n-a),  0 <= a <= n,

which are independent and span V_C.  The rational (p,p)-classes in degree
2p are then DEFINED by pulling H^(p,p) back along the canonical map

  V_Q -> V_C,  alpha |-> 1 tensor alpha.

Thus hodgePP is no longer supplied independently.

Important boundary:
* this file formalizes the algebraic shape of a Hodge decomposition;
* it does not yet construct the decomposition analytically;
* conjugation symmetry H^(a,b) bar = H^(b,a) is deliberately left for the
  next strengthening layer rather than silently assumed here;
* no cycle-class surjectivity or algebraicity statement occurs in the
  Hodge-bigrading data.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2E
open GSTGeometricRealizationStage2F
open GSTGlobalPureHodgeCosmology

namespace GSTGeometricRealizationStage2G

/-- Scalar extension of a rational vector space to the complex numbers. -/
abbrev Complexification
    (VQ : Type) [AddCommGroup VQ] [Module ℚ VQ] : Type :=
  TensorProduct ℚ ℂ VQ

/-- The canonical rational-linear inclusion into complexification,
alpha |-> 1 tensor alpha. -/
noncomputable def complexificationMapQ
    (VQ : Type) [AddCommGroup VQ] [Module ℚ VQ] :
    VQ →ₗ[ℚ] Complexification VQ :=
  TensorProduct.mk ℚ ℂ VQ 1

@[simp]
theorem complexificationMapQ_apply
    (VQ : Type) [AddCommGroup VQ] [Module ℚ VQ]
    (x : VQ) :
    complexificationMapQ VQ x = (1 : ℂ) ⊗ₜ[ℚ] x :=
  rfl

/-- A finite weight-n complex Hodge bigrading.

Index a : Fin (n+1) represents the component H^(a,n-a).
The two fields say exactly that these components form an internal direct
sum whose total is the whole complexification. -/
structure HodgeBigrading
    (VQ : Type) [AddCommGroup VQ] [Module ℚ VQ]
    (n : Nat) where
  component :
    Fin (n + 1) → Submodule ℂ (Complexification VQ)
  independent :
    iSupIndep component
  spans :
    (⨆ a, component a) = ⊤

/-- The diagonal index p inside a weight-2p Hodge bigrading. -/
def ppIndex (p : Nat) : Fin (2 * p + 1) :=
  ⟨p, by omega⟩

/-- The complex H^(p,p) component in weight 2p. -/
def HodgeBigrading.ppComponent
    {VQ : Type} [AddCommGroup VQ] [Module ℚ VQ]
    {p : Nat}
    (D : HodgeBigrading VQ (2 * p)) :
    Submodule ℂ (Complexification VQ) :=
  D.component (ppIndex p)

/-- Rational Hodge classes are not independent input data.

They are the pullback of the complex H^(p,p) summand along the canonical
rational-to-complex scalar-extension map. -/
noncomputable def rationalHodgeSubspace
    {VQ : Type} [AddCommGroup VQ] [Module ℚ VQ]
    {p : Nat}
    (D : HodgeBigrading VQ (2 * p)) :
    Submodule ℚ VQ :=
  ((D.ppComponent).restrictScalars ℚ).comap
    (complexificationMapQ VQ)

theorem mem_rationalHodgeSubspace_iff
    {VQ : Type} [AddCommGroup VQ] [Module ℚ VQ]
    {p : Nat}
    (D : HodgeBigrading VQ (2 * p))
    (alpha : VQ) :
    alpha ∈ rationalHodgeSubspace D ↔
      complexificationMapQ VQ alpha ∈ D.ppComponent :=
  Iff.rfl

/-- Stage-2G semantic data.

The Betti cohomology is already fixed by Stage 2F.
The rational Hodge subspace is derived from hodgeBigrading.
Only the actual Hodge bigrading and the actual cycle-class map remain as
geometric input. -/
structure HodgeBigradedBettiData
    (V : SmoothProjectiveComplexScheme) where
  analytification : AnalytificationData V
  hodgeBigrading :
    ∀ p : Nat,
      HodgeBigrading
        (RationalSingularCohomology analytification (2 * p))
        (2 * p)
  cycleClass :
    ∀ p : Nat,
      codimensionCycles V.X p →ₗ[ℚ]
        RationalSingularCohomology analytification (2 * p)

/-- Forget the extra Hodge-decomposition structure and land canonically in
Stage 2F.  The hodgePP field is generated, not supplied. -/
noncomputable def HodgeBigradedBettiData.toBettiHodgeData
    {V : SmoothProjectiveComplexScheme}
    (H : HodgeBigradedBettiData V) :
    BettiHodgeData V where
  analytification := H.analytification
  hodgePP := fun p =>
    rationalHodgeSubspace (H.hodgeBigrading p)
  cycleClass := H.cycleClass

/-- The exact Hodge target after the (p,p)-subspace has been derived from
the complex Hodge bigrading. -/
def BigradedBettiHodgeStatement
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) : Prop :=
  ∀ p : Nat,
    rationalHodgeSubspace (H.hodgeBigrading p) ≤
      LinearMap.range (H.cycleClass p)

/-- Stage-2G's target is definitionally Stage-2F's target under the derived
Hodge-subspace specialization. -/
theorem bigradedBettiHodgeStatement_iff_stage2f
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) :
    BigradedBettiHodgeStatement V H ↔
      BettiHodgeStatement V H.toBettiHodgeData :=
  Iff.rfl

/-- Stage-2G realization certificate: the Stage-2F certificate after
specializing its Hodge subspace to the one derived from the bigrading. -/
abbrev Stage2GClassRealization
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p N : Nat) :=
  Stage2FClassRealization
    V H.toBettiHodgeData p N

/-- Every class whose complexification lies in H^(p,p) obtains an actual
codimension-p algebraic-cycle witness from a Stage-2G realization. -/
theorem hodge_class_has_bigraded_cycle
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    {p N : Nat}
    (R : Stage2GClassRealization V H p N)
    (alpha :
      RationalSingularCohomology H.analytification (2 * p))
    (halpha :
      complexificationMapQ
          (RationalSingularCohomology H.analytification (2 * p))
          alpha
        ∈ (H.hodgeBigrading p).ppComponent) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha := by
  apply hodge_class_has_betti_cycle
    V H.toBettiHodgeData R alpha
  exact (mem_rationalHodgeSubspace_iff
    (H.hodgeBigrading p) alpha).2 halpha

/-- STAGE-2G BIGRADED BETTI LANDING THEOREM.

Once every codimension admits an explicit realization certificate, the
Hodge target follows with:
* native rational singular cohomology;
* rational (p,p)-classes derived from a spanning independent Hodge bigrading;
* native codimension-p algebraic cycles. -/
theorem bigraded_betti_hodge_of_stage2g_family
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (N : Nat -> Nat)
    (R : ∀ p : Nat, Stage2GClassRealization V H p (N p)) :
    BigradedBettiHodgeStatement V H := by
  intro p alpha halpha
  exact hodge_class_has_betti_cycle
    V H.toBettiHodgeData (R p) alpha halpha

/-- The exact remaining Stage-2G realization obligation. -/
def Stage2GRealizationObligation
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) : Prop :=
  ∃ N : Nat -> Nat,
    ∀ p : Nat,
      Nonempty (Stage2GClassRealization V H p (N p))

theorem bigraded_betti_hodge_of_stage2g_obligation
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (hR : Stage2GRealizationObligation V H) :
    BigradedBettiHodgeStatement V H := by
  rcases hR with ⟨N, hN⟩
  exact bigraded_betti_hodge_of_stage2g_family
    V H N (fun p => (hN p).some)

/-! ## Cosmology-strengthened pure-coordinate realization

The modern cosmology no longer needs an injective coordinate system on the
entire ambient cohomology group in order to reconstruct a Hodge class.  The
global pure-Hodge theorem identifies a pure world by its complete diagonal
coordinate vector of rank `min A B`.  Over Q we use the same canonical shape
as the rational scalar extension of that coordinate module.

A `CosmologyHodgeRealization` therefore asks only for:
* an exact linear chart from the derived rational Hodge subspace to one
  global pure-Hodge coordinate space;
* one native codimension-p algebraic cycle for each intrinsic diagonal basis
  coordinate;
* exact compatibility of those basis cycles with the chart.

From those data the cycle witness is reconstructed directly, so the older
ambient Stage-2G address certificate is unnecessary for the final implication.
-/

/-- Rational-coordinate analogue of `PureHodgeCoordinates A B`.
This definition does not itself identify a geometric Hodge sector with GST. -/
abbrev CosmologyPureCoordinates (A B : Nat) : Type :=
  Fin (min A B) → ℚ

/-- Intrinsic Kronecker basis of the rationalized global pure-Hodge coordinates. -/
def cosmologyCoordinateBasis
    {A B : Nat} (i : Fin (min A B)) :
    CosmologyPureCoordinates A B :=
  fun j => if j = i then 1 else 0

/-- Exact reconstruction from every intrinsic pure-Hodge coordinate. -/
theorem cosmology_coordinate_reconstruct
    {A B : Nat} (phi : CosmologyPureCoordinates A B) :
    phi = ∑ i : Fin (min A B),
      (phi i) • cosmologyCoordinateBasis i := by
  classical
  funext j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single j]
  · simp [cosmologyCoordinateBasis]
  · intro b hb hbj
    simp [cosmologyCoordinateBasis, hbj, Ne.symm hbj]
  · simp

/-- A direct cosmology chart of one native rational Hodge sector.
The chart must prove that its dimension matches the chosen GST diagonal
rank `min A B`. The geometric algebraicity requirement is explicit in
`basisCycle_class`; coordinate reconstruction alone does not supply it. -/
structure CosmologyHodgeRealization
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p A B : Nat) where
  chart :
    rationalHodgeSubspace (H.hodgeBigrading p) ≃ₗ[ℚ]
      CosmologyPureCoordinates A B
  basisCycle :
    Fin (min A B) → codimensionCycles V.X p
  basisCycle_class :
    ∀ i : Fin (min A B),
      H.cycleClass p (basisCycle i) =
        (chart.symm (cosmologyCoordinateBasis i)).1

/-- Construct the native algebraic cycle dictated by the complete cosmology
coordinate vector of one rational Hodge class. -/
noncomputable def cosmologyCycleWitness
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    {p A B : Nat}
    (R : CosmologyHodgeRealization V H p A B)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p)) :
    codimensionCycles V.X p :=
  ∑ i : Fin (min A B),
    (R.chart ⟨alpha, halpha⟩ i) • R.basisCycle i

/-- **COSMOLOGY CYCLE RECONSTRUCTION.**  The cycle built from the intrinsic
pure-Hodge coordinates has exactly the requested native Betti class. -/
theorem cosmologyCycleWitness_spec
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    {p A B : Nat}
    (R : CosmologyHodgeRealization V H p A B)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p)) :
    H.cycleClass p (cosmologyCycleWitness R alpha halpha) = alpha := by
  let a : rationalHodgeSubspace (H.hodgeBigrading p) := ⟨alpha, halpha⟩
  have hchart :
      a = ∑ i : Fin (min A B),
        (R.chart a i) • R.chart.symm (cosmologyCoordinateBasis i) := by
    apply R.chart.injective
    rw [map_sum]
    simp only [LinearEquiv.map_smul, LinearEquiv.apply_symm_apply]
    exact cosmology_coordinate_reconstruct (R.chart a)
  calc
    H.cycleClass p (cosmologyCycleWitness R alpha halpha) =
        ∑ i : Fin (min A B),
          (R.chart a i) • H.cycleClass p (R.basisCycle i) := by
            simp [cosmologyCycleWitness, a]
    _ = ∑ i : Fin (min A B),
          (R.chart a i) •
            (R.chart.symm (cosmologyCoordinateBasis i)).1 := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [R.basisCycle_class i]
    _ = alpha := by
          simpa [a] using (congrArg Subtype.val hchart).symm

/-- Cycle reconstruction respects the rational linear structure. Once the
geometric basis witnesses are supplied, this is a simultaneous linear lift
of the entire Hodge sector, not a separate choice for each input class. -/
noncomputable def cosmologyCycleLift
    {V : SmoothProjectiveComplexScheme} {H : HodgeBigradedBettiData V}
    {p A B : Nat} (R : CosmologyHodgeRealization V H p A B) :
    rationalHodgeSubspace (H.hodgeBigrading p) →ₗ[ℚ] codimensionCycles V.X p where
  toFun := fun a => cosmologyCycleWitness R a.1 a.2
  map_add' := by
    intro a b
    change (∑ i, (R.chart (a+b) i) • R.basisCycle i) =
      (∑ i, (R.chart a i) • R.basisCycle i) + (∑ i, (R.chart b i) • R.basisCycle i)
    simp only [map_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' := by
    intro q a
    change (∑ i, (R.chart (q • a) i) • R.basisCycle i) =
      q • (∑ i, (R.chart a i) • R.basisCycle i)
    simp only [map_smul, Pi.smul_apply, Finset.smul_sum, smul_smul, smul_eq_mul]

/-- The lift is a right inverse of the cycle-class map on the Hodge sector. -/
theorem cosmologyCycleLift_section
    {V : SmoothProjectiveComplexScheme} {H : HodgeBigradedBettiData V}
    {p A B : Nat} (R : CosmologyHodgeRealization V H p A B) :
    (H.cycleClass p).comp (cosmologyCycleLift R) =
      (rationalHodgeSubspace (H.hodgeBigrading p)).subtype := by
  ext a
  exact cosmologyCycleWitness_spec R a.1 a.2

/-- All algebraic witnesses of one Hodge class are its reconstructed cycle
plus a cycle in the kernel. Reconstruction does not imply uniqueness of the
algebraic cycle itself. -/
theorem cosmology_cycle_fiber_exact
    {V : SmoothProjectiveComplexScheme} {H : HodgeBigradedBettiData V}
    {p A B : Nat} (R : CosmologyHodgeRealization V H p A B)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p))
    (Z : codimensionCycles V.X p) :
    H.cycleClass p Z = alpha ↔
      ∃ K ∈ LinearMap.ker (H.cycleClass p), Z = cosmologyCycleWitness R alpha halpha + K := by
  constructor
  · intro hZ
    refine ⟨Z - cosmologyCycleWitness R alpha halpha, ?_, ?_⟩
    · change H.cycleClass p (Z - cosmologyCycleWitness R alpha halpha) = 0
      rw [map_sub, hZ, cosmologyCycleWitness_spec, sub_self]
    · calc
        Z = (Z - cosmologyCycleWitness R alpha halpha) +
            cosmologyCycleWitness R alpha halpha := (sub_add_cancel _ _).symm
        _ = cosmologyCycleWitness R alpha halpha +
            (Z - cosmologyCycleWitness R alpha halpha) := add_comm _ _
  · rintro ⟨K, hK, rfl⟩
    change H.cycleClass p K = 0 at hK
    rw [map_add, cosmologyCycleWitness_spec, hK, add_zero]

/-- Every native rational Hodge class represented by a cosmology chart has a
constructive codimension-p algebraic-cycle witness. -/
theorem hodge_class_has_cosmology_cycle
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    {p A B : Nat}
    (R : CosmologyHodgeRealization V H p A B)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p)) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha :=
  ⟨cosmologyCycleWitness R alpha halpha,
    cosmologyCycleWitness_spec R alpha halpha⟩

/-- **COSMOLOGY-STRENGTHENED HODGE LANDING.**  A pure-world realization in
all codimensions closes the native bigraded Betti Hodge statement directly,
without the older ambient finite-address realization structure. -/
theorem bigraded_betti_hodge_of_cosmology_family
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (A B : Nat → Nat)
    (R : ∀ p : Nat,
      CosmologyHodgeRealization V H p (A p) (B p)) :
    BigradedBettiHodgeStatement V H := by
  intro p alpha halpha
  exact hodge_class_has_cosmology_cycle V H (R p) alpha halpha

/-- The remaining realization target after importing the upgraded global
pure-Hodge coordinate theorem into the native Stage-2G front. -/
def CosmologyStage2GRealizationObligation
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) : Prop :=
  ∃ A B : Nat → Nat,
    ∀ p : Nat,
      Nonempty (CosmologyHodgeRealization V H p (A p) (B p))

/-- The cosmology-level obligation directly implies the native Hodge target. -/
theorem bigraded_betti_hodge_of_cosmology_obligation
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (hR : CosmologyStage2GRealizationObligation V H) :
    BigradedBettiHodgeStatement V H := by
  rcases hR with ⟨A, B, hAB⟩
  exact bigraded_betti_hodge_of_cosmology_family
    V H A B (fun p => (hAB p).some)

/-- Apply native transport/duality generation to the actual cycle image.

Only one nonzero algebraic class is required. The other cycle witnesses are
obtained by native transport, reflection, and rational superposition, provided
those operations have compatible linear actions on the geometric cycle space.
No list of algebraic basis representatives is an input to this theorem.

The compatibility equations are geometric obligations: the native GST laws
alone do not construct the cycle-space operators appearing here. -/
theorem hodge_sector_of_transport_duality
    (V : SmoothProjectiveComplexScheme) (H : HodgeBigradedBettiData V)
    (p : Nat) {I : Type} [Fintype I] (d : I → ℕ)
    (chart : rationalHodgeSubspace (H.hodgeBigrading p) ≃ₗ[ℚ]
      GSTMultiAxisCosmology.RationalCoef d)
    (hcycles : ∀ Z : codimensionCycles V.X p,
      H.cycleClass p Z ∈ rationalHodgeSubspace (H.hodgeBigrading p))
    (cycleShift : (I → ℕ) → Module.End ℚ (codimensionCycles V.X p))
    (cycleMirror : Module.End ℚ (codimensionCycles V.X p))
    (hshift : ∀ m Z,
      chart ⟨H.cycleClass p (cycleShift m Z), hcycles _⟩ =
        GSTMultiAxisCosmology.rationalShift d m
          (chart ⟨H.cycleClass p Z, hcycles Z⟩))
    (hmirror : ∀ Z,
      chart ⟨H.cycleClass p (cycleMirror Z), hcycles _⟩ =
        GSTMultiAxisCosmology.rationalMirror d
          (chart ⟨H.cycleClass p Z, hcycles Z⟩))
    (seed : codimensionCycles V.X p) (hseed : H.cycleClass p seed ≠ 0) :
    rationalHodgeSubspace (H.hodgeBigrading p) ≤ LinearMap.range (H.cycleClass p) := by
  let read : codimensionCycles V.X p →ₗ[ℚ] GSTMultiAxisCosmology.RationalCoef d :=
    chart.toLinearMap.comp ((H.cycleClass p).codRestrict
      (rationalHodgeSubspace (H.hodgeBigrading p)) hcycles)
  have hshiftRange : ∀ m f, f ∈ LinearMap.range read →
      GSTMultiAxisCosmology.rationalShift d m f ∈ LinearMap.range read := by
    rintro m f ⟨Z, rfl⟩
    exact ⟨cycleShift m Z, hshift m Z⟩
  have hmirrorRange : ∀ f, f ∈ LinearMap.range read →
      GSTMultiAxisCosmology.rationalMirror d f ∈ LinearMap.range read := by
    rintro f ⟨Z, rfl⟩
    exact ⟨cycleMirror Z, hmirror Z⟩
  have hseedRead : read seed ≠ 0 := by
    intro hz
    have he : chart ⟨H.cycleClass p seed, hcycles seed⟩ = chart 0 := by
      simpa only [map_zero] using hz
    exact hseed (congrArg Subtype.val (chart.injective he))
  have hfull := GSTMultiAxisCosmology.rational_transport_duality_generation d
    (LinearMap.range read) hshiftRange hmirrorRange (read seed) ⟨seed, rfl⟩ hseedRead
  intro alpha halpha
  have hm : chart ⟨alpha, halpha⟩ ∈ LinearMap.range read := by
    rw [hfull]
    trivial
  obtain ⟨Z, hZ⟩ := hm
  exact ⟨Z, congrArg Subtype.val (chart.injective hZ)⟩

/-- For a fixed pure-coordinate chart, constructing its cycle realization
is equivalent to algebraicity of the entire Hodge sector. The chart alone
does not establish this: the forward and reverse implications expose the
precise mathematical content of the basis-cycle field. -/
theorem cosmology_chart_realization_iff
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) (p A B : Nat)
    (chart : rationalHodgeSubspace (H.hodgeBigrading p) ≃ₗ[ℚ]
      CosmologyPureCoordinates A B) :
    (∃ R : CosmologyHodgeRealization V H p A B, R.chart = chart) ↔
      rationalHodgeSubspace (H.hodgeBigrading p) ≤ LinearMap.range (H.cycleClass p) := by
  classical
  constructor
  · rintro ⟨R, hchart⟩ alpha halpha
    exact hodge_class_has_cosmology_cycle V H R alpha halpha
  · intro h
    have hb : ∀ i : Fin (min A B), ∃ Z : codimensionCycles V.X p,
        H.cycleClass p Z = (chart.symm (cosmologyCoordinateBasis i)).1 := by
      intro i
      exact h (chart.symm (cosmologyCoordinateBasis i)).2
    choose Z hZ using hb
    exact ⟨{ chart := chart, basisCycle := Z, basisCycle_class := hZ }, rfl⟩

/-- A zero cycle-class map realizes exactly the zero Hodge sector. This
checks that no unconditional algebraicity conclusion follows just from a
semantic package with an arbitrary linear cycle-class field. -/
theorem zero_cycleClass_hodge_iff
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) (p : Nat)
    (hzero : H.cycleClass p = 0) :
    rationalHodgeSubspace (H.hodgeBigrading p) ≤ LinearMap.range (H.cycleClass p) ↔
      rationalHodgeSubspace (H.hodgeBigrading p) = ⊥ := by
  simp [hzero]

#check Complexification
#check complexificationMapQ
#check complexificationMapQ_apply
#check HodgeBigrading
#check ppIndex
#check HodgeBigrading.ppComponent
#check rationalHodgeSubspace
#check mem_rationalHodgeSubspace_iff
#check HodgeBigradedBettiData
#check HodgeBigradedBettiData.toBettiHodgeData
#check BigradedBettiHodgeStatement
#check bigradedBettiHodgeStatement_iff_stage2f
#check Stage2GClassRealization
#check hodge_class_has_bigraded_cycle
#check bigraded_betti_hodge_of_stage2g_family
#check Stage2GRealizationObligation
#check bigraded_betti_hodge_of_stage2g_obligation
#check CosmologyPureCoordinates
#check cosmologyCoordinateBasis
#check cosmology_coordinate_reconstruct
#check CosmologyHodgeRealization
#check cosmologyCycleWitness
#check cosmologyCycleWitness_spec
#check hodge_class_has_cosmology_cycle
#check bigraded_betti_hodge_of_cosmology_family
#check CosmologyStage2GRealizationObligation
#check bigraded_betti_hodge_of_cosmology_obligation

#print axioms mem_rationalHodgeSubspace_iff
#print axioms bigradedBettiHodgeStatement_iff_stage2f
#print axioms hodge_class_has_bigraded_cycle
#print axioms bigraded_betti_hodge_of_stage2g_family
#print axioms bigraded_betti_hodge_of_stage2g_obligation
#print axioms cosmology_coordinate_reconstruct
#print axioms cosmologyCycleWitness_spec
#print axioms bigraded_betti_hodge_of_cosmology_family
#print axioms bigraded_betti_hodge_of_cosmology_obligation

end GSTGeometricRealizationStage2G
