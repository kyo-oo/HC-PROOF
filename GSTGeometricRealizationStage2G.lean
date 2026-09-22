import Mathlib
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Algebra.Module.Submodule.RestrictScalars
import Mathlib.Order.SupIndep
import GSTGeometricRealizationStage2F

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

#print axioms mem_rationalHodgeSubspace_iff
#print axioms bigradedBettiHodgeStatement_iff_stage2f
#print axioms hodge_class_has_bigraded_cycle
#print axioms bigraded_betti_hodge_of_stage2g_family
#print axioms bigraded_betti_hodge_of_stage2g_obligation

end GSTGeometricRealizationStage2G
