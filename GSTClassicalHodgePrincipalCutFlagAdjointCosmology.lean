import GSTClassicalHodgePrincipalCutIncidenceTransposeCosmology
import GSTClassicalHodgeGeometricCycleClassSpine

/-!
# GST CLASSICAL HODGE — PRINCIPAL-CUT FLAG ADJOINT COSMOLOGY

The principal-cut successor is not merely a one-way list of points.  On every
finite source chart it is an incidence operator, and the preceding module
constructed its finite transpose.  This file supplies the exact adjoint
calculus and splices the forward incidence back into the genuine geometric
cycle-class spine.

The key point is categorical.  A codimension-lowering return should not be
searched for among arbitrary same-dimensional finite self-correspondences.
The native object is the *flag relation* between a source codimension-p generic
point and its codimension-(p+1) principal-cut successors.  On a finite chart,
the reverse flag is precisely the transpose incidence kernel.

Everything below is unconditional and occurs before any Hodge-surjectivity
claim:

* the coefficient pairing on finite native presentations;
* exact forward/transpose adjointness on a local flag chart;
* the normal quadratic identity <phi,K^t K phi> = <K phi,K phi>;
* exact identification of the forward flag with the already genuine
  cycle-class-natural principal-cut cohomology operator.

Thus the remaining external question is no longer an invented matrix unit.  It
is whether the geometrically defined reverse flag descends through homological
equivalence on the one first-failure chart.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open scoped BigOperators

namespace GSTClassicalHodgePrincipalCutFlagAdjointCosmology

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgePointNormalForm
open GSTClassicalHodgePrincipalCutSuccessorOperator
open GSTClassicalHodgePrincipalCutIncidenceTransposeCosmology
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeCrossWeightNativePropagation

/-- Coefficient pairing on two finite native point presentations of the same
codimension.  It is the finite-support dot product in the genuine point normal
form. -/
noncomputable def presentationPair
    {X : Scheme} {p : Nat}
    (phi psi : FiniteCodimensionPresentation X p) : ℚ :=
  phi.sum fun x q => q * psi x

@[simp]
theorem presentationPair_zero_left
    {X : Scheme} {p : Nat}
    (psi : FiniteCodimensionPresentation X p) :
    presentationPair (0 : FiniteCodimensionPresentation X p) psi = 0 := by
  simp [presentationPair]

@[simp]
theorem presentationPair_single_left
    {X : Scheme} {p : Nat}
    (x : CodimensionPoint X p) (q : ℚ)
    (psi : FiniteCodimensionPresentation X p) :
    presentationPair (Finsupp.single x q) psi = q * psi x := by
  classical
  simp [presentationPair]

/-- The finite-support coefficient pairing is symmetric. -/
theorem presentationPair_comm
    {X : Scheme} {p : Nat}
    (phi psi : FiniteCodimensionPresentation X p) :
    presentationPair phi psi = presentationPair psi phi := by
  classical
  unfold presentationPair
  induction phi using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
      simp [hf, hg, Finsupp.sum_add_index]
  | single x q =>
      induction psi using Finsupp.induction_linear with
      | zero => simp
      | add f g hf hg => simp [hf, hg, add_mul]
      | single y r =>
          by_cases hxy : x = y
          · subst y; simp [mul_comm]
          · simp [hxy, Ne.symm hxy]

/-- Adjointness on one source atom: forward principal-cut incidence paired
against an arbitrary target presentation equals the source atom paired against
the reverse flag incidence. -/
theorem successor_localTranspose_adjoint_single
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (sigma : Finset (CodimensionPoint V.X p))
    (x : CodimensionPoint V.X p)
    (hx : x ∈ sigma)
    (psi : FiniteCodimensionPresentation V.X (p + 1)) :
    presentationPair (successorPresentation V p x) psi =
      presentationPair (Finsupp.single x (1 : ℚ))
        (localSuccessorTranspose V p sigma psi) := by
  classical
  rw [presentationPair_single_left]
  rw [localSuccessorTranspose_apply_of_mem V p sigma psi x hx]
  unfold presentationPair
  apply Finsupp.sum_congr
  intro y q hy
  ring

/-- Exact self-energy identity for one flag source. -/
theorem successor_selfEnergy_eq_pair
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p) :
    successorSelfEnergy V p x =
      presentationPair (successorPresentation V p x)
        (successorPresentation V p x) := by
  rfl

/-- The normal return coefficient is literally the squared coefficient norm of
the forward principal-cut incidence vector. -/
theorem normal_self_pair_eq_forward_square
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (sigma : Finset (CodimensionPoint V.X p))
    (x : CodimensionPoint V.X p)
    (hx : x ∈ sigma) :
    presentationPair (Finsupp.single x (1 : ℚ))
        (localSuccessorNormal V p sigma
          (Finsupp.single x (1 : ℚ))) =
      presentationPair (successorPresentation V p x)
        (successorPresentation V p x) := by
  rw [presentationPair_single_left]
  rw [localSuccessorNormal_single_self V p sigma x hx]
  exact successor_selfEnergy_eq_pair V p x

/-- Realize one principal-cut presentation as its actual codimension-(p+1)
native cycle. -/
noncomputable def successorPresentationCycle
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p) :
    codimensionCycles V.X (p + 1) :=
  realizeFiniteCodimensionPresentation V.X (p + 1)
    (successorPresentation V p x)

/-- The presentation-level forward flag is exactly the native geometric
principal-cut successor on a point atom. -/
theorem successorPresentationCycle_eq_native
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p) :
    successorPresentationCycle V p x =
      successorNativeOperator V p (codimensionPointCycle V.X p x) := by
  exact (successorNativeOperator_point V p x).symm

/-- **FORWARD FLAG / COHOMOLOGY SPLICE.**
The finite incidence row used by the transpose cosmology has cycle class
exactly equal to the genuine principal-cut cohomology operator from the
geometric spine.  Hence the new flag kernel is not an auxiliary combinatorial
model: its forward face is the already-certified classical geometric
transport. -/
theorem cycleClass_successorPresentationCycle
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (x : CodimensionPoint V.X p) :
    H.cycleClass (p + 1) (successorPresentationCycle V p x) =
      (G.principalCutPair p).cohomologyOperator
        (H.cycleClass p (codimensionPointCycle V.X p x)) := by
  rw [successorPresentationCycle_eq_native]
  rw [← G.principalCutPair_native p]
  exact (G.principalCutPair p).cycleClass_natural
    (codimensionPointCycle V.X p x)

/-- Therefore any live exact principal cut gives a genuine nonzero incidence
energy whose forward native cycle already sits in the certified
cycle-class-natural principal-cut square. -/
theorem forwardFlag_live_crown
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (sigma : Finset (CodimensionPoint V.X p))
    (x : CodimensionPoint V.X p)
    (hx : x ∈ sigma)
    (hExact : GSTClassicalHodgeRelativeSuccessorExactStratum.RelativeSuccessorAmbientExact V p x)
    (hNonempty : (relativeCodimensionOneFinset V x.1).Nonempty) :
    successorSelfEnergy V p x ≠ 0
      ∧ H.cycleClass (p + 1) (successorPresentationCycle V p x) =
          (G.principalCutPair p).cohomologyOperator
            (H.cycleClass p (codimensionPointCycle V.X p x))
      ∧ presentationPair (Finsupp.single x (1 : ℚ))
          (localSuccessorNormal V p sigma
            (Finsupp.single x (1 : ℚ))) =
        successorSelfEnergy V p x := by
  refine ⟨
    successorSelfEnergy_ne_zero_of_exact_nonempty
      V p x hExact hNonempty,
    cycleClass_successorPresentationCycle G p x,
    ?_⟩
  rw [normal_self_pair_eq_forward_square V p sigma x hx]
  exact (successor_selfEnergy_eq_pair V p x).symm

#check presentationPair
#check successor_localTranspose_adjoint_single
#check normal_self_pair_eq_forward_square
#check successorPresentationCycle
#check cycleClass_successorPresentationCycle
#check forwardFlag_live_crown

#print axioms successor_localTranspose_adjoint_single
#print axioms normal_self_pair_eq_forward_square
#print axioms cycleClass_successorPresentationCycle
#print axioms forwardFlag_live_crown

end GSTClassicalHodgePrincipalCutFlagAdjointCosmology
