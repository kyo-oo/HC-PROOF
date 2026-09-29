import GSTClassicalHodgePrincipalCutFlagNativeReturn
import GSTClassicalHodgePrincipalCutFlagAdjointCosmology
import GSTClassicalHodgePointNormalForm

/-!
# GST CLASSICAL HODGE — PRINCIPAL-CUT FLAG HOMOLOGICAL DESCENT

The native reverse principal-cut flag has already been constructed directly
from incidence geometry.  Its remaining classical-semantic problem is not the
existence of the operator: it is whether that operator depends only on the
Betti cycle class of its input.

This file isolates a genuinely geometric sufficient law for that descent.
For one finite source chart, assume that the native incidence pairing between
one principal-cut row and an arbitrary finite target presentation agrees with
an honest bilinear pairing of their Betti cycle classes.  This is the local
projection/intersection formula expected from the classical geometry; it does
not mention Hodge surjectivity, a ghost sheet, target-basis algebraicity, a
matrix unit, or projective visibility.

Under this one law we prove:

* every finite target presentation whose realized cycle has zero Betti class is
  annihilated by the reverse incidence transpose;
* every homologically trivial native target cycle is annihilated by the native
  reverse flag;
* consequently the reverse flag takes equal values on cycles with equal Betti
  classes, i.e. it genuinely factors through homological equivalence.

This is the exact semantic bridge identified as missing by the preceding flag
adjoint/native-return files.  The next geometric task is therefore sharply
localized: construct the pairing and prove the incidence projection formula
from the actual smooth-projective intersection/Poincare geometry.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgePrincipalCutFlagHomologicalDescent

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTCompactNativeCyclePresentation
open GSTClassicalHodgePointNormalForm
open GSTClassicalHodgePrincipalCutSuccessorOperator
open GSTClassicalHodgePrincipalCutIncidenceTransposeCosmology
open GSTClassicalHodgePrincipalCutFlagAdjointCosmology
open GSTClassicalHodgePrincipalCutFlagNativeReturn

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- The ambient rational cohomology group in the target weight of one
principal-cut step. -/
abbrev TargetCohomology
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) :=
  RationalSingularCohomology H.analytification (2 * (p + 1))

/-- **LOCAL INCIDENCE / COHOMOLOGY PROJECTION FORMULA.**

For every source point retained in `sigma`, incidence pairing with its genuine
principal-cut row is computed by a bilinear pairing of the corresponding
actual Betti cycle classes.  The target argument is stated for arbitrary finite
point presentations, so the law is independent of compactness and of any
choice of presentation for a native cycle. -/
structure PrincipalCutFlagProjectionFormula
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (sigma : Finset (CodimensionPoint V.X p)) where
  cohomologyPair :
    TargetCohomology V H p →ₗ[ℚ]
      TargetCohomology V H p →ₗ[ℚ] ℚ
  incidence_eq :
    ∀ x : CodimensionPoint V.X p,
      x ∈ sigma →
      ∀ psi : FiniteCodimensionPresentation V.X (p + 1),
        presentationPair (successorPresentation V p x) psi =
          cohomologyPair
            (H.cycleClass (p + 1) (successorPresentationCycle V p x))
            (H.cycleClass (p + 1)
              (realizeFiniteCodimensionPresentation V.X (p + 1) psi))

namespace PrincipalCutFlagProjectionFormula

/-- If the native cycle realized by a finite target presentation is
homologically trivial, the complete local reverse-incidence presentation is
zero.  The proof is coefficientwise: inside the source chart, adjointness
turns each transpose coefficient into the forward incidence pairing and the
projection formula kills it; outside the chart the transpose column is zero by
construction. -/
theorem localSuccessorTranspose_eq_zero_of_realized_cycleClass_eq_zero
    {sigma : Finset (CodimensionPoint V.X p)}
    (P : PrincipalCutFlagProjectionFormula V H p sigma)
    (psi : FiniteCodimensionPresentation V.X (p + 1))
    (hpsi :
      H.cycleClass (p + 1)
        (realizeFiniteCodimensionPresentation V.X (p + 1) psi) = 0) :
    localSuccessorTranspose V p sigma psi = 0 := by
  classical
  apply Finsupp.ext
  intro x
  by_cases hx : x ∈ sigma
  · calc
      localSuccessorTranspose V p sigma psi x =
          presentationPair (Finsupp.single x (1 : ℚ))
            (localSuccessorTranspose V p sigma psi) := by
              simp [presentationPair]
      _ = presentationPair (successorPresentation V p x) psi := by
            exact (successor_localTranspose_adjoint_single
              V p sigma x hx psi).symm
      _ = P.cohomologyPair
            (H.cycleClass (p + 1) (successorPresentationCycle V p x))
            (H.cycleClass (p + 1)
              (realizeFiniteCodimensionPresentation V.X (p + 1) psi)) :=
            P.incidence_eq x hx psi
      _ = 0 := by simp [hpsi]
      _ = (0 : FiniteCodimensionPresentation V.X p) x := by simp
  · change
      (psi.sum fun y q => q • localTransposeColumn V p sigma y) x = 0
    classical
    simp [localTransposeColumn_apply_of_not_mem V p sigma x, hx]

/-- **HOMOLOGICALLY TRIVIAL CYCLES ARE KILLED BY THE REVERSE FLAG.**

This is the key descent theorem.  Compactness supplies the exact finite point
normal form of an arbitrary native target cycle; the preceding presentation
result then kills its reverse incidence image. -/
theorem localTransposeNativeOperator_eq_zero_of_cycleClass_eq_zero
    {sigma : Finset (CodimensionPoint V.X p)}
    (P : PrincipalCutFlagProjectionFormula V H p sigma)
    (Z : codimensionCycles V.X (p + 1))
    (hZ : H.cycleClass (p + 1) Z = 0) :
    localTransposeNativeOperator V p sigma Z = 0 := by
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  let psi : FiniteCodimensionPresentation V.X (p + 1) :=
    presentationOfNativeCycle V.X (p + 1) Z
  have hreal :
      realizeFiniteCodimensionPresentation V.X (p + 1) psi = Z := by
    simpa [psi] using realize_presentationOfNativeCycle V.X (p + 1) Z
  have hpsiClass :
      H.cycleClass (p + 1)
        (realizeFiniteCodimensionPresentation V.X (p + 1) psi) = 0 := by
    rw [hreal]
    exact hZ
  have htranspose : localSuccessorTranspose V p sigma psi = 0 :=
    P.localSuccessorTranspose_eq_zero_of_realized_cycleClass_eq_zero
      psi hpsiClass
  calc
    localTransposeNativeOperator V p sigma Z =
        localTransposeNativeOperator V p sigma
          (realizeFiniteCodimensionPresentation V.X (p + 1) psi) := by
            rw [hreal]
    _ = realizeFiniteCodimensionPresentation V.X p
          (localSuccessorTranspose V p sigma psi) := by
            exact localTransposeNativeOperator_realize V p sigma psi
    _ = 0 := by rw [htranspose]; simp

/-- Kernel formulation of homological descent: the kernel of the genuine
cycle-class map is contained in the kernel of the native reverse flag. -/
theorem cycleClass_kernel_le_reverseFlag_kernel
    {sigma : Finset (CodimensionPoint V.X p)}
    (P : PrincipalCutFlagProjectionFormula V H p sigma) :
    LinearMap.ker (H.cycleClass (p + 1)) ≤
      LinearMap.ker (localTransposeNativeOperator V p sigma) := by
  intro Z hZ
  rw [LinearMap.mem_ker] at hZ ⊢
  exact P.localTransposeNativeOperator_eq_zero_of_cycleClass_eq_zero Z hZ

/-- Equal Betti cycle classes have exactly equal reverse-flag images.  Thus the
native reverse flag genuinely depends only on the homology class of its target
cycle once the local projection formula is available. -/
theorem localTransposeNativeOperator_eq_of_cycleClass_eq
    {sigma : Finset (CodimensionPoint V.X p)}
    (P : PrincipalCutFlagProjectionFormula V H p sigma)
    (Z W : codimensionCycles V.X (p + 1))
    (hZW : H.cycleClass (p + 1) Z = H.cycleClass (p + 1) W) :
    localTransposeNativeOperator V p sigma Z =
      localTransposeNativeOperator V p sigma W := by
  have hsub : H.cycleClass (p + 1) (Z - W) = 0 := by
    rw [map_sub, hZW, sub_self]
  have hzero :=
    P.localTransposeNativeOperator_eq_zero_of_cycleClass_eq_zero
      (Z - W) hsub
  simpa only [map_sub, sub_eq_zero] using hzero

/-- Crown: the projection/intersection formula simultaneously gives kernel
annihilation and presentation-independence of the reverse principal-cut flag. -/
theorem homological_descent_crown
    {sigma : Finset (CodimensionPoint V.X p)}
    (P : PrincipalCutFlagProjectionFormula V H p sigma) :
    (LinearMap.ker (H.cycleClass (p + 1)) ≤
      LinearMap.ker (localTransposeNativeOperator V p sigma))
      ∧
    (∀ Z W : codimensionCycles V.X (p + 1),
      H.cycleClass (p + 1) Z = H.cycleClass (p + 1) W →
        localTransposeNativeOperator V p sigma Z =
          localTransposeNativeOperator V p sigma W) := by
  exact ⟨P.cycleClass_kernel_le_reverseFlag_kernel,
    P.localTransposeNativeOperator_eq_of_cycleClass_eq⟩

end PrincipalCutFlagProjectionFormula

#check PrincipalCutFlagProjectionFormula
#check PrincipalCutFlagProjectionFormula.localSuccessorTranspose_eq_zero_of_realized_cycleClass_eq_zero
#check PrincipalCutFlagProjectionFormula.localTransposeNativeOperator_eq_zero_of_cycleClass_eq_zero
#check PrincipalCutFlagProjectionFormula.cycleClass_kernel_le_reverseFlag_kernel
#check PrincipalCutFlagProjectionFormula.localTransposeNativeOperator_eq_of_cycleClass_eq
#check PrincipalCutFlagProjectionFormula.homological_descent_crown

#print axioms PrincipalCutFlagProjectionFormula.localSuccessorTranspose_eq_zero_of_realized_cycleClass_eq_zero
#print axioms PrincipalCutFlagProjectionFormula.localTransposeNativeOperator_eq_zero_of_cycleClass_eq_zero
#print axioms PrincipalCutFlagProjectionFormula.cycleClass_kernel_le_reverseFlag_kernel
#print axioms PrincipalCutFlagProjectionFormula.localTransposeNativeOperator_eq_of_cycleClass_eq
#print axioms PrincipalCutFlagProjectionFormula.homological_descent_crown

end GSTClassicalHodgePrincipalCutFlagHomologicalDescent
