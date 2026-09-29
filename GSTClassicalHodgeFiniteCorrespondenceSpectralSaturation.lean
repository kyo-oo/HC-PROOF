import GSTClassicalHodgeFiniteCorrespondenceOperatorAlgebra
import GSTClassicalHodgeCyclicSpectralGeneration

/-!
# GST CLASSICAL HODGE — FINITE CORRESPONDENCE SPECTRAL SATURATION

The generic cyclic spectral theorem previously required `atomic_stable` as a
separate field of the observable.  For an observable coming from a genuine
finite closed correspondence that requirement is no longer independent: point
naturality plus compact point normal form already prove exact cycle-class
naturality, and therefore preservation of the complete atomic cycle-class
span.

This file packages that splice.

A `FiniteCorrespondenceSpectralFamily` consists of one actual finite closed
correspondence with point-generator Betti naturality plus an independently
computed simple rational spectrum on a selected finite family of genuine Hodge
basis directions.  No basis direction is assumed algebraic.

The correspondence atom automatically becomes a
`ClassicalHodgeSpectralOperator`.  Hence one algebraic cyclic seed with nonzero
coordinates in the selected eigendirections lets the existing Lagrange
functional calculus isolate every selected Hodge sheet by polynomials in an
actual correspondence operator.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry

namespace GSTClassicalHodgeFiniteCorrespondenceSpectralSaturation

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeCyclicSpectralGeneration
open GSTClassicalHodgeFiniteCorrespondenceOperatorAlgebra

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A simple rational Hodge spectrum carried by one genuine finite closed
correspondence atom. -/
structure FiniteCorrespondenceSpectralFamily
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (ι : Type*) [Fintype ι] [DecidableEq ι] where
  atom : FiniteCorrespondenceAtom V H p
  basisIndex : ι → ClassicalHodgeBasisIndex V H p
  basisIndex_injective : Function.Injective basisIndex
  eigenvalue : ι → ℚ
  eigenvalue_injective : Function.Injective eigenvalue
  eigenvector : ∀ i,
    atom.cohomologyOperator
        (classicalHodgeBasis V H p (basisIndex i)).1 =
      eigenvalue i • (classicalHodgeBasis V H p (basisIndex i)).1

namespace FiniteCorrespondenceSpectralFamily

/-- The genuine correspondence atom preserves the complete atomic span by its
cycle-class naturality; no extra algebraicity-stability assumption is needed. -/
theorem atomic_stable
    (S : FiniteCorrespondenceSpectralFamily V H p ι) :
    ∀ x : RationalSingularCohomology H.analytification (2 * p),
      x ∈ pointCycleClassSpan p (H.cycleClass p) →
        S.atom.cohomologyOperator x ∈
          pointCycleClassSpan p (H.cycleClass p) := by
  intro x hx
  let w : FiniteCorrespondenceWord V H p :=
    FiniteCorrespondenceWord.atom S.atom
  exact w.maps_atomicSpan hx

/-- Forget only the geometric carrier and expose the already-proved generic
spectral interface.  Atomic stability is derived, not supplied. -/
noncomputable def toClassicalHodgeSpectralOperator
    (S : FiniteCorrespondenceSpectralFamily V H p ι) :
    ClassicalHodgeSpectralOperator V H p ι where
  basisIndex := S.basisIndex
  basisIndex_injective := S.basisIndex_injective
  observable := S.atom.cohomologyOperator
  eigenvalue := S.eigenvalue
  eigenvalue_injective := S.eigenvalue_injective
  eigenvector := S.eigenvector
  atomic_stable := S.atomic_stable

/-- **GENUINE-CORRESPONDENCE SPECTRAL EXTRACTION.**
One algebraic cyclic seed lets polynomial words in the actual correspondence
isolate every selected Hodge basis direction. -/
theorem selected_basis_algebraic_of_cyclic_seed
    (S : FiniteCorrespondenceSpectralFamily V H p ι)
    (a : ι → ℚ)
    (ha : ∀ i, a i ≠ 0)
    (hseed :
      ∑ i : ι,
        a i • (classicalHodgeBasis V H p (S.basisIndex i)).1 ∈
          pointCycleClassSpan p (H.cycleClass p)) :
    ∀ i : ι,
      (classicalHodgeBasis V H p (S.basisIndex i)).1 ∈
        pointCycleClassSpan p (H.cycleClass p) := by
  exact S.toClassicalHodgeSpectralOperator
    |>.selected_basis_algebraic_of_cyclic_seed a ha hseed

/-- If the selected spectrum exhausts the Hodge basis, the same single genuine
correspondence and one cyclic algebraic seed prove the whole fixed-weight Hodge
inclusion. -/
theorem weight_hodge_of_cyclic_seed
    (S : FiniteCorrespondenceSpectralFamily V H p ι)
    (hsurj : Function.Surjective S.basisIndex)
    (a : ι → ℚ)
    (ha : ∀ i, a i ≠ 0)
    (hseed :
      ∑ i : ι,
        a i • (classicalHodgeBasis V H p (S.basisIndex i)).1 ∈
          pointCycleClassSpan p (H.cycleClass p)) :
    rationalHodgeSubspace (H.hodgeBigrading p) ≤
      pointCycleClassSpan p (H.cycleClass p) := by
  exact S.toClassicalHodgeSpectralOperator
    |>.weight_hodge_of_cyclic_spectral_generation hsurj a ha hseed

/-- All-weight genuine finite-correspondence spectral data reduce the Stage-2G
Hodge target to constructing one simple-spectrum correspondence and one cyclic
algebraic seed in each nontrivial Hodge weight. -/
theorem bigradedBettiHodge_of_finiteCorrespondenceSpectralFamilies
    (rank : Nat → Nat)
    (S : ∀ q : Nat,
      FiniteCorrespondenceSpectralFamily V H q (Fin (rank q)))
    (hsurj : ∀ q, Function.Surjective (S q).basisIndex)
    (a : ∀ q, Fin (rank q) → ℚ)
    (ha : ∀ q i, a q i ≠ 0)
    (hseed : ∀ q,
      ∑ i : Fin (rank q),
        a q i •
          (classicalHodgeBasis V H q ((S q).basisIndex i)).1 ∈
            pointCycleClassSpan q (H.cycleClass q)) :
    BigradedBettiHodgeStatement V H := by
  exact (bigradedBettiHodgeStatement_iff_atomic_span V H).2
    (fun q => (S q).weight_hodge_of_cyclic_seed
      (hsurj q) (a q) (ha q) (hseed q))

#check FiniteCorrespondenceSpectralFamily
#check FiniteCorrespondenceSpectralFamily.atomic_stable
#check FiniteCorrespondenceSpectralFamily.toClassicalHodgeSpectralOperator
#check FiniteCorrespondenceSpectralFamily.selected_basis_algebraic_of_cyclic_seed
#check FiniteCorrespondenceSpectralFamily.weight_hodge_of_cyclic_seed
#check bigradedBettiHodge_of_finiteCorrespondenceSpectralFamilies

#print axioms FiniteCorrespondenceSpectralFamily.atomic_stable
#print axioms FiniteCorrespondenceSpectralFamily.selected_basis_algebraic_of_cyclic_seed
#print axioms FiniteCorrespondenceSpectralFamily.weight_hodge_of_cyclic_seed
#print axioms bigradedBettiHodge_of_finiteCorrespondenceSpectralFamilies

end FiniteCorrespondenceSpectralFamily

end GSTClassicalHodgeFiniteCorrespondenceSpectralSaturation
