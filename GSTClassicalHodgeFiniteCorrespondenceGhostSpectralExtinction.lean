import GSTClassicalHodgeFiniteCorrespondenceSpectralSaturation
import GSTClassicalHodgeOmniversalSeparatorGhostCrown

/-!
# GST CLASSICAL HODGE — FINITE CORRESPONDENCE GHOST SPECTRAL EXTINCTION

Full cyclic spectral generation is stronger than a separator contradiction
needs.  To kill one omniversal ghost, only one selected eigendirection matters.

Let a genuine finite closed correspondence have a finite simple rational
spectrum on selected Hodge basis directions, including the ghost sheet.  If an
actual algebraic cycle class is a linear combination of those eigenvectors and
its coefficient in the ghost eigendirection is nonzero, the Lagrange isolator
polynomial extracts a nonzero scalar multiple of the ghost basis vector.

Because the observable is an actual finite correspondence, the isolator
polynomial preserves the complete atomic cycle-class span.  The ghost separator
must therefore annihilate the isolated vector.  But it detects the ghost basis
vector, and the Lagrange normalization and selected coefficient are both
nonzero: contradiction.

Thus one-coordinate spectral visibility is enough; no all-sheet cyclic seed,
no matrix-unit realization and no projective-orbit irreducibility is needed.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry

namespace GSTClassicalHodgeFiniteCorrespondenceGhostSpectralExtinction

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeAtomicAnnihilator
open GSTClassicalHodgeCyclicSpectralGeneration
open GSTClassicalHodgeFiniteCorrespondenceOperatorAlgebra
open GSTClassicalHodgeFiniteCorrespondenceSpectralSaturation
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeOmniversalSeparatorGhostCrown

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {G : GeometricCycleClassSpine V H}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A selected finite spectral combination of one genuine correspondence. -/
def spectralSeed
    {p : Nat}
    (S : FiniteCorrespondenceSpectralFamily V H p ι)
    (a : ι → ℚ) :
    RationalSingularCohomology H.analytification (2 * p) :=
  ∑ i : ι,
    a i • (classicalHodgeBasis V H p (S.basisIndex i)).1

/-- Polynomial isolation of a single selected coordinate remains inside the
atomic cycle-class span because the underlying observable is a genuine finite
correspondence. -/
theorem isolated_seed_mem_atomic
    {p : Nat}
    (S : FiniteCorrespondenceSpectralFamily V H p ι)
    (a : ι → ℚ)
    (hseed : spectralSeed S a ∈
      pointCycleClassSpan p (H.cycleClass p))
    (i : ι) :
    linearPolyEval S.atom.cohomologyOperator
        (S.toClassicalHodgeSpectralOperator.toFiniteSpectralFamily.isolatorPolynomial i)
        (spectralSeed S a) ∈
      pointCycleClassSpan p (H.cycleClass p) := by
  exact polynomialStable_of_operatorStable
    (pointCycleClassSpan p (H.cycleClass p))
    S.atom.cohomologyOperator
    S.atomic_stable
    (S.toClassicalHodgeSpectralOperator.toFiniteSpectralFamily.isolatorPolynomial i)
    (spectralSeed S a) hseed

/-- Exact one-coordinate extraction formula for a genuine correspondence
spectral family. -/
theorem isolated_seed_eq
    {p : Nat}
    (S : FiniteCorrespondenceSpectralFamily V H p ι)
    (a : ι → ℚ)
    (i : ι) :
    linearPolyEval S.atom.cohomologyOperator
        (S.toClassicalHodgeSpectralOperator.toFiniteSpectralFamily.isolatorPolynomial i)
        (spectralSeed S a) =
      (a i *
        S.toClassicalHodgeSpectralOperator.toFiniteSpectralFamily.isolatorScale i) •
        (classicalHodgeBasis V H p (S.basisIndex i)).1 := by
  exact S.toClassicalHodgeSpectralOperator.toFiniteSpectralFamily
    |>.isolator_on_combination a i

/-- **ONE-SHEET GENUINE-CORRESPONDENCE EXTINCTION.**
An algebraic spectral seed cannot carry a nonzero coefficient in a selected
sheet detected by an omniversal ghost. -/
theorem ghost_selected_coefficient_eq_zero
    (E : OmniversalSeparatorGhost G)
    (S : FiniteCorrespondenceSpectralFamily V H E.weight ι)
    (a : ι → ℚ)
    (hseed : spectralSeed S a ∈
      pointCycleClassSpan E.weight (H.cycleClass E.weight))
    (i : ι)
    (hi : S.basisIndex i = E.sheet) :
    a i = 0 := by
  by_contra hai
  have hmem := isolated_seed_mem_atomic S a hseed i
  have hker :
      pointCycleClassSpan E.weight (H.cycleClass E.weight) ≤
        LinearMap.ker E.separator.detector :=
    (annihilatesPointCycles_iff_atomicSpan_le_ker
      E.weight (H.cycleClass E.weight) E.separator.detector).mp
      E.separator.annihilates_atoms
  have hzero := hker hmem
  rw [isolated_seed_eq S a i, hi, LinearMap.map_smul] at hzero
  have hscale :
      a i *
        S.toClassicalHodgeSpectralOperator.toFiniteSpectralFamily.isolatorScale i ≠ 0 :=
    mul_ne_zero hai
      (S.toClassicalHodgeSpectralOperator.toFiniteSpectralFamily.isolatorScale_ne_zero i)
  have hdetect :
      E.separator.detector
        (classicalHodgeBasis V H E.weight E.sheet).1 ≠ 0 :=
    E.separator.detects_basis
  exact hscale (mul_eq_zero.mp hzero |>.resolve_right hdetect)

/-- Contradiction form: no algebraic selected spectral seed can have a nonzero
ghost coordinate. -/
theorem no_algebraic_seed_with_nonzero_ghost_coordinate
    (E : OmniversalSeparatorGhost G)
    (S : FiniteCorrespondenceSpectralFamily V H E.weight ι)
    (a : ι → ℚ)
    (hseed : spectralSeed S a ∈
      pointCycleClassSpan E.weight (H.cycleClass E.weight))
    (i : ι)
    (hi : S.basisIndex i = E.sheet) :
    ¬ a i ≠ 0 := by
  intro hai
  exact hai (ghost_selected_coefficient_eq_zero E S a hseed i hi)

/-- If geometry supplies, for every possible ghost, one genuine finite
correspondence spectral chart and one algebraic seed whose selected ghost
coefficient is nonzero, the Hodge target follows.  This is the one-coordinate
version of the spectral closure criterion. -/
theorem bigradedBettiHodge_of_oneSheetCorrespondenceSpectralHits
    (R : ∀ E : OmniversalSeparatorGhost G,
      ∃ (rank : Nat)
        (S : FiniteCorrespondenceSpectralFamily V H E.weight (Fin rank))
        (a : Fin rank → ℚ)
        (i : Fin rank),
          spectralSeed S a ∈
            pointCycleClassSpan E.weight (H.cycleClass E.weight)
          ∧ S.basisIndex i = E.sheet
          ∧ a i ≠ 0) :
    BigradedBettiHodgeStatement V H := by
  by_contra hnot
  rcases (not_hodge_iff_nonempty_omniversalSeparatorGhost G).mp hnot with ⟨E⟩
  rcases R E with ⟨rank, S, a, i, hseed, hi, hai⟩
  exact hai (ghost_selected_coefficient_eq_zero E S a hseed i hi)

#check spectralSeed
#check isolated_seed_mem_atomic
#check isolated_seed_eq
#check ghost_selected_coefficient_eq_zero
#check no_algebraic_seed_with_nonzero_ghost_coordinate
#check bigradedBettiHodge_of_oneSheetCorrespondenceSpectralHits

#print axioms isolated_seed_mem_atomic
#print axioms isolated_seed_eq
#print axioms ghost_selected_coefficient_eq_zero
#print axioms bigradedBettiHodge_of_oneSheetCorrespondenceSpectralHits

end GSTClassicalHodgeFiniteCorrespondenceGhostSpectralExtinction
