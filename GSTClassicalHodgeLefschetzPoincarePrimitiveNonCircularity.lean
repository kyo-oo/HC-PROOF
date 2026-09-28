import GSTClassicalHodgeAtomicNaturalLefschetzPoincareClosure
import GSTClassicalHodgeAtomicNaturalLefschetzNonCircularity

/-!
# GST CLASSICAL HODGE — LEFSCHETZ–POINCARE PRIMITIVE NONCIRCULARITY

The atomic-natural Lefschetz–Poincare closure correctly compresses a complete
matrix-unit arsenal to two primitive operators on each distinct two-sheet
chart.  Compression alone, however, is not a geometric construction.

This file splices the primitive closure directly to the bare-Lefschetz
noncircularity audit.  The `lefschetz` member of an
`AtomicNaturalLefschetzPoincarePair` is exactly an atomic-natural realization
of the universal two-slot bare `L^2` Hodge operator.  Therefore, whenever one
live algebraic source has nonzero source coordinate, existence of the primitive
pair already forces the target basis sheet into the genuine atomic cycle-class
span.

In particular a separator which annihilates the atomic span but detects the
target sheet forbids such a primitive pair.  Thus Poincare compression does not
weaken the final geometric obligation past the bare-Lefschetz barrier; any
actual construction of the pair must independently prove the target-crossing
geometry rather than postulate its Hodge action.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeLefschetzPoincarePrimitiveNonCircularity

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeAtomicDefectEquivariantIrreducibility
open GSTClassicalHodgeAtomicNaturalLefschetzNonCircularity
open GSTClassicalHodgeAtomicNaturalLefschetzPoincareClosure

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- One atomic-natural Lefschetz–Poincare pair already forces its target sheet
algebraic from any live algebraic source in the pair's source coordinate. -/
theorem targetBasis_algebraic_of_lefschetzPoincarePair
    (i j : ClassicalHodgeBasisIndex V H p)
    (hij : i ≠ j)
    (a : ClassicalHodgeFiber V H p)
    (haAlg : a ∈ AlgebraicHodgeSubspace V H p)
    (hi : hodgeCoordinate i a ≠ 0)
    (R : AtomicNaturalLefschetzPoincarePair
      (V := V) (H := H) i j hij) :
    (classicalHodgeBasis V H p j).1 ∈
      pointCycleClassSpan p (H.cycleClass p) := by
  exact targetBasis_algebraic_of_atomicNatural_bareLefschetz
    i j a haAlg hi R.lefschetz R.lefschetz_hodge

/-- **SEPARATOR FORBIDS LEFSCHETZ–POINCARE PRIMITIVE PAIR.**
If a detector kills the complete atomic span but sees the target sheet, then no
atomic-natural Lefschetz–Poincare pair can connect a live algebraic source to
that target. -/
theorem no_lefschetzPoincarePair_to_separatorSheet
    (i j : ClassicalHodgeBasisIndex V H p)
    (hij : i ≠ j)
    (a : ClassicalHodgeFiber V H p)
    (haAlg : a ∈ AlgebraicHodgeSubspace V H p)
    (hi : hodgeCoordinate i a ≠ 0)
    (ell : RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ] ℚ)
    (hann : pointCycleClassSpan p (H.cycleClass p) ≤ LinearMap.ker ell)
    (hdetect : ell (classicalHodgeBasis V H p j).1 ≠ 0) :
    IsEmpty
      (AtomicNaturalLefschetzPoincarePair
        (V := V) (H := H) i j hij) := by
  refine ⟨?_⟩
  intro R
  have hj := targetBasis_algebraic_of_lefschetzPoincarePair
    i j hij a haAlg hi R
  exact hdetect (hann hj)

/-- Pointwise contradiction form for consumers that already have a pair. -/
theorem lefschetzPoincarePair_false_of_separator
    (i j : ClassicalHodgeBasisIndex V H p)
    (hij : i ≠ j)
    (a : ClassicalHodgeFiber V H p)
    (haAlg : a ∈ AlgebraicHodgeSubspace V H p)
    (hi : hodgeCoordinate i a ≠ 0)
    (ell : RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ] ℚ)
    (hann : pointCycleClassSpan p (H.cycleClass p) ≤ LinearMap.ker ell)
    (hdetect : ell (classicalHodgeBasis V H p j).1 ≠ 0)
    (R : AtomicNaturalLefschetzPoincarePair
      (V := V) (H := H) i j hij) : False :=
  (no_lefschetzPoincarePair_to_separatorSheet
    i j hij a haAlg hi ell hann hdetect).false R

#check targetBasis_algebraic_of_lefschetzPoincarePair
#check no_lefschetzPoincarePair_to_separatorSheet
#check lefschetzPoincarePair_false_of_separator

#print axioms targetBasis_algebraic_of_lefschetzPoincarePair
#print axioms no_lefschetzPoincarePair_to_separatorSheet
#print axioms lefschetzPoincarePair_false_of_separator

end GSTClassicalHodgeLefschetzPoincarePrimitiveNonCircularity
