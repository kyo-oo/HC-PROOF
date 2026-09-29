import GSTClassicalHodgeLimitlessSeparatorGhost
import GSTClassicalHodgeFiniteSupportChart

/-!
# GST CLASSICAL HODGE — SEPARATOR READS ARE FINITE GST POINCARE READS

The classical atomic separator and the finite GST Poincare observable were
previously connected only indirectly.

`GSTClassicalHodgeLimitlessSeparatorGhost` proves that an ambient detector
`ell` is represented exactly by its completed fibered probe:

    < coords(alpha), separatorProbe(ell) > = ell(alpha).

`GSTClassicalHodgeFiniteSupportChart` proves that every compact/completed
fibered pairing is literally the Poincare top pairing in the finite GST chart
of the live support.

Composing those two theorems gives the exact cross-cosmology identity used by
the brute-force return attack:

    ell(alpha)
      = finiteGSTPoincare(
          supportWorld(coords(alpha)),
          dualizedSupportProbe(coords(alpha), separatorProbe(ell))).

Thus the genuine algebraic-annihilator detector is not merely analogous to a
GST observable.  On every individual Hodge state it IS the finite GST Poincare
observable of that state's canonical local chart.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeSeparatorFiniteGSTPoincare

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicAnnihilator
open GSTClassicalHodgeLimitlessSeparatorGhost
open GSTClassicalHodgeFiniteSupportChart

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- **EXACT SEPARATOR / FINITE-GST POINCARE IDENTITY.**
The value of any ambient rational functional on a genuine Hodge vector is
exactly one finite GST Poincare top pairing in the vector's canonical support
chart. -/
theorem detector_eq_finiteGSTPoincare
    (ell : GSTGeometricRealizationStage2F.RationalSingularCohomology
      H.analytification (2 * p) →ₗ[ℚ] ℚ)
    (alpha : ClassicalHodgeFiber V H p) :
    ell alpha.1 =
      rationalWorldTopPairing
        (fiberedSupportWorld (fiberedWeightCoordinates V H p alpha))
        (dualizedSupportProbe
          (fiberedWeightCoordinates V H p alpha)
          (separatorFiberedProbe (V := V) (H := H) p ell)) := by
  rw [← fiberedPairing_separatorProbe
    (V := V) (H := H) p ell alpha]
  exact fiberedPairing_eq_finiteGSTPoincare
    (fiberedWeightCoordinates V H p alpha)
    (separatorFiberedProbe (V := V) (H := H) p ell)

/-- Nonzero detector read is exactly nonzero finite GST Poincare read. -/
theorem detector_ne_zero_iff_finiteGSTPoincare_ne_zero
    (ell : GSTGeometricRealizationStage2F.RationalSingularCohomology
      H.analytification (2 * p) →ₗ[ℚ] ℚ)
    (alpha : ClassicalHodgeFiber V H p) :
    ell alpha.1 ≠ 0 ↔
      rationalWorldTopPairing
        (fiberedSupportWorld (fiberedWeightCoordinates V H p alpha))
        (dualizedSupportProbe
          (fiberedWeightCoordinates V H p alpha)
          (separatorFiberedProbe (V := V) (H := H) p ell)) ≠ 0 := by
  rw [detector_eq_finiteGSTPoincare ell alpha]

/-- For an actual atomic separator, its nonzero basis detection is therefore a
nonzero native finite-world Poincare pairing. -/
theorem basisSeparator_finiteGSTPoincare_ne_zero
    {i : ClassicalHodgeBasisIndex V H p}
    (S : BasisAtomicSeparator V H p i) :
    rationalWorldTopPairing
        (fiberedSupportWorld
          (fiberedWeightCoordinates V H p
            (classicalHodgeBasis V H p i)))
        (dualizedSupportProbe
          (fiberedWeightCoordinates V H p
            (classicalHodgeBasis V H p i))
          (separatorFiberedProbe (V := V) (H := H) p S.detector)) ≠ 0 := by
  exact (detector_ne_zero_iff_finiteGSTPoincare_ne_zero
    S.detector (classicalHodgeBasis V H p i)).mp S.detects_basis

/-- Conversely every algebraic Hodge class has zero finite GST Poincare read
against the separator probe, because the separator kills the complete atomic
cycle-class span. -/
theorem basisSeparator_finiteGSTPoincare_eq_zero_of_algebraic
    {i : ClassicalHodgeBasisIndex V H p}
    (S : BasisAtomicSeparator V H p i)
    (alpha : ClassicalHodgeFiber V H p)
    (halg : alpha.1 ∈
      GSTClassicalHodgeAtomicSpan.pointCycleClassSpan p (H.cycleClass p)) :
    rationalWorldTopPairing
        (fiberedSupportWorld (fiberedWeightCoordinates V H p alpha))
        (dualizedSupportProbe
          (fiberedWeightCoordinates V H p alpha)
          (separatorFiberedProbe (V := V) (H := H) p S.detector)) = 0 := by
  rw [← detector_eq_finiteGSTPoincare S.detector alpha]
  have hker :
      GSTClassicalHodgeAtomicSpan.pointCycleClassSpan p (H.cycleClass p) ≤
        LinearMap.ker S.detector :=
    (GSTClassicalHodgeAtomicAnnihilator.annihilatesPointCycles_iff_atomicSpan_le_ker
      p (H.cycleClass p) S.detector).mp S.annihilates_atoms
  exact hker halg

/-- Separator crown: a classical Hodge obstruction is literally a finite GST
Poincare observable which is nonzero on the obstructed state and zero on every
actual algebraic state. -/
theorem basisSeparator_finiteGSTPoincare_crown
    {i : ClassicalHodgeBasisIndex V H p}
    (S : BasisAtomicSeparator V H p i) :
    rationalWorldTopPairing
        (fiberedSupportWorld
          (fiberedWeightCoordinates V H p
            (classicalHodgeBasis V H p i)))
        (dualizedSupportProbe
          (fiberedWeightCoordinates V H p
            (classicalHodgeBasis V H p i))
          (separatorFiberedProbe (V := V) (H := H) p S.detector)) ≠ 0
    ∧ ∀ alpha : ClassicalHodgeFiber V H p,
      alpha.1 ∈ GSTClassicalHodgeAtomicSpan.pointCycleClassSpan p (H.cycleClass p) →
        rationalWorldTopPairing
          (fiberedSupportWorld (fiberedWeightCoordinates V H p alpha))
          (dualizedSupportProbe
            (fiberedWeightCoordinates V H p alpha)
            (separatorFiberedProbe (V := V) (H := H) p S.detector)) = 0 := by
  exact ⟨basisSeparator_finiteGSTPoincare_ne_zero S,
    basisSeparator_finiteGSTPoincare_eq_zero_of_algebraic S⟩

#check detector_eq_finiteGSTPoincare
#check detector_ne_zero_iff_finiteGSTPoincare_ne_zero
#check basisSeparator_finiteGSTPoincare_ne_zero
#check basisSeparator_finiteGSTPoincare_eq_zero_of_algebraic
#check basisSeparator_finiteGSTPoincare_crown

#print axioms detector_eq_finiteGSTPoincare
#print axioms basisSeparator_finiteGSTPoincare_ne_zero
#print axioms basisSeparator_finiteGSTPoincare_eq_zero_of_algebraic
#print axioms basisSeparator_finiteGSTPoincare_crown

end GSTClassicalHodgeSeparatorFiniteGSTPoincare
