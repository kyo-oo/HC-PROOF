import GSTClassicalHodgeOmniversalSeparatorGhostCrown
import GSTClassicalHodgeAtomicDefectDuality
import GSTClassicalHodgeGenuineCycleClassGeometry

/-!
# GST CLASSICAL HODGE — COHOMOLOGICAL PAIRING FRONTIER

The projective/cycle-natural visibility route is now formally blocked: every
genuine cycle-natural image of an algebraic source is again algebraic, hence is
annihilated by an omniversal separator ghost.  The next legitimate operation
must therefore act on the separator itself rather than try to manufacture a
nonzero separator reading from another algebraic output.

This file performs that transformation abstractly at the level of genuine
rational singular cohomology.  A perfect rational cohomological pairing turns
an arbitrary linear detector into a unique dual cohomology class.  Applied to
an omniversal separator ghost, that dual class is:

* nonzero whenever the separator is nonzero;
* orthogonal to every genuine codimension-p cycle class;
* nontrivial on the Hodge direction detected by the ghost.

Thus a hypothetical Hodge failure is transformed from a functional obstruction
into a concrete nonzero cohomology class lying in the pairing-orthogonal
complement of the algebraic cycle-class span.

Crucially, perfectness of the pairing alone does NOT contradict such an
orthogonal class.  Any subsequent extinction theorem must use additional
independently geometric Hodge/polarization information; it must not simply
assume that the orthogonal complement is zero, because that statement is
already equivalent to the desired saturation when restricted to the Hodge
sector.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeCohomologicalPairingFrontier

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeAtomicAnnihilator
open GSTClassicalHodgeGenuineCycleClassGeometry
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeOmniversalSeparatorGhostCrown

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

abbrev Coh (H : HodgeBigradedBettiData V) (p : Nat) :=
  RationalSingularCohomology H.analytification (2 * p)

/-- A rational perfect self-pairing on one even Betti cohomology degree.

`toDual` is the adjoint map `u ↦ <u, ->`.  We package bijectivity rather than
finite dimensionality so this file does not impose an artificial rank bound on
the Stage-2G carrier. -/
structure PerfectCohomologicalPairing
    (H : HodgeBigradedBettiData V) (p : Nat) where
  pair : Coh H p →ₗ[ℚ] Coh H p →ₗ[ℚ] ℚ
  toDual : Coh H p →ₗ[ℚ] (Coh H p →ₗ[ℚ] ℚ) :=
    pair
  toDual_bijective : Function.Bijective toDual

namespace PerfectCohomologicalPairing

variable {p : Nat}

/-- The unique cohomology class representing a rational detector under the
perfect pairing. -/
noncomputable def dualClass
    (P : PerfectCohomologicalPairing H p)
    (ell : Coh H p →ₗ[ℚ] ℚ) : Coh H p :=
  Classical.choose (P.toDual_bijective.2 ell)

/-- The representing class reproduces the detector exactly. -/
theorem dualClass_spec
    (P : PerfectCohomologicalPairing H p)
    (ell : Coh H p →ₗ[ℚ] ℚ) :
    P.toDual (P.dualClass ell) = ell :=
  Classical.choose_spec (P.toDual_bijective.2 ell)

/-- Elementwise form of detector representation. -/
theorem pair_dualClass
    (P : PerfectCohomologicalPairing H p)
    (ell : Coh H p →ₗ[ℚ] ℚ)
    (alpha : Coh H p) :
    P.pair (P.dualClass ell) alpha = ell alpha := by
  have h := LinearMap.congr_fun (P.dualClass_spec ell) alpha
  exact h

/-- A nonzero detector has a nonzero representing class. -/
theorem dualClass_ne_zero
    (P : PerfectCohomologicalPairing H p)
    (ell : Coh H p →ₗ[ℚ] ℚ)
    (hell : ell ≠ 0) :
    P.dualClass ell ≠ 0 := by
  intro hz
  apply hell
  rw [← P.dualClass_spec ell, hz]
  exact map_zero P.toDual

end PerfectCohomologicalPairing

/-- Pairing-orthogonality to the complete genuine codimension-p point-cycle
span. -/
def OrthogonalToAtomicCycleSpan
    {p : Nat}
    (P : PerfectCohomologicalPairing H p)
    (u : Coh H p) : Prop :=
  ∀ alpha : Coh H p,
    alpha ∈ pointCycleClassSpan p (H.cycleClass p) →
      P.pair u alpha = 0

/-- An omniversal separator, represented through a perfect cohomological
pairing, gives one concrete nonzero dual cohomology class. -/
noncomputable def ghostDualClass
    {G : GeometricCycleClassSpine V H}
    {p : Nat}
    (P : PerfectCohomologicalPairing H p)
    (E : OmniversalSeparatorGhost G)
    (hp : E.weight = p) : Coh H p := by
  subst hp
  exact P.dualClass E.separator.detector

/-- **GHOST -> NONZERO DUAL CLASS.** -/
theorem ghostDualClass_ne_zero
    {G : GeometricCycleClassSpine V H}
    (E : OmniversalSeparatorGhost G)
    (P : PerfectCohomologicalPairing H E.weight) :
    P.dualClass E.separator.detector ≠ 0 := by
  exact P.dualClass_ne_zero E.separator.detector E.separator.detector_nonzero

/-- **GHOST -> ALGEBRAIC ORTHOGONALITY.**  The pairing-dual ghost class is
orthogonal to the entire genuine atomic cycle-class span. -/
theorem ghostDualClass_orthogonal_atomic
    {G : GeometricCycleClassSpine V H}
    (E : OmniversalSeparatorGhost G)
    (P : PerfectCohomologicalPairing H E.weight) :
    OrthogonalToAtomicCycleSpan P (P.dualClass E.separator.detector) := by
  intro alpha halpha
  rw [P.pair_dualClass]
  have hker :
      pointCycleClassSpan E.weight (H.cycleClass E.weight) ≤
        LinearMap.ker E.separator.detector :=
    (annihilatesPointCycles_iff_atomicSpan_le_ker
      E.weight (H.cycleClass E.weight) E.separator.detector).mp
      E.separator.annihilates_atoms
  exact hker halpha

/-- The dual ghost class still reads the actually obstructed Hodge direction
nontrivially. -/
theorem ghostDualClass_detects_ghost
    {G : GeometricCycleClassSpine V H}
    (E : OmniversalSeparatorGhost G)
    (P : PerfectCohomologicalPairing H E.weight) :
    P.pair (P.dualClass E.separator.detector) E.hodge.1 ≠ 0 := by
  rw [P.pair_dualClass]
  exact E.separator.detects

/-- Concrete transformed obstruction packet produced by a hypothetical Hodge
failure once a perfect cohomological pairing is available. -/
structure PairingOrthogonalGhost
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (P : PerfectCohomologicalPairing H p) where
  dual : Coh H p
  dual_ne_zero : dual ≠ 0
  hodge : ClassicalHodgeFiber V H p
  orthogonal_atomic : OrthogonalToAtomicCycleSpan P dual
  detects_hodge : P.pair dual hodge.1 ≠ 0

/-- An omniversal separator ghost canonically transforms into a pairing-
orthogonal cohomology ghost. -/
noncomputable def OmniversalSeparatorGhost.toPairingOrthogonalGhost
    {G : GeometricCycleClassSpine V H}
    (E : OmniversalSeparatorGhost G)
    (P : PerfectCohomologicalPairing H E.weight) :
    PairingOrthogonalGhost G E.weight P where
  dual := P.dualClass E.separator.detector
  dual_ne_zero := ghostDualClass_ne_zero E P
  hodge := E.hodge
  orthogonal_atomic := ghostDualClass_orthogonal_atomic E P
  detects_hodge := ghostDualClass_detects_ghost E P

/-- **FAILURE -> PAIRING-ORTHOGONAL GHOST.**  This is the exact classical
cohomological transformation replacing the now-blocked projective-visibility
route. -/
theorem failure_yields_pairingOrthogonalGhost
    (G : GeometricCycleClassSpine V H)
    (P : ∀ p : Nat, PerfectCohomologicalPairing H p)
    (hnot : ¬ BigradedBettiHodgeStatement V H) :
    ∃ p : Nat, Nonempty (PairingOrthogonalGhost G p (P p)) := by
  rcases (not_hodge_iff_nonempty_omniversalSeparatorGhost G).mp hnot with ⟨E⟩
  exact ⟨E.weight, ⟨E.toPairingOrthogonalGhost (P E.weight)⟩⟩

#check PerfectCohomologicalPairing
#check PerfectCohomologicalPairing.dualClass
#check PerfectCohomologicalPairing.pair_dualClass
#check PerfectCohomologicalPairing.dualClass_ne_zero
#check OrthogonalToAtomicCycleSpan
#check ghostDualClass_ne_zero
#check ghostDualClass_orthogonal_atomic
#check ghostDualClass_detects_ghost
#check PairingOrthogonalGhost
#check OmniversalSeparatorGhost.toPairingOrthogonalGhost
#check failure_yields_pairingOrthogonalGhost

#print axioms PerfectCohomologicalPairing.pair_dualClass
#print axioms PerfectCohomologicalPairing.dualClass_ne_zero
#print axioms ghostDualClass_orthogonal_atomic
#print axioms ghostDualClass_detects_ghost
#print axioms failure_yields_pairingOrthogonalGhost

end GSTClassicalHodgeCohomologicalPairingFrontier
