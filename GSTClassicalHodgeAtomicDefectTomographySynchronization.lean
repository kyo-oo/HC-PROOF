import GSTClassicalHodgeAtomicDefectTomographyGhost
import GSTClassicalHodgeAtomicDefectDuality
import GSTClassicalHodgeLefschetzTomography

/-!
# GST CLASSICAL HODGE — ATOMIC DEFECT / TOMOGRAPHY SYNCHRONIZATION

A surviving Hodge ghost already carries two nonzero signals on the same basis
sheet:

* a nonzero class in the genuine atomic defect quotient;
* a nonzero finite GST Lefschetz-tomography moment.

This file synchronizes those signals without introducing a cycle
representative.  Because the separator annihilates the complete atomic
cycle-class span, it descends canonically to a linear functional on the atomic
defect quotient.  Rational rescaling then normalizes that descended functional
to read exactly the selected nonzero GST tomography moment on the ghost defect.

This is strictly a quotient-level comparison.  It does NOT assert that a GST
matrix unit, Lefschetz operator, or projective correspondence descends to native
cycles, and it does not make the defect vanish.  Instead it gives the precise
common scalar observable on which a future independent geometric extinction
law would have to act.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeAtomicDefectTomographySynchronization

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeAtomicAnnihilator
open GSTClassicalHodgeAtomicDefectDuality
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeLefschetzTomography
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeOmniversalSeparatorGhostCrown
open GSTClassicalHodgeAtomicDefectTomographyGhost

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- The separator detector factors through the genuine atomic defect quotient
because it vanishes on the complete atomic span. -/
noncomputable def ghostDefectDetector
    {G : GeometricCycleClassSpine V H}
    (E : OmniversalSeparatorGhost G) :
    AtomicDefectSpace V H E.weight →ₗ[ℚ] ℚ :=
  Submodule.liftQ
    (pointCycleClassSpan E.weight (H.cycleClass E.weight))
    E.separator.detector
    ((annihilatesPointCycles_iff_atomicSpan_le_ker
      E.weight (H.cycleClass E.weight) E.separator.detector).mp
      E.separator.annihilates_atoms)

/-- Evaluation of the descended detector on a quotient class is exactly the
original separator evaluation on any representative. -/
theorem ghostDefectDetector_mk
    {G : GeometricCycleClassSpine V H}
    (E : OmniversalSeparatorGhost G)
    (alpha : RationalSingularCohomology H.analytification (2 * E.weight)) :
    ghostDefectDetector E (Submodule.Quotient.mk alpha) =
      E.separator.detector alpha := by
  rfl

/-- The descended quotient detector sees the ghost's genuine atomic defect
nontrivially. -/
theorem ghostDefectDetector_ghostAtomicDefect_ne_zero
    {G : GeometricCycleClassSpine V H}
    (E : OmniversalSeparatorGhost G) :
    ghostDefectDetector E (ghostAtomicDefect E) ≠ 0 := by
  rw [ghostAtomicDefect, atomicDefectLinearMap_apply]
  rw [ghostDefectDetector_mk]
  exact E.separator.detects_basis

/-- Canonical nonzero GST tomography scalar selected by the ghost. -/
noncomputable def ghostTomographyScalar
    {G : GeometricCycleClassSpine V H}
    (E : OmniversalSeparatorGhost G) : ℚ :=
  let q := Classical.choose (ghost_basis_has_nonzero_lefschetzMoment E)
  lefschetzTomography
    (supportCoordinateVector
      (fiberedWeightCoordinates V H E.weight
        (classicalHodgeBasis V H E.weight E.sheet))) q

theorem ghostTomographyScalar_ne_zero
    {G : GeometricCycleClassSpine V H}
    (E : OmniversalSeparatorGhost G) :
    ghostTomographyScalar E ≠ 0 := by
  exact Classical.choose_spec (ghost_basis_has_nonzero_lefschetzMoment E)

/-- Rational normalization factor taking the quotient detector's nonzero ghost
read to the selected GST tomography moment. -/
noncomputable def ghostSynchronizationScale
    {G : GeometricCycleClassSpine V H}
    (E : OmniversalSeparatorGhost G) : ℚ :=
  ghostTomographyScalar E /
    ghostDefectDetector E (ghostAtomicDefect E)

/-- The normalized defect readout. -/
noncomputable def synchronizedDefectRead
    {G : GeometricCycleClassSpine V H}
    (E : OmniversalSeparatorGhost G) :
    AtomicDefectSpace V H E.weight →ₗ[ℚ] ℚ :=
  ghostSynchronizationScale E • ghostDefectDetector E

/-- **EXACT DEFECT/TOMOGRAPHY SYNCHRONIZATION.**  The normalized quotient
functional reads the genuine nonzero atomic defect as exactly the nonzero GST
tomography moment selected from the same failed Hodge sheet. -/
theorem synchronizedDefectRead_ghostAtomicDefect
    {G : GeometricCycleClassSpine V H}
    (E : OmniversalSeparatorGhost G) :
    synchronizedDefectRead E (ghostAtomicDefect E) =
      ghostTomographyScalar E := by
  unfold synchronizedDefectRead ghostSynchronizationScale
  simp only [LinearMap.smul_apply, smul_eq_mul]
  let v := ghostDefectDetector E (ghostAtomicDefect E)
  let m := ghostTomographyScalar E
  have hv : v ≠ 0 := by
    simpa [v] using ghostDefectDetector_ghostAtomicDefect_ne_zero E
  change (m / v) * v = m
  field_simp [hv]

/-- The synchronized quotient functional itself is nonzero. -/
theorem synchronizedDefectRead_ne_zero
    {G : GeometricCycleClassSpine V H}
    (E : OmniversalSeparatorGhost G) :
    synchronizedDefectRead E ≠ 0 := by
  intro hz
  have hval := LinearMap.congr_fun hz (ghostAtomicDefect E)
  rw [synchronizedDefectRead_ghostAtomicDefect E] at hval
  exact ghostTomographyScalar_ne_zero E hval

/-- Combined quotient/tomography obstruction packet. -/
structure SynchronizedAtomicDefectGhost
    (G : GeometricCycleClassSpine V H) where
  ghost : OmniversalSeparatorGhost G
  read : AtomicDefectSpace V H ghost.weight →ₗ[ℚ] ℚ
  read_ne_zero : read ≠ 0
  defect_nonzero : ghostAtomicDefect ghost ≠ 0
  tomography_nonzero : ghostTomographyScalar ghost ≠ 0
  synchronized :
    read (ghostAtomicDefect ghost) = ghostTomographyScalar ghost

noncomputable def OmniversalSeparatorGhost.toSynchronizedAtomicDefectGhost
    {G : GeometricCycleClassSpine V H}
    (E : OmniversalSeparatorGhost G) :
    SynchronizedAtomicDefectGhost G where
  ghost := E
  read := synchronizedDefectRead E
  read_ne_zero := synchronizedDefectRead_ne_zero E
  defect_nonzero := ghostAtomicDefect_ne_zero E
  tomography_nonzero := ghostTomographyScalar_ne_zero E
  synchronized := synchronizedDefectRead_ghostAtomicDefect E

/-- **HODGE FAILURE -> SYNCHRONIZED NONZERO DEFECT/TOMOGRAPHY GHOST.** -/
theorem failure_yields_synchronizedAtomicDefectGhost
    (G : GeometricCycleClassSpine V H)
    (hnot : ¬ BigradedBettiHodgeStatement V H) :
    Nonempty (SynchronizedAtomicDefectGhost G) := by
  rcases (not_hodge_iff_nonempty_omniversalSeparatorGhost G).mp hnot with ⟨E⟩
  exact ⟨E.toSynchronizedAtomicDefectGhost⟩

#check ghostDefectDetector
#check ghostDefectDetector_mk
#check ghostDefectDetector_ghostAtomicDefect_ne_zero
#check ghostTomographyScalar
#check ghostTomographyScalar_ne_zero
#check ghostSynchronizationScale
#check synchronizedDefectRead
#check synchronizedDefectRead_ghostAtomicDefect
#check synchronizedDefectRead_ne_zero
#check SynchronizedAtomicDefectGhost
#check OmniversalSeparatorGhost.toSynchronizedAtomicDefectGhost
#check failure_yields_synchronizedAtomicDefectGhost

#print axioms ghostDefectDetector_ghostAtomicDefect_ne_zero
#print axioms ghostTomographyScalar_ne_zero
#print axioms synchronizedDefectRead_ghostAtomicDefect
#print axioms synchronizedDefectRead_ne_zero
#print axioms failure_yields_synchronizedAtomicDefectGhost

end GSTClassicalHodgeAtomicDefectTomographySynchronization
