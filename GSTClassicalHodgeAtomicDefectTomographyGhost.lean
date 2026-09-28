import GSTClassicalHodgeAtomicDefectDuality
import GSTClassicalHodgeAtomicAnnihilator
import GSTClassicalHodgeOmniversalSeparatorGhostCrown
import GSTClassicalHodgeLefschetzTomography

/-!
# GST CLASSICAL HODGE — ATOMIC-DEFECT / TOMOGRAPHY GHOST

The projective-visibility route cannot be the unconditional closure: every
cycle-class-natural image of an algebraic source is again algebraic and is
therefore killed by a surviving separator.  The correct transformed target is
the actual quotient defect itself.

For an omniversal separator ghost at weight `p` and sheet `i` this file proves
simultaneously:

* the basis class has a NONZERO image in the genuine atomic defect quotient
  `H^(p,p)_Q / span{point-cycle classes}`;
* the same basis class has a NONZERO finite GST Lefschetz-tomography moment.

Thus a hypothetical Hodge counterexample becomes one concrete state carrying
both a classical algebraic-defect signal and a limitless GST spectral signal.
No geometric correspondence is asked to have nonzero separator reading, and no
basis-cycle representative is assumed.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeAtomicDefectTomographyGhost

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeAtomicAnnihilator
open GSTClassicalHodgeAtomicDefectDuality
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeOmniversalSeparatorGhostCrown
open GSTClassicalHodgeLefschetzTomography
open GSTClassicalHodgeSingleSheetCrown
open GSTClassicalHodgeFiniteSupportChart

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- The genuine quotient defect carried by the Hodge basis sheet selected by
an omniversal ghost. -/
noncomputable def ghostAtomicDefect
    {G : GeometricCycleClassSpine V H}
    (E : OmniversalSeparatorGhost G) :
    AtomicDefectSpace V H E.weight :=
  atomicDefectLinearMap V H E.weight
    (classicalHodgeBasis V H E.weight E.sheet)

/-- The ghost-selected Hodge basis vector is nonzero. -/
theorem ghost_basis_ne_zero
    {G : GeometricCycleClassSpine V H}
    (E : OmniversalSeparatorGhost G) :
    classicalHodgeBasis V H E.weight E.sheet ≠ 0 := by
  intro hz
  have hread := E.separator.detects_basis
  rw [hz, map_zero] at hread
  exact hread rfl

/-- **GHOST -> NONZERO ATOMIC DEFECT.**  The quotient class of the selected
Hodge basis sheet cannot vanish: otherwise that basis class would lie in the
atomic cycle-class span, where the separator is zero, contradicting its stored
nonzero basis detection. -/
theorem ghostAtomicDefect_ne_zero
    {G : GeometricCycleClassSpine V H}
    (E : OmniversalSeparatorGhost G) :
    ghostAtomicDefect E ≠ 0 := by
  intro hzero
  have hmk :
      Submodule.Quotient.mk
        ((classicalHodgeBasis V H E.weight E.sheet).1) =
        (0 : AtomicDefectSpace V H E.weight) := by
    simpa [ghostAtomicDefect, atomicDefectLinearMap_apply] using hzero
  have hmem :
      (classicalHodgeBasis V H E.weight E.sheet).1 ∈
        pointCycleClassSpan E.weight (H.cycleClass E.weight) :=
    (Submodule.Quotient.mk_eq_zero
      (pointCycleClassSpan E.weight (H.cycleClass E.weight))).mp hmk
  have hker :
      pointCycleClassSpan E.weight (H.cycleClass E.weight) ≤
        LinearMap.ker E.separator.detector :=
    (annihilatesPointCycles_iff_atomicSpan_le_ker
      E.weight (H.cycleClass E.weight) E.separator.detector).mp
      E.separator.annihilates_atoms
  have hzdet := hker hmem
  rw [LinearMap.mem_ker] at hzdet
  exact E.separator.detects_basis hzdet

/-- The same failed basis sheet carries a nonzero finite GST tomography
moment. -/
theorem ghost_basis_has_nonzero_lefschetzMoment
    {G : GeometricCycleClassSpine V H}
    (E : OmniversalSeparatorGhost G) :
    ∃ q : Fin
        (fiberedSupportSize
          (fiberedWeightCoordinates V H E.weight
            (classicalHodgeBasis V H E.weight E.sheet))),
      lefschetzTomography
        (supportCoordinateVector
          (fiberedWeightCoordinates V H E.weight
            (classicalHodgeBasis V H E.weight E.sheet))) q ≠ 0 := by
  exact nonzero_hodgeClass_has_nonzero_lefschetzMoment
    V H E.weight
    (classicalHodgeBasis V H E.weight E.sheet)
    (ghost_basis_ne_zero E)

/-- One counterexample state expressed simultaneously in the genuine algebraic
quotient and the finite limitless tomography world. -/
structure AtomicDefectTomographyGhost
    (G : GeometricCycleClassSpine V H) where
  weight : Nat
  sheet : ClassicalHodgeBasisIndex V H weight
  separator : BasisAtomicSeparator V H weight sheet
  defect : AtomicDefectSpace V H weight
  defect_eq :
    defect = atomicDefectLinearMap V H weight
      (classicalHodgeBasis V H weight sheet)
  defect_ne_zero : defect ≠ 0
  momentIndex : Fin
    (fiberedSupportSize
      (fiberedWeightCoordinates V H weight
        (classicalHodgeBasis V H weight sheet)))
  moment_nonzero :
    lefschetzTomography
      (supportCoordinateVector
        (fiberedWeightCoordinates V H weight
          (classicalHodgeBasis V H weight sheet))) momentIndex ≠ 0

/-- Canonical transformation from an omniversal separator ghost into the
atomic-defect/tomography obstruction packet. -/
noncomputable def OmniversalSeparatorGhost.toAtomicDefectTomographyGhost
    {G : GeometricCycleClassSpine V H}
    (E : OmniversalSeparatorGhost G) :
    AtomicDefectTomographyGhost G := by
  let q := Classical.choose (ghost_basis_has_nonzero_lefschetzMoment E)
  refine {
    weight := E.weight
    sheet := E.sheet
    separator := E.separator
    defect := ghostAtomicDefect E
    defect_eq := rfl
    defect_ne_zero := ghostAtomicDefect_ne_zero E
    momentIndex := q
    moment_nonzero := ?_
  }
  exact Classical.choose_spec (ghost_basis_has_nonzero_lefschetzMoment E)

/-- **FAILURE -> NONZERO QUOTIENT DEFECT + NONZERO GST MOMENT.** -/
theorem failure_yields_atomicDefectTomographyGhost
    (G : GeometricCycleClassSpine V H)
    (hnot : ¬ BigradedBettiHodgeStatement V H) :
    Nonempty (AtomicDefectTomographyGhost G) := by
  rcases (not_hodge_iff_nonempty_omniversalSeparatorGhost G).mp hnot with ⟨E⟩
  exact ⟨E.toAtomicDefectTomographyGhost⟩

/-- The transformation is exact: existence of such a packet is equivalent to
failure of the Stage-2G Hodge statement. -/
theorem not_hodge_iff_nonempty_atomicDefectTomographyGhost
    (G : GeometricCycleClassSpine V H) :
    ¬ BigradedBettiHodgeStatement V H ↔
      Nonempty (AtomicDefectTomographyGhost G) := by
  constructor
  · exact failure_yields_atomicDefectTomographyGhost G
  · rintro ⟨E⟩ hHodge
    have hnone :=
      (bigradedBettiHodgeStatement_iff_no_basis_separator V H).mp
        hHodge E.weight E.sheet
    exact isEmpty_iff.mp hnone E.separator

#check ghostAtomicDefect
#check ghost_basis_ne_zero
#check ghostAtomicDefect_ne_zero
#check ghost_basis_has_nonzero_lefschetzMoment
#check AtomicDefectTomographyGhost
#check OmniversalSeparatorGhost.toAtomicDefectTomographyGhost
#check failure_yields_atomicDefectTomographyGhost
#check not_hodge_iff_nonempty_atomicDefectTomographyGhost

#print axioms ghostAtomicDefect_ne_zero
#print axioms ghost_basis_has_nonzero_lefschetzMoment
#print axioms failure_yields_atomicDefectTomographyGhost
#print axioms not_hodge_iff_nonempty_atomicDefectTomographyGhost

end GSTClassicalHodgeAtomicDefectTomographyGhost
