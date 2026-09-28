import GSTClassicalHodgeAtomicDefectTomographySynchronization

/-!
# GST CLASSICAL HODGE — TOMOGRAPHY SYNCHRONIZATION AUDIT

The synchronized atomic-defect/tomography packet is a maximally explicit
encoding of one Hodge failure: it carries the actual omniversal separator, the
nonzero atomic quotient defect, a descended nonzero quotient functional, and an
exact nonzero GST tomography scalar on the same failed sheet.

This file proves that the packet is not itself an extra contradiction.  Its
existence is exactly equivalent to failure of the Stage-2G Hodge statement.
Consequently no argument may finish merely by rephrasing, normalizing, or
injectively reconstructing the tomography coordinates.  The next theorem must
supply genuinely new geometry that forbids this synchronized packet.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeTomographySynchronizationAudit

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeOmniversalSeparatorGhostCrown
open GSTClassicalHodgeAtomicDefectTomographySynchronization

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- **EXACT AUDIT.**  A synchronized nonzero atomic-defect/GST-tomography
packet exists exactly when the Stage-2G Hodge statement fails. -/
theorem not_hodge_iff_nonempty_synchronizedAtomicDefectGhost
    (G : GeometricCycleClassSpine V H) :
    ¬ BigradedBettiHodgeStatement V H ↔
      Nonempty (SynchronizedAtomicDefectGhost G) := by
  constructor
  · exact failure_yields_synchronizedAtomicDefectGhost G
  · rintro ⟨S⟩
    exact (not_hodge_iff_nonempty_omniversalSeparatorGhost G).2 ⟨S.ghost⟩

/-- Eliminating every synchronized packet is therefore exactly sufficient for
Hodge.  This theorem is useful as a final integration surface, but `extinguish`
must come from independent geometry rather than tomography injectivity itself. -/
theorem hodge_of_no_synchronizedAtomicDefectGhost
    (G : GeometricCycleClassSpine V H)
    (extinguish : IsEmpty (SynchronizedAtomicDefectGhost G)) :
    BigradedBettiHodgeStatement V H := by
  by_contra hnot
  rcases failure_yields_synchronizedAtomicDefectGhost G hnot with ⟨S⟩
  exact extinguish.false S

/-- Conversely Hodge itself empties the synchronized obstruction type. -/
theorem no_synchronizedAtomicDefectGhost_of_hodge
    (G : GeometricCycleClassSpine V H)
    (hHodge : BigradedBettiHodgeStatement V H) :
    IsEmpty (SynchronizedAtomicDefectGhost G) := by
  refine ⟨?_⟩
  intro S
  have hnot : ¬ BigradedBettiHodgeStatement V H :=
    (not_hodge_iff_nonempty_synchronizedAtomicDefectGhost G).2 ⟨S⟩
  exact hnot hHodge

/-- Empty synchronized tomography obstruction is equivalent to Hodge. -/
theorem synchronizedAtomicDefectGhost_empty_iff_hodge
    (G : GeometricCycleClassSpine V H) :
    IsEmpty (SynchronizedAtomicDefectGhost G) ↔
      BigradedBettiHodgeStatement V H := by
  constructor
  · exact hodge_of_no_synchronizedAtomicDefectGhost G
  · exact no_synchronizedAtomicDefectGhost_of_hodge G

#check not_hodge_iff_nonempty_synchronizedAtomicDefectGhost
#check hodge_of_no_synchronizedAtomicDefectGhost
#check no_synchronizedAtomicDefectGhost_of_hodge
#check synchronizedAtomicDefectGhost_empty_iff_hodge

#print axioms not_hodge_iff_nonempty_synchronizedAtomicDefectGhost
#print axioms hodge_of_no_synchronizedAtomicDefectGhost
#print axioms synchronizedAtomicDefectGhost_empty_iff_hodge

end GSTClassicalHodgeTomographySynchronizationAudit
