import GSTClassicalHodgeOmniversalSeparatorGhostCrown
import GSTClassicalHodgeLefschetzTomography

/-!
# GST CLASSICAL HODGE — TOMOGRAPHIC GHOST OBSTRUCTION

This module performs the transformation all the way down to a finite GST
signal.

A classical Hodge failure is already equivalent to an omniversal separator
ghost.  Such a ghost detects one genuine classical Hodge basis sheet and is
orthogonal to every state produced by every verified graded geometric program.
Independently, finite GST Lefschetz tomography is unit triangular, so every
nonzero Hodge state has a nonzero exact central-binomial tomography moment.

Applying tomography to the sheet detected by an omniversal ghost therefore
produces a sharper obstruction packet:

* a concrete nonzero finite GST Lefschetz signal;
* a separator which kills every genuine native graded-program orbit state;
* hence no genuine origin program can realize that nonzero signal through the
  separator.

This is a transformation theorem, not an externalization assumption.  No
cycle representative for the detected Hodge basis vector is introduced.
-/

set_option maxHeartbeats 90000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeTomographicGhostObstruction

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeGradedGeometricProgramOrbit
open GSTClassicalHodgeGradedSeparatorBackpropagation
open GSTClassicalHodgeOmniversalSeparatorGhostCrown
open GSTClassicalHodgeLefschetzTomography

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- A Hodge obstruction after exact finite GST tomography.

The stored moment is not merely a formal nonzero vector coordinate: it is the
exact unit-triangular Lefschetz tomography signal whose kernel coefficients
are the GST pure-diagonal world-action coefficients. -/
structure TomographicDarkGhost
    (G : GeometricCycleClassSpine V H) where
  ghost : OmniversalSeparatorGhost G
  momentIndex : Fin
    (fiberedSupportSize
      (fiberedWeightCoordinates V H ghost.weight
        (classicalHodgeBasis V H ghost.weight ghost.sheet)))
  moment_ne_zero :
    lefschetzTomography
      (supportCoordinateVector
        (fiberedWeightCoordinates V H ghost.weight
          (classicalHodgeBasis V H ghost.weight ghost.sheet)))
      momentIndex ≠ 0

/-- The Hodge basis state detected by a separator is necessarily nonzero. -/
theorem ghost_basis_ne_zero
    {G : GeometricCycleClassSpine V H}
    (E : OmniversalSeparatorGhost G) :
    classicalHodgeBasis V H E.weight E.sheet ≠ 0 := by
  intro hzero
  have h := congrArg
    (fun z : ClassicalHodgeFiber V H E.weight => E.separator.detector z.1)
    hzero
  apply E.separator.detects_basis
  simpa using h

/-- Every omniversal separator ghost canonically acquires a nonzero exact GST
Lefschetz-tomography moment. -/
noncomputable def OmniversalSeparatorGhost.toTomographicDarkGhost
    {G : GeometricCycleClassSpine V H}
    (E : OmniversalSeparatorGhost G) :
    TomographicDarkGhost G := by
  rcases nonzero_hodgeClass_has_nonzero_lefschetzMoment
      V H E.weight
      (classicalHodgeBasis V H E.weight E.sheet)
      (ghost_basis_ne_zero E) with ⟨q, hq⟩
  exact ⟨E, q, hq⟩

/-- **TRANSFORMED FAILURE EQUIVALENCE.**
A classical Stage-2G Hodge failure is equivalent to existence of a separator
ghost carrying a concrete nonzero finite GST Lefschetz-tomography signal. -/
theorem not_hodge_iff_nonempty_tomographicDarkGhost
    (G : GeometricCycleClassSpine V H) :
    ¬ BigradedBettiHodgeStatement V H ↔
      Nonempty (TomographicDarkGhost G) := by
  constructor
  · intro hnot
    rcases (not_hodge_iff_nonempty_omniversalSeparatorGhost G).mp hnot with ⟨E⟩
    exact ⟨E.toTomographicDarkGhost⟩
  · rintro ⟨T⟩
    exact (not_hodge_iff_nonempty_omniversalSeparatorGhost G).mpr ⟨T.ghost⟩

/-- Positive form: eliminating tomographic dark ghosts is exactly equivalent
to the Hodge statement. -/
theorem hodge_iff_no_tomographicDarkGhost
    (G : GeometricCycleClassSpine V H) :
    BigradedBettiHodgeStatement V H ↔
      IsEmpty (TomographicDarkGhost G) := by
  constructor
  · intro hHodge
    refine ⟨?_⟩
    intro T
    have hnot : ¬ BigradedBettiHodgeStatement V H :=
      (not_hodge_iff_nonempty_tomographicDarkGhost G).mpr ⟨T⟩
    exact hnot hHodge
  · intro hnone
    by_contra hnot
    have hT := (not_hodge_iff_nonempty_tomographicDarkGhost G).mp hnot
    exact isEmpty_iff.mp hnone (Classical.choice hT)

/-- A tomographic dark ghost has both sides of the transformed obstruction at
once: an internally nonzero GST signal and complete darkness along every
genuine canonical-origin graded geometric program. -/
theorem tomographic_signal_nonzero_and_origin_orbit_dark
    {G : GeometricCycleClassSpine V H}
    (T : TomographicDarkGhost G) :
    lefschetzTomography
      (supportCoordinateVector
        (fiberedWeightCoordinates V H T.ghost.weight
          (classicalHodgeBasis V H T.ghost.weight T.ghost.sheet)))
      T.momentIndex ≠ 0
    ∧
    ∀ P : GradedGeometricProgram V 0 T.ghost.weight,
      T.ghost.separator.detector
        (P.cohomologyEval G (geometricOriginClass V H)) = 0 := by
  refine ⟨T.moment_ne_zero, ?_⟩
  intro P
  exact omniversalGhost_kills_origin_orbit T.ghost P

/-- Exact realization predicate for the transformed signal.  It asks for one
genuine graded geometric program whose separator read is the already-proved
nonzero GST tomography moment. -/
def RealizesTomographicSignal
    {G : GeometricCycleClassSpine V H}
    (T : TomographicDarkGhost G) : Prop :=
  ∃ P : GradedGeometricProgram V 0 T.ghost.weight,
    T.ghost.separator.detector
      (P.cohomologyEval G (geometricOriginClass V H)) =
    lefschetzTomography
      (supportCoordinateVector
        (fiberedWeightCoordinates V H T.ghost.weight
          (classicalHodgeBasis V H T.ghost.weight T.ghost.sheet)))
      T.momentIndex

/-- **TOMOGRAPHIC TERMINAL COLLISION.**
A genuine Hodge ghost cannot geometrically realize its own nonzero GST
Lefschetz-tomography signal.  The left side must vanish by graded separator
backpropagation, whereas the right side is nonzero by unit-triangular GST
tomography. -/
theorem tomographicDarkGhost_not_realizable
    {G : GeometricCycleClassSpine V H}
    (T : TomographicDarkGhost G) :
    ¬ RealizesTomographicSignal T := by
  rintro ⟨P, hreal⟩
  have hzero := omniversalGhost_kills_origin_orbit T.ghost P
  have hm :
      lefschetzTomography
        (supportCoordinateVector
          (fiberedWeightCoordinates V H T.ghost.weight
            (classicalHodgeBasis V H T.ghost.weight T.ghost.sheet)))
        T.momentIndex = 0 := by
    rw [← hreal]
    exact hzero
  exact T.moment_ne_zero hm

/-- If the independently verified graded geometry can realize the canonical
nonzero tomographic signal of every hypothetical transformed ghost, then no
such ghost exists and the Hodge statement follows.  This isolates the final
externalization demand to one scalar-detected origin program per ghost; it does
not assume a basis cycle representative or global matrix-unit naturality. -/
theorem hodge_of_all_tomographic_signals_realizable
    (G : GeometricCycleClassSpine V H)
    (hreal : ∀ T : TomographicDarkGhost G, RealizesTomographicSignal T) :
    BigradedBettiHodgeStatement V H := by
  rw [hodge_iff_no_tomographicDarkGhost G]
  refine ⟨?_⟩
  intro T
  exact tomographicDarkGhost_not_realizable T (hreal T)

#check TomographicDarkGhost
#check ghost_basis_ne_zero
#check OmniversalSeparatorGhost.toTomographicDarkGhost
#check not_hodge_iff_nonempty_tomographicDarkGhost
#check hodge_iff_no_tomographicDarkGhost
#check tomographic_signal_nonzero_and_origin_orbit_dark
#check RealizesTomographicSignal
#check tomographicDarkGhost_not_realizable
#check hodge_of_all_tomographic_signals_realizable

#print axioms ghost_basis_ne_zero
#print axioms not_hodge_iff_nonempty_tomographicDarkGhost
#print axioms hodge_iff_no_tomographicDarkGhost
#print axioms tomographicDarkGhost_not_realizable
#print axioms hodge_of_all_tomographic_signals_realizable

end GSTClassicalHodgeTomographicGhostObstruction
