import GSTClassicalHodgeOmniversalSeparatorGhostCrown
import GSTClassicalHodgeGradedProgramSpectralSaturation
import GSTClassicalHodgeAtomicAnnihilator

/-!
# GST CLASSICAL HODGE — TRANSFORMED COSMOLOGY GHOST EXTINCTION

A genuine Stage-2G failure has already been transformed into an omniversal
completed GST separator ghost.  This file performs the next reduction entirely
inside the established graded-program / spectral cosmology.

The transformed obstruction carries one detected Hodge sheet.  If that exact
sheet is visible in a one-slot spectral chart whose observable is an
independently verified graded geometric program, graded spectral saturation
isolates the sheet inside the genuine program orbit.  But the separator
annihilates the whole algebraic/program orbit while detecting that same sheet.
Contradiction.

Thus, after the classical-to-GST transformation, the remaining problem is one
visibility statement for one sheet.  No basis-cycle representative, arbitrary
ambient extension, matrix-unit externalization, or Hodge-surjectivity premise
is used.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeTransformedCosmologyGhostExtinction

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeAtomicAnnihilator
open GSTClassicalHodgeSingleSheetCrown
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeGradedGeometricProgramOrbit
open GSTClassicalHodgeGradedGeometricOrbitAlgebra
open GSTClassicalHodgeGradedProgramSpectralSaturation
open GSTClassicalHodgeOmniversalSeparatorGhostCrown

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- The exact transformed visibility packet: one verified one-slot GST spectral
chart whose unique selected coordinate is the sheet detected by the ghost and
is visible in the genuine graded geometric orbit. -/
structure SingletonGhostSpectralVisibility
    (G : GeometricCycleClassSpine V H)
    (E : OmniversalSeparatorGhost G) where
  spectral :
    GradedProgramSpectralFamily
      (V := V) (H := H) (p := E.weight) G (Fin 1)
  sheet_eq : spectral.basisIndex 0 = E.sheet
  visible : spectral.CoordinateVisible 0

/-- The unique coordinate of a one-slot visibility packet is visible at every
index of `Fin 1`. -/
theorem singleton_visibility_all
    (G : GeometricCycleClassSpine V H)
    (E : OmniversalSeparatorGhost G)
    (W : SingletonGhostSpectralVisibility G E) :
    ∀ k : Fin 1, W.spectral.CoordinateVisible k := by
  intro k
  have hk : k = 0 := Subsingleton.elim _ _
  simpa [hk] using W.visible

/-- **ONE VISIBLE GHOST SHEET IS IMPOSSIBLE.**
The GST spectral extractor places the detected sheet in the verified graded
program orbit.  Program-orbit algebraicity then places it in the genuine
atomic cycle-class span, where the separator must vanish.  This contradicts
the separator's stored nonzero reading on that same sheet. -/
theorem ghost_false_of_singleton_spectral_visibility
    (G : GeometricCycleClassSpine V H)
    (E : OmniversalSeparatorGhost G)
    (W : SingletonGhostSpectralVisibility G E) : False := by
  have hmem0 :=
    W.spectral.selected_basis_mem_orbit
      (singleton_visibility_all G E W) 0
  have hmem :
      (classicalHodgeBasis V H E.weight E.sheet).1 ∈
        geometricProgramOrbitModule G E.weight := by
    simpa [W.sheet_eq] using hmem0
  have hrange :
      (classicalHodgeBasis V H E.weight E.sheet).1 ∈
        LinearMap.range (H.cycleClass E.weight) :=
    geometricProgramOrbitModule_le_cycleClass_range G E.weight hmem
  have hatomic :
      (classicalHodgeBasis V H E.weight E.sheet).1 ∈
        pointCycleClassSpan E.weight (H.cycleClass E.weight) := by
    rw [← smoothProjective_cycleClass_range_eq_atomic_span V H E.weight]
    exact hrange
  have hker :
      pointCycleClassSpan E.weight (H.cycleClass E.weight) ≤
        LinearMap.ker E.separator.detector :=
    (annihilatesPointCycles_iff_atomicSpan_le_ker
      E.weight (H.cycleClass E.weight) E.separator.detector).mp
      E.separator.annihilates_atoms
  exact E.separator.detects_basis (hker hatomic)

/-- **TRANSFORMED COSMOLOGY CROWN.**
If every possible omniversal GST separator ghost admits one verified singleton
spectral visibility chart for its detected sheet, the genuine Stage-2G Hodge
statement follows. -/
theorem bigradedBettiHodge_of_transformed_spectral_extinction
    (G : GeometricCycleClassSpine V H)
    (visibility : ∀ E : OmniversalSeparatorGhost G,
      SingletonGhostSpectralVisibility G E) :
    BigradedBettiHodgeStatement V H := by
  by_contra hnot
  let E : OmniversalSeparatorGhost G :=
    Classical.choice
      ((not_hodge_iff_nonempty_omniversalSeparatorGhost G).mp hnot)
  exact ghost_false_of_singleton_spectral_visibility G E (visibility E)

/-- Exact contrapositive of the transformed problem: a genuine Hodge failure
produces an omniversal GST ghost whose detected sheet is invisible to every
verified singleton spectral chart.  This is the remaining frontier expressed
purely in the transformed cosmology. -/
theorem failure_yields_spectrally_invisible_ghost
    (G : GeometricCycleClassSpine V H)
    (hnot : ¬ BigradedBettiHodgeStatement V H) :
    ∃ E : OmniversalSeparatorGhost G,
      IsEmpty (SingletonGhostSpectralVisibility G E) := by
  let E : OmniversalSeparatorGhost G :=
    Classical.choice
      ((not_hodge_iff_nonempty_omniversalSeparatorGhost G).mp hnot)
  refine ⟨E, ?_⟩
  exact ⟨fun W => ghost_false_of_singleton_spectral_visibility G E W⟩

#check SingletonGhostSpectralVisibility
#check singleton_visibility_all
#check ghost_false_of_singleton_spectral_visibility
#check bigradedBettiHodge_of_transformed_spectral_extinction
#check failure_yields_spectrally_invisible_ghost

#print axioms singleton_visibility_all
#print axioms ghost_false_of_singleton_spectral_visibility
#print axioms bigradedBettiHodge_of_transformed_spectral_extinction
#print axioms failure_yields_spectrally_invisible_ghost

end GSTClassicalHodgeTransformedCosmologyGhostExtinction
