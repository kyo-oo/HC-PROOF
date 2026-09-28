import GSTClassicalHodgeGhostSpineMultiplicity
import GSTClassicalHodgeSpineNonzeroFiniteSupportOrbit
import GSTClassicalHodgeGradedGeometricOrbitAlgebra
import GSTClassicalHodgeUniversalTwoSlotSaturation

/-!
# GST CLASSICAL HODGE — CANONICAL SPINE / GHOST-SHEET COSMIC LEAK

A genuine Hodge failure has already been transformed into an omniversal
separator ghost.  Native mass simultaneously makes the canonical projective
spine nonzero at every weight.

The nonzero spine has a canonically selected live Hodge coordinate.  Apply the
single universal two-slot GST transfer word from that live coordinate directly
to the sheet detected by the ghost.  Rank-free arsenal conjugation identifies
the result with the corresponding Hodge matrix unit, hence with the nonzero
live source coefficient times the ghost basis vector.

The ghost separator therefore reads this one specific GST image nontrivially.
But every state in the genuine graded geometric-program orbit is an actual
cycle class and is annihilated by the separator.  Consequently this exact
spine-to-ghost GST transfer escapes the native orbit.

This is stronger than an abstract failure of orbit invariance: the escaping
source is the canonical geometry-built spine, the source coordinate is chosen
canonically from its finite support, and the target is exactly the sheet stored
by the omniversal ghost.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeGhostSpineCosmicLeak

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeAtomicAnnihilator
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeLimitlessSpinePropagation
open GSTClassicalHodgeSynchronizedDefectOrbit
open GSTClassicalHodgeSpineNonzeroFiniteSupportOrbit
open GSTClassicalHodgeGradedGeometricProgramOrbit
open GSTClassicalHodgeGradedGeometricOrbitAlgebra
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeUniversalTwoSlotSaturation
open GSTClassicalHodgeOmniversalSeparatorGhostCrown
open GSTClassicalHodgeExplicitArsenalGeneration
open GSTClassicalHodgeRankFreePrimitiveGeneration
open GSTClassicalHodgeAugmentedTargetWindow

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Canonical nonzero synchronized spine seed at the weight of a ghost. -/
noncomputable def ghostSpineSeed
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (E : OmniversalSeparatorGhost G) :
    NativeHodgeOrbitSeed (V := V) (H := H) (p := E.weight) :=
  spineOrbitSeedOfNonzero G E.weight
    (M.spineHodgeSeed_ne_zero G E.weight)

/-- The canonical spine source is already a state of the genuine native
program orbit. -/
theorem ghostSpineSeed_mem_orbit
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (E : OmniversalSeparatorGhost G) :
    (ghostSpineSeed G M E).hodge.1 ∈
      geometricProgramOrbitModule G E.weight := by
  simpa [ghostSpineSeed] using
    spineHodgeSeed_mem_geometricProgramOrbitModule G E.weight

/-- Exact value of the universal two-slot word from the live spine coordinate
to the ghost-detected sheet. -/
theorem ghostSpine_twoSlot_exact
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (E : OmniversalSeparatorGhost G) :
    let S := ghostSpineSeed G M E
    (liftFiniteHodgeOperator (pairBasisIndex S.sourceIndex E.sheet)
      (forwardArsenalWord sourceSlot targetSlot) S.hodge).1 =
      (classicalHodgeBasis V H E.weight).repr S.hodge S.sourceIndex •
        (classicalHodgeBasis V H E.weight E.sheet).1 := by
  dsimp only
  rw [← rankFreeMatrixUnit_eq_lifted_GST_word
    (ghostSpineSeed G M E).sourceIndex E.sheet]
  simp [hodgeMatrixUnit_apply, hodgeCoordinate]

/-- **THE CANONICAL SPINE->GHOST GST IMAGE IS DETECTED.**
The source coefficient is nonzero by construction and the target basis sheet
is detected nontrivially by the ghost separator. -/
theorem ghostSpine_twoSlot_detector_ne_zero
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (E : OmniversalSeparatorGhost G) :
    let S := ghostSpineSeed G M E
    E.separator.detector
      (liftFiniteHodgeOperator (pairBasisIndex S.sourceIndex E.sheet)
        (forwardArsenalWord sourceSlot targetSlot) S.hodge).1 ≠ 0 := by
  dsimp only
  rw [ghostSpine_twoSlot_exact G M E, LinearMap.map_smul]
  exact smul_ne_zero
    (ghostSpineSeed G M E).sourceCoefficient_ne_zero
    E.separator.detects_basis

/-- **CANONICAL COSMIC LEAK.**
The exact spine-to-ghost universal GST transfer cannot belong to the genuine
native program orbit. -/
theorem ghostSpine_twoSlot_not_mem_orbit
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (E : OmniversalSeparatorGhost G) :
    let S := ghostSpineSeed G M E
    (liftFiniteHodgeOperator (pairBasisIndex S.sourceIndex E.sheet)
      (forwardArsenalWord sourceSlot targetSlot) S.hodge).1 ∉
        geometricProgramOrbitModule G E.weight := by
  dsimp only
  intro hmem
  have hrange :
      (liftFiniteHodgeOperator
        (pairBasisIndex (ghostSpineSeed G M E).sourceIndex E.sheet)
        (forwardArsenalWord sourceSlot targetSlot)
        (ghostSpineSeed G M E).hodge).1 ∈
      LinearMap.range (H.cycleClass E.weight) :=
    geometricProgramOrbitModule_le_cycleClass_range G E.weight hmem
  have hatomic :
      (liftFiniteHodgeOperator
        (pairBasisIndex (ghostSpineSeed G M E).sourceIndex E.sheet)
        (forwardArsenalWord sourceSlot targetSlot)
        (ghostSpineSeed G M E).hodge).1 ∈
      pointCycleClassSpan E.weight (H.cycleClass E.weight) := by
    rw [← smoothProjective_cycleClass_range_eq_atomic_span V H E.weight]
    exact hrange
  have hker :
      pointCycleClassSpan E.weight (H.cycleClass E.weight) ≤
        LinearMap.ker E.separator.detector :=
    (annihilatesPointCycles_iff_atomicSpan_le_ker
      E.weight (H.cycleClass E.weight) E.separator.detector).mp
      E.separator.annihilates_atoms
  exact (ghostSpine_twoSlot_detector_ne_zero G M E) (hker hatomic)

/-- No verified graded geometric program can realize the canonical spine-to-
ghost universal GST transfer on the canonical spine source. -/
theorem no_program_realizes_ghostSpine_twoSlot
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (E : OmniversalSeparatorGhost G) :
    IsEmpty
      { P : GradedGeometricProgram V E.weight E.weight //
        P.cohomologyEval G (ghostSpineSeed G M E).hodge.1 =
          (liftFiniteHodgeOperator
            (pairBasisIndex (ghostSpineSeed G M E).sourceIndex E.sheet)
            (forwardArsenalWord sourceSlot targetSlot)
            (ghostSpineSeed G M E).hodge).1 } := by
  refine ⟨?_⟩
  rintro ⟨P, hP⟩
  have hsource := ghostSpineSeed_mem_orbit G M E
  have himage :
      P.cohomologyEval G (ghostSpineSeed G M E).hodge.1 ∈
        geometricProgramOrbitModule G E.weight :=
    program_maps_geometricProgramOrbitModule G P hsource
  rw [hP] at himage
  exact ghostSpine_twoSlot_not_mem_orbit G M E himage

/-- Exact transformed failure statement: a Stage-2G counterexample forces one
canonical, explicitly named GST transfer from a geometry-built source to be
unrealizable by the entire verified graded geometric-program algebra. -/
theorem failure_yields_canonical_spine_cosmic_leak
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (hnot : ¬ BigradedBettiHodgeStatement V H) :
    ∃ E : OmniversalSeparatorGhost G,
      IsEmpty
        { P : GradedGeometricProgram V E.weight E.weight //
          P.cohomologyEval G (ghostSpineSeed G M E).hodge.1 =
            (liftFiniteHodgeOperator
              (pairBasisIndex (ghostSpineSeed G M E).sourceIndex E.sheet)
              (forwardArsenalWord sourceSlot targetSlot)
              (ghostSpineSeed G M E).hodge).1 } := by
  rcases (not_hodge_iff_nonempty_omniversalSeparatorGhost G).mp hnot with ⟨E⟩
  exact ⟨E, no_program_realizes_ghostSpine_twoSlot G M E⟩

#check ghostSpineSeed
#check ghostSpineSeed_mem_orbit
#check ghostSpine_twoSlot_exact
#check ghostSpine_twoSlot_detector_ne_zero
#check ghostSpine_twoSlot_not_mem_orbit
#check no_program_realizes_ghostSpine_twoSlot
#check failure_yields_canonical_spine_cosmic_leak

#print axioms ghostSpine_twoSlot_exact
#print axioms ghostSpine_twoSlot_detector_ne_zero
#print axioms ghostSpine_twoSlot_not_mem_orbit
#print axioms no_program_realizes_ghostSpine_twoSlot
#print axioms failure_yields_canonical_spine_cosmic_leak

end GSTClassicalHodgeGhostSpineCosmicLeak
