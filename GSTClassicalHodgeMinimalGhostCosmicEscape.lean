import GSTClassicalHodgeLimitlessTwoSlotFailureDichotomy
import GSTClassicalHodgeLocalSeedBareLefschetzExtinction
import GSTClassicalHodgeAtomicAnnihilator

/-!
# GST CLASSICAL HODGE — MINIMAL GHOST TO LIMITLESS COSMIC ESCAPE

This module performs the requested transformation of the classical obstruction
into the native GST limitless cosmology.

A minimal primitive separator ghost together with any nonzero algebraic local
seed forces the genuine algebraic Hodge fiber at that weight to be both:

* nonzero, because the local seed lies in it and has a nonzero basis
  coordinate;
* proper, because the separator annihilates every algebraic point-cycle class
  while detecting its distinguished ghost sheet.

The established limitless two-slot failure dichotomy then leaves exactly one
possibility: an unrestricted cosmic Poincare read/write matrix unit `E_01`,
after a two-sheet recoordination, ejects an actual algebraic Hodge state from
the algebraic fiber.

Thus a seeded Hodge failure is no longer a classical missing-cycle statement.
It is a concrete limitless-cosmology escape event.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeMinimalGhostCosmicEscape

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeAtomicAnnihilator
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeConcreteFailureDichotomy
open GSTClassicalHodgeLimitlessTwoSlotFailureDichotomy
open GSTClassicalHodgeMinimalPrimitiveSeparatorGhost
open GSTClassicalHodgeLocalSeedBareLefschetzExtinction

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- The local algebraic seed makes the actual algebraic Hodge fiber nonzero. -/
theorem algebraicFiber_ne_bot_of_localSeed
    (G : GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    (S : MinimalGhostLocalSeed G M) :
    AlgebraicFiber (V := V) (H := H) (p := M.weight) ≠ ⊥ := by
  intro hbot
  have hs : S.source ∈ AlgebraicFiber (V := V) (H := H) (p := M.weight) :=
    S.source_algebraic
  rw [hbot] at hs
  have hzero : S.source = 0 := by
    simpa using hs
  apply S.sourceCoefficient_ne_zero
  rw [hzero]
  simp [hodgeCoordinate]

/-- The separator makes the actual algebraic Hodge fiber proper: if it were the
whole Hodge fiber, the detected basis sheet would be algebraic, but the
separator annihilates every algebraic state and detects that sheet nontrivially. -/
theorem algebraicFiber_ne_top_of_minimalGhost
    (G : GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G) :
    AlgebraicFiber (V := V) (H := H) (p := M.weight) ≠ ⊤ := by
  intro htop
  have hbasis :
      classicalHodgeBasis V H M.weight M.sheet ∈
        AlgebraicFiber (V := V) (H := H) (p := M.weight) := by
    rw [htop]
    trivial
  have hatomic :
      (classicalHodgeBasis V H M.weight M.sheet).1 ∈
        pointCycleClassSpan M.weight (H.cycleClass M.weight) :=
    hbasis
  have hker :
      pointCycleClassSpan M.weight (H.cycleClass M.weight) ≤
        LinearMap.ker M.separator.detector :=
    (annihilatesPointCycles_iff_atomicSpan_le_ker
      M.weight (H.cycleClass M.weight) M.separator.detector).mp
      M.separator.annihilates_atoms
  exact M.separator.detects_basis (hker hatomic)

/-- **SEEDED MINIMAL GHOST = LIMITLESS COSMIC ESCAPE.**
Once a minimal separator ghost has one nonzero algebraic source, the zero-fiber
branch of the limitless failure dichotomy is impossible.  Therefore one true
unrestricted cosmic `E_01`, after two-sheet recoordination, ejects an actual
algebraic Hodge state from the cycle-class range. -/
theorem minimalGhost_yields_limitlessCosmicEscape
    (G : GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    (S : MinimalGhostLocalSeed G M) :
    Nonempty (LimitlessCosmicEscape
      (V := V) (H := H) (p := M.weight)) := by
  have hproper :
      AlgebraicFiber (V := V) (H := H) (p := M.weight) ≠ ⊤ :=
    algebraicFiber_ne_top_of_minimalGhost G M
  have hnonzero :
      AlgebraicFiber (V := V) (H := H) (p := M.weight) ≠ ⊥ :=
    algebraicFiber_ne_bot_of_localSeed G M S
  rcases proper_algebraicFiber_zero_or_limitlessCosmicEscape
      (V := V) (H := H) (p := M.weight) hproper with hzero | hescape
  · exact False.elim (hnonzero hzero)
  · exact hescape

/-- The escape is witnessed by one and the same universal cosmic `E_01`; only
the two-sheet recoordination changes with the source and target sheets. -/
theorem minimalGhost_cosmicEscape_spelled_out
    (G : GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    (S : MinimalGhostLocalSeed G M) :
    ∃ i j : ClassicalHodgeBasisIndex V H M.weight,
    ∃ alpha : ClassicalHodgeFiber V H M.weight,
      alpha ∈ AlgebraicFiber (V := V) (H := H) (p := M.weight) ∧
      liftCosmicWindowOperator (pairBasisIndex i j)
          (rationalCosmicMatrixUnit sourceSlot.1 targetSlot.1) alpha ∉
        AlgebraicFiber (V := V) (H := H) (p := M.weight) := by
  let E := Classical.choice (minimalGhost_yields_limitlessCosmicEscape G M S)
  exact ⟨E.source, E.target, E.alpha, E.alpha_algebraic, E.escapes⟩

#check algebraicFiber_ne_bot_of_localSeed
#check algebraicFiber_ne_top_of_minimalGhost
#check minimalGhost_yields_limitlessCosmicEscape
#check minimalGhost_cosmicEscape_spelled_out

#print axioms algebraicFiber_ne_bot_of_localSeed
#print axioms algebraicFiber_ne_top_of_minimalGhost
#print axioms minimalGhost_yields_limitlessCosmicEscape
#print axioms minimalGhost_cosmicEscape_spelled_out

end GSTClassicalHodgeMinimalGhostCosmicEscape
