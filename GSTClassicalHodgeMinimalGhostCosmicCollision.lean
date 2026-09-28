import GSTClassicalHodgeMinimalGhostCosmicEscape
import GSTClassicalHodgeLimitlessCosmicNoEscape

/-!
# GST CLASSICAL HODGE — MINIMAL GHOST / COSMIC NO-ESCAPE COLLISION

The preceding transformation sends every seeded minimal primitive Hodge ghost
to one concrete unrestricted cosmic `E_01` escape after a two-sheet
recoordination.  The limitless no-escape theorem independently proves that such
an escape is impossible whenever the two native geometry-first GST primitives
exist for that exact source/target pair.

This file fuses the two statements.  Importantly, it does NOT request native
realization for every ordered Hodge-basis pair.  A hypothetical failure chooses
one actual escape, and only the geometry-first realization for that one pair is
needed to kill it.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeMinimalGhostCosmicCollision

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeMinimalPrimitiveSeparatorGhost
open GSTClassicalHodgeLocalSeedBareLefschetzExtinction
open GSTClassicalHodgeMinimalGhostCosmicEscape
open GSTClassicalHodgeLimitlessTwoSlotFailureDichotomy
open GSTClassicalHodgeGeometryFirstTwoGenerator
open GSTClassicalHodgeLimitlessCosmicNoEscape

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Exact one-escape native closure demanded after the full classical problem
has been transformed into the limitless GST cosmology. -/
structure MinimalGhostEscapeClosure
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    (S : MinimalGhostLocalSeed G M) where
  realize : ∀ E : LimitlessCosmicEscape
      (V := V) (H := H) (p := M.weight),
    GeometryFirstTwoGenerator
      (V := V) (H := H) E.source E.target

/-- **TRANSFORMED COSMIC COLLISION.**
A seeded minimal ghost and native realization of the single cosmic escape pair
are incompatible. -/
theorem minimalGhost_false_of_escapeClosure
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    (S : MinimalGhostLocalSeed G M)
    (R : MinimalGhostEscapeClosure G M S) : False := by
  let E : LimitlessCosmicEscape (V := V) (H := H) (p := M.weight) :=
    Classical.choice (minimalGhost_yields_limitlessCosmicEscape G M S)
  exact not_limitlessCosmicEscape_of_geometryFirst E (R.realize E)

/-- Equivalent single-witness form: after choosing the actual escape produced
by the transformed failure, only its exact geometry-first realization is
needed. -/
theorem minimalGhost_false_of_chosen_escape_realization
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    (S : MinimalGhostLocalSeed G M)
    (E : LimitlessCosmicEscape (V := V) (H := H) (p := M.weight))
    (hE : E ∈ Set.range
      (fun _ : Unit =>
        Classical.choice (minimalGhost_yields_limitlessCosmicEscape G M S)))
    (R : GeometryFirstTwoGenerator
      (V := V) (H := H) E.source E.target) : False := by
  exact not_limitlessCosmicEscape_of_geometryFirst E R

#check MinimalGhostEscapeClosure
#check minimalGhost_false_of_escapeClosure
#check minimalGhost_false_of_chosen_escape_realization

#print axioms minimalGhost_false_of_escapeClosure
#print axioms minimalGhost_false_of_chosen_escape_realization

end GSTClassicalHodgeMinimalGhostCosmicCollision
