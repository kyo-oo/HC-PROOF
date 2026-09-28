import GSTClassicalHodgeMinimalGhostCosmicEscape
import GSTClassicalHodgeLimitlessCosmicNoEscape
import GSTClassicalHodgeProjectiveTwoGeneratorExternalization

/-!
# GST CLASSICAL HODGE — SINGLE PROJECTIVE ESCAPE-PAIR COLLISION

A seeded minimal Hodge ghost has already been transformed into one concrete
limitless cosmic escape.  The no-escape theorem requires a
`GeometryFirstTwoGenerator` only for the escape's actual source/target pair.
`ProjectiveTwoGenerator` supplies exactly such a realization from two genuine
projective-native primitive transports.

Therefore the old all-pairs projective externalization interface is much
stronger than necessary for the transformed contradiction: it is enough to
realize the two GST primitives for the one pair selected by the actual cosmic
escape.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeMinimalGhostProjectiveCollision

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeMinimalPrimitiveSeparatorGhost
open GSTClassicalHodgeLocalSeedBareLefschetzExtinction
open GSTClassicalHodgeMinimalGhostCosmicEscape
open GSTClassicalHodgeLimitlessTwoSlotFailureDichotomy
open GSTClassicalHodgeLimitlessCosmicNoEscape
open GSTClassicalHodgeProjectiveTwoGeneratorExternalization

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Projective closure demanded only for whichever cosmic escape is actually
produced by the transformed minimal ghost. -/
structure MinimalGhostProjectiveEscapeClosure
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    (S : MinimalGhostLocalSeed G M) where
  realize : ∀ E : LimitlessCosmicEscape
      (V := V) (H := H) (p := M.weight),
    ProjectiveTwoGenerator
      (V := V) (H := H) E.source E.target

/-- **SINGLE PROJECTIVE ESCAPE-PAIR COLLISION.**
A seeded minimal ghost cannot coexist with genuine projective realization of
the two GST primitives for its actual limitless cosmic escape pair. -/
theorem minimalGhost_false_of_projective_escapeClosure
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    (S : MinimalGhostLocalSeed G M)
    (R : MinimalGhostProjectiveEscapeClosure G M S) : False := by
  let E : LimitlessCosmicEscape (V := V) (H := H) (p := M.weight) :=
    Classical.choice (minimalGhost_yields_limitlessCosmicEscape G M S)
  exact not_limitlessCosmicEscape_of_geometryFirst
    E ((R.realize E).toGeometryFirst)

/-- Spelled-out remaining projective interface for one escape: two genuine
projective primitive realizations, one for the GST code observable and one for
the exact two-step GST Lefschetz operator, are sufficient. -/
theorem minimalGhost_false_of_two_projective_primitives
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    (S : MinimalGhostLocalSeed G M)
    (E : LimitlessCosmicEscape (V := V) (H := H) (p := M.weight))
    (code : ProjectivePrimitiveRealization
      (V := V) (H := H)
      (GSTClassicalHodgeRankFreePrimitiveGeneration.twoSlotCodeHodge
        E.source E.target))
    (lefschetz : ProjectivePrimitiveRealization
      (V := V) (H := H)
      (GSTClassicalHodgeRankFreePrimitiveGeneration.twoSlotHodgeOperator
        E.source E.target
        (GSTClassicalHodgeFullArsenalIrreducibility.diagonalLefschetzQ 2 2))) :
    False := by
  let R : ProjectiveTwoGenerator
      (V := V) (H := H) E.source E.target := {
    code := code
    lefschetz := lefschetz
  }
  exact not_limitlessCosmicEscape_of_geometryFirst E R.toGeometryFirst

#check MinimalGhostProjectiveEscapeClosure
#check minimalGhost_false_of_projective_escapeClosure
#check minimalGhost_false_of_two_projective_primitives

#print axioms minimalGhost_false_of_projective_escapeClosure
#print axioms minimalGhost_false_of_two_projective_primitives

end GSTClassicalHodgeMinimalGhostProjectiveCollision
