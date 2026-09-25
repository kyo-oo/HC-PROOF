import GSTClassicalHodgeLimitlessTwoSlotFailureDichotomy
import GSTClassicalHodgeGeometryFirstNativeWord
import GSTClassicalHodgeSynchronizedDefectOrbit

/-!
# GST CLASSICAL HODGE — LIMITLESS COSMIC NO-ESCAPE

The unrestricted cosmic matrix unit is not a new formal operator unrelated to
the finite GST arsenal.  The two-slot observation theorem already identifies
its finite read/write action with the exact projector/Lefschetz/Poincare word,
and rank-free conjugation identifies that word with the genuine Hodge matrix
unit.

Independently, `GSTClassicalHodgeGeometryFirstNativeWord` constructs the same
word on actual native codimension-p algebraic cycles and proves an exact
cycle-class commuting square.

This file fuses those two facts.  Whenever the two GST primitives have their
genuine native realization, the limitless cosmic matrix-unit action on the
Hodge fiber is literally the cohomological face of an actual native cycle
operator.  Hence it cannot eject an algebraic Hodge class from the genuine
cycle-class range.
-/

set_option maxHeartbeats 70000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeLimitlessCosmicNoEscape

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeLimitlessTwoSlotFailureDichotomy
open GSTClassicalHodgeGeometryFirstTwoGenerator
open GSTClassicalHodgeGeometryFirstNativeWord
open GSTClassicalHodgeAtomicSpan

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- The genuine native GST word and the unrestricted cosmic matrix-unit lift
have exactly the same action on every true Hodge vector. -/
theorem nativeWord_ambient_eq_limitlessCosmic_on_hodge
    (i j : ClassicalHodgeBasisIndex V H p)
    (R : GeometryFirstTwoGenerator (V := V) (H := H) i j)
    (alpha : ClassicalHodgeFiber V H p) :
    R.ambientWord alpha.1 =
      liftCosmicWindowOperator (pairBasisIndex i j)
        (GSTClassicalHodgeLimitlessCosmicMatrixUnits.rationalCosmicMatrixUnit
          sourceSlot.1 targetSlot.1) alpha := by
  rw [R.ambientWord_on_hodge]
  rw [hodgeMatrixUnit_eq_lift_limitless_cosmic]

/-- Consequently the unrestricted cosmic matrix-unit lift sends every
algebraic Hodge vector to another actual cycle-class value whenever the one
geometry-first native GST word from `i` to `j` is available. -/
theorem limitlessCosmic_preserves_cycleClass_range_on_hodge
    (i j : ClassicalHodgeBasisIndex V H p)
    (R : GeometryFirstTwoGenerator (V := V) (H := H) i j)
    (alpha : ClassicalHodgeFiber V H p)
    (halg : alpha.1 ∈ LinearMap.range (H.cycleClass p)) :
    liftCosmicWindowOperator (pairBasisIndex i j)
        (GSTClassicalHodgeLimitlessCosmicMatrixUnits.rationalCosmicMatrixUnit
          sourceSlot.1 targetSlot.1) alpha ∈
      LinearMap.range (H.cycleClass p) := by
  rcases halg with ⟨Z, hZ⟩
  refine ⟨nativeWord R Z, ?_⟩
  rw [cycleClass_nativeWord R Z]
  rw [hZ]
  exact nativeWord_ambient_eq_limitlessCosmic_on_hodge i j R alpha

/-- Atomic-span form of the same no-escape law. -/
theorem limitlessCosmic_preserves_algebraicFiber
    (i j : ClassicalHodgeBasisIndex V H p)
    (R : GeometryFirstTwoGenerator (V := V) (H := H) i j)
    (alpha : ClassicalHodgeFiber V H p)
    (halg : alpha ∈ AlgebraicFiber (V := V) (H := H) (p := p)) :
    liftCosmicWindowOperator (pairBasisIndex i j)
        (GSTClassicalHodgeLimitlessCosmicMatrixUnits.rationalCosmicMatrixUnit
          sourceSlot.1 targetSlot.1) alpha ∈
      AlgebraicFiber (V := V) (H := H) (p := p) := by
  have hrange : alpha.1 ∈ LinearMap.range (H.cycleClass p) := by
    rw [smoothProjective_cycleClass_range_eq_atomic_span V H p]
    exact halg
  have hout := limitlessCosmic_preserves_cycleClass_range_on_hodge
    i j R alpha hrange
  rw [smoothProjective_cycleClass_range_eq_atomic_span V H p] at hout
  exact hout

/-- A limitless cosmic escape is impossible as soon as the corresponding
finite GST word has its genuine native realization. -/
theorem not_limitlessCosmicEscape_of_geometryFirst
    (E : LimitlessCosmicEscape (V := V) (H := H) (p := p))
    (R : GeometryFirstTwoGenerator
      (V := V) (H := H) E.source E.target) : False := by
  exact E.escapes
    (limitlessCosmic_preserves_algebraicFiber
      E.source E.target R E.alpha E.alpha_algebraic)

/-- If every ordered Hodge-basis pair admits the genuine native two-generator
GST realization, then the escape branch of the limitless failure dichotomy is
completely empty. -/
theorem no_limitlessCosmicEscape
    (R : ∀ i j : ClassicalHodgeBasisIndex V H p,
      GeometryFirstTwoGenerator (V := V) (H := H) i j) :
    ¬ Nonempty (LimitlessCosmicEscape (V := V) (H := H) (p := p)) := by
  rintro ⟨E⟩
  exact not_limitlessCosmicEscape_of_geometryFirst E (R E.source E.target)

/-- **LIMITLESS NO-ESCAPE SATURATION.**
Once one nonzero algebraic Hodge state exists, genuine native realization of
the single cosmic read/write action rules out the only nonzero escape branch
and forces the algebraic Hodge fiber to be the whole Hodge fiber. -/
theorem algebraicFiber_eq_top_of_geometryFirst_and_seed
    (hseed : AlgebraicFiber (V := V) (H := H) (p := p) ≠ ⊥)
    (R : ∀ i j : ClassicalHodgeBasisIndex V H p,
      GeometryFirstTwoGenerator (V := V) (H := H) i j) :
    AlgebraicFiber (V := V) (H := H) (p := p) = ⊤ := by
  by_contra htop
  rcases proper_algebraicFiber_zero_or_limitlessCosmicEscape
      (V := V) (H := H) (p := p) htop with hzero | hescape
  · exact hseed hzero
  · exact no_limitlessCosmicEscape R hescape

/-- Weight-p exact Hodge landing from one nonzero algebraic seed and the true
limitless no-escape law. -/
theorem hodge_weight_of_geometryFirst_noEscape
    (hseed : AlgebraicFiber (V := V) (H := H) (p := p) ≠ ⊥)
    (R : ∀ i j : ClassicalHodgeBasisIndex V H p,
      GeometryFirstTwoGenerator (V := V) (H := H) i j) :
    rationalHodgeSubspace (H.hodgeBigrading p) ≤
      LinearMap.range (H.cycleClass p) := by
  have htop := algebraicFiber_eq_top_of_geometryFirst_and_seed hseed R
  intro alpha halpha
  let alphaH : ClassicalHodgeFiber V H p := ⟨alpha, halpha⟩
  have halg : alphaH ∈ AlgebraicFiber (V := V) (H := H) (p := p) := by
    rw [htop]
    trivial
  rw [smoothProjective_cycleClass_range_eq_atomic_span V H p]
  exact halg

#check nativeWord_ambient_eq_limitlessCosmic_on_hodge
#check limitlessCosmic_preserves_cycleClass_range_on_hodge
#check limitlessCosmic_preserves_algebraicFiber
#check not_limitlessCosmicEscape_of_geometryFirst
#check no_limitlessCosmicEscape
#check algebraicFiber_eq_top_of_geometryFirst_and_seed
#check hodge_weight_of_geometryFirst_noEscape

#print axioms limitlessCosmic_preserves_cycleClass_range_on_hodge
#print axioms not_limitlessCosmicEscape_of_geometryFirst
#print axioms algebraicFiber_eq_top_of_geometryFirst_and_seed
#print axioms hodge_weight_of_geometryFirst_noEscape

end GSTClassicalHodgeLimitlessCosmicNoEscape
