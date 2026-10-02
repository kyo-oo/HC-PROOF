import GSTClassicalHodgeFiniteClosedCorrespondenceOperator
import GSTClassicalHodgeGeometricCycleClassSpine
import GSTClassicalHodgeCycleOperatorNaturality

/-!
# GST CLASSICAL HODGE — REALIZED CLOSED-CORRESPONDENCE ALGEBRA

This is the geometry-first replacement for treating arbitrary finite point
presentations, or the span of graph pushforwards alone, as if they were the
full algebra of projective correspondences.

A realized finite closed correspondence consists of:

* an actual finite closed correspondence in `X × X`;
* an ambient rational cohomology endomorphism;
* a pointwise cycle-class naturality theorem for that same correspondence.

The point-generator engine upgrades this to an exact commuting square on all
native cycles.  Rational finite words in such realized correspondences then
form an honest operator algebra which preserves the actual cycle-class range
and the atomic point-cycle span by construction.

No Hodge-surjectivity statement, matrix-unit reachability assumption, or
visibility hypothesis occurs in this file.  Those are later geometric burdens;
this file only supplies the non-circular operator arena in which they must be
proved.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicGeometry

namespace GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiniteClosedCorrespondence
open GSTClassicalHodgeFiniteClosedCorrespondenceOperator
open GSTClassicalHodgeCycleOperatorNaturality
open GSTClassicalHodgeGeometricCycleClassSpine

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- A genuine finite closed correspondence together with an independently
proved ambient cohomological realization on every point-cycle generator. -/
structure RealizedFiniteClosedCorrespondence
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) where
  geometry : FiniteClosedCorrespondence V
  cohomologyOperator :
    RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
      RationalSingularCohomology H.analytification (2 * p)
  realizes_on_points :
    geometry.RealizesAmbientOnPoints (H := H) cohomologyOperator

namespace RealizedFiniteClosedCorrespondence

/-- Exact native/cohomology commuting operator pair carried by the genuine
correspondence. -/
noncomputable def operatorPair
    (R : RealizedFiniteClosedCorrespondence V H p) :
    CycleClassOperatorPair V H p :=
  R.geometry.toCycleClassOperatorPair R.cohomologyOperator R.realizes_on_points

@[simp]
theorem operatorPair_cycle
    (R : RealizedFiniteClosedCorrespondence V H p) :
    R.operatorPair.cycleOperator = R.geometry.nativeOperator p :=
  rfl

@[simp]
theorem operatorPair_cohomology
    (R : RealizedFiniteClosedCorrespondence V H p) :
    R.operatorPair.cohomologyOperator = R.cohomologyOperator :=
  rfl

/-- Exact cycle-class naturality on every native cycle. -/
theorem cycleClass_natural
    (R : RealizedFiniteClosedCorrespondence V H p)
    (Z : codimensionCycles V.X p) :
    H.cycleClass p (R.geometry.nativeOperator p Z) =
      R.cohomologyOperator (H.cycleClass p Z) := by
  simpa [operatorPair] using R.operatorPair.cycleClass_cycleOperator Z

/-- Every realized correspondence preserves the actual cycle-class range. -/
theorem cycleClass_range_stable
    (R : RealizedFiniteClosedCorrespondence V H p) :
    ∀ alpha,
      alpha ∈ LinearMap.range (H.cycleClass p) →
      R.cohomologyOperator alpha ∈ LinearMap.range (H.cycleClass p) :=
  R.operatorPair.cycleClass_range_stable

/-- Every actual scheme endomorphism graph is a realized finite closed
correspondence.  This embeds the old graph-generated algebra into the richer
closed-correspondence arena without equating the two notions. -/
noncomputable def graphRealized
    (G : GeometricCycleClassSpine V H)
    (f : GSTClassicalHodgeAnalytificationFunctoriality.ComplexSchemeEndomorphism V) :
    RealizedFiniteClosedCorrespondence V H p where
  geometry := FiniteClosedCorrespondence.graphCorrespondence f
  cohomologyOperator := (G.pushforward_naturality p f.hom).cohomologyPushforward
  realizes_on_points := by
    intro x
    rw [FiniteClosedCorrespondence.graphCorrespondence_nativePointImage_eq]
    exact (G.pushforward_naturality p f.hom).naturality
      (GSTNativeCodimensionCyclePresentation.codimensionPointCycle V.X p x)

@[simp]
theorem graphRealized_cycleOperator
    (G : GeometricCycleClassSpine V H)
    (f : GSTClassicalHodgeAnalytificationFunctoriality.ComplexSchemeEndomorphism V) :
    (graphRealized (p := p) G f).operatorPair.cycleOperator =
      GSTClassicalHodgeProjectivePointTransport.smoothProjectiveNativePushforward
        V f.hom p := by
  rw [operatorPair_cycle,
    FiniteClosedCorrespondence.graphCorrespondence_nativeOperator_eq_pushforward]

end RealizedFiniteClosedCorrespondence

/-! ## Rational finite-word algebra -/

abbrev WeightedRealizedCorrespondence
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) :=
  ℚ × RealizedFiniteClosedCorrespondence V H p

abbrev RealizedCorrespondenceWord
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) :=
  List (WeightedRealizedCorrespondence V H p)

namespace CycleClassOperatorPair

noncomputable def zero : CycleClassOperatorPair V H p where
  cycleOperator := 0
  cohomologyOperator := 0
  cycleClass_natural := by
    ext Z
    simp

noncomputable def smul
    (q : ℚ)
    (A : CycleClassOperatorPair V H p) :
    CycleClassOperatorPair V H p where
  cycleOperator := q • A.cycleOperator
  cohomologyOperator := q • A.cohomologyOperator
  cycleClass_natural := by
    ext Z
    simp [A.cycleClass_cycleOperator]

noncomputable def add
    (A B : CycleClassOperatorPair V H p) :
    CycleClassOperatorPair V H p where
  cycleOperator := A.cycleOperator + B.cycleOperator
  cohomologyOperator := A.cohomologyOperator + B.cohomologyOperator
  cycleClass_natural := by
    ext Z
    simp [A.cycleClass_cycleOperator, B.cycleClass_cycleOperator]

noncomputable def comp
    (A B : CycleClassOperatorPair V H p) :
    CycleClassOperatorPair V H p where
  cycleOperator := A.cycleOperator.comp B.cycleOperator
  cohomologyOperator := A.cohomologyOperator.comp B.cohomologyOperator
  cycleClass_natural := by
    ext Z
    simp [A.cycleClass_cycleOperator, B.cycleClass_cycleOperator]

end CycleClassOperatorPair

/-- Exact operator pair represented by a finite rational word of genuine
realized closed correspondences. -/
noncomputable def realizedWordPair :
    RealizedCorrespondenceWord V H p → CycleClassOperatorPair V H p
  | [] => CycleClassOperatorPair.zero
  | (q,R) :: W =>
      CycleClassOperatorPair.add
        (CycleClassOperatorPair.smul q R.operatorPair)
        (realizedWordPair W)

/-- Every realized word preserves the genuine cycle-class range. -/
theorem realizedWord_range_stable
    (W : RealizedCorrespondenceWord V H p) :
    ∀ alpha,
      alpha ∈ LinearMap.range (H.cycleClass p) →
      (realizedWordPair W).cohomologyOperator alpha ∈
        LinearMap.range (H.cycleClass p) :=
  (realizedWordPair W).cycleClass_range_stable

/-- Every realized word preserves the atomic point-cycle span. -/
theorem realizedWord_atomic_stable
    (W : RealizedCorrespondenceWord V H p) :
    ∀ alpha,
      alpha ∈ GSTClassicalHodgeAtomicSpan.pointCycleClassSpan p (H.cycleClass p) →
      (realizedWordPair W).cohomologyOperator alpha ∈
        GSTClassicalHodgeAtomicSpan.pointCycleClassSpan p (H.cycleClass p) :=
  (realizedWordPair W).atomicSpan_stable

/-- One realized correspondence as a one-letter rational word. -/
noncomputable def singletonWord
    (R : RealizedFiniteClosedCorrespondence V H p) :
    RealizedCorrespondenceWord V H p :=
  [(1 : ℚ), R]

/-- A one-letter word has exactly the same native operator as its underlying
realized correspondence. -/
@[simp]
theorem singletonWord_cycleOperator
    (R : RealizedFiniteClosedCorrespondence V H p) :
    (realizedWordPair (singletonWord R)).cycleOperator =
      R.geometry.nativeOperator p := by
  ext Z
  simp [singletonWord, realizedWordPair,
    CycleClassOperatorPair.add, CycleClassOperatorPair.smul,
    CycleClassOperatorPair.zero, R.operatorPair_cycle]

/-- A one-letter word has exactly the independently certified cohomological
operator of its underlying realized correspondence. -/
@[simp]
theorem singletonWord_cohomologyOperator
    (R : RealizedFiniteClosedCorrespondence V H p) :
    (realizedWordPair (singletonWord R)).cohomologyOperator =
      R.cohomologyOperator := by
  ext alpha
  simp [singletonWord, realizedWordPair,
    CycleClassOperatorPair.add, CycleClassOperatorPair.smul,
    CycleClassOperatorPair.zero, R.operatorPair_cohomology]

#check RealizedFiniteClosedCorrespondence
#check RealizedFiniteClosedCorrespondence.operatorPair
#check RealizedFiniteClosedCorrespondence.graphRealized
#check RealizedCorrespondenceWord
#check realizedWordPair
#check realizedWord_range_stable
#check realizedWord_atomic_stable
#check singletonWord
#check singletonWord_cycleOperator
#check singletonWord_cohomologyOperator

#print axioms RealizedFiniteClosedCorrespondence.cycleClass_natural
#print axioms RealizedFiniteClosedCorrespondence.graphRealized
#print axioms realizedWord_range_stable
#print axioms realizedWord_atomic_stable
#print axioms singletonWord_cycleOperator
#print axioms singletonWord_cohomologyOperator

end GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra
