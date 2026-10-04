import GSTClassicalHodgeFiniteClosedCorrespondenceOperator
import GSTClassicalHodgeCycleOperatorNaturality

/-!
# GST CLASSICAL HODGE — RATIONAL CORRESPONDENCE OPERATOR SYNTHESIS

The correct algebraic correspondence carrier is rational-linear.  This file
shows that exact cycle-class-natural operator pairs are closed under rational
linear synthesis and then applies that closure to finite rational combinations
of genuine one-sided finite closed correspondences.

No new geometric realization equation is assumed for the sum.  Each primitive
correspondence K must independently realize its own cohomological operator on
point cycles.  The global rational correspondence operator is then derived by
linearity from the already-proved pointwise-to-full naturality theorem.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeRationalCorrespondenceOperatorSynthesis

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeCycleOperatorNaturality
open GSTClassicalHodgeFiniteClosedCorrespondence
open GSTClassicalHodgeFiniteClosedCorrespondenceOperator

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

abbrev Pair := CycleClassOperatorPair V H p

namespace Pair

/-- Zero natural operator pair. -/
noncomputable def zero : Pair (V := V) (H := H) (p := p) where
  cycleOperator := 0
  cohomologyOperator := 0
  cycleClass_natural := by ext Z; simp

/-- Sum of two exact natural operator pairs. -/
noncomputable def add
    (A B : Pair (V := V) (H := H) (p := p)) :
    Pair (V := V) (H := H) (p := p) where
  cycleOperator := A.cycleOperator + B.cycleOperator
  cohomologyOperator := A.cohomologyOperator + B.cohomologyOperator
  cycleClass_natural := by
    ext Z
    simp [A.cycleClass_cycleOperator, B.cycleClass_cycleOperator]

/-- Rational scaling of an exact natural operator pair. -/
noncomputable def smul
    (q : ℚ)
    (A : Pair (V := V) (H := H) (p := p)) :
    Pair (V := V) (H := H) (p := p) where
  cycleOperator := q • A.cycleOperator
  cohomologyOperator := q • A.cohomologyOperator
  cycleClass_natural := by
    ext Z
    simp [A.cycleClass_cycleOperator]

@[simp] theorem zero_cycleOperator :
    (zero (V := V) (H := H) (p := p)).cycleOperator = 0 := rfl

@[simp] theorem zero_cohomologyOperator :
    (zero (V := V) (H := H) (p := p)).cohomologyOperator = 0 := rfl

@[simp] theorem add_cycleOperator
    (A B : Pair (V := V) (H := H) (p := p)) :
    (add A B).cycleOperator = A.cycleOperator + B.cycleOperator := rfl

@[simp] theorem add_cohomologyOperator
    (A B : Pair (V := V) (H := H) (p := p)) :
    (add A B).cohomologyOperator = A.cohomologyOperator + B.cohomologyOperator := rfl

@[simp] theorem smul_cycleOperator
    (q : ℚ) (A : Pair (V := V) (H := H) (p := p)) :
    (smul q A).cycleOperator = q • A.cycleOperator := rfl

@[simp] theorem smul_cohomologyOperator
    (q : ℚ) (A : Pair (V := V) (H := H) (p := p)) :
    (smul q A).cohomologyOperator = q • A.cohomologyOperator := rfl

end Pair

/-- Exact operator pair carried by one genuine one-sided finite closed
correspondence and its independently verified pointwise Betti realization. -/
noncomputable def primitivePair
    (K : FiniteClosedCorrespondence V)
    (T : RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
      RationalSingularCohomology H.analytification (2 * p))
    (hT : K.RealizesAmbientOnPoints (H := H) T) :
    Pair (V := V) (H := H) (p := p) :=
  K.toCycleClassOperatorPair T hT

/-- Fold a finite rational correspondence cycle into one exact natural
operator pair.  The input `T` and `hT` are primitive geometric realization
proofs; naturality of the rational sum is derived. -/
noncomputable def rationalPair
    (A : RationalClosedCorrespondenceCycle V)
    (T : ∀ K : FiniteClosedCorrespondence V,
      RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
        RationalSingularCohomology H.analytification (2 * p))
    (hT : ∀ K : FiniteClosedCorrespondence V,
      K.RealizesAmbientOnPoints (H := H) (T K)) :
    Pair (V := V) (H := H) (p := p) := by
  classical
  exact A.sum fun K q => Pair.smul q (primitivePair K (T K) (hT K))

/-- Native operator of the synthesized pair is exactly the rational sum of
native correspondence operators. -/
theorem rationalPair_cycleOperator
    (A : RationalClosedCorrespondenceCycle V)
    (T : ∀ K : FiniteClosedCorrespondence V,
      RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
        RationalSingularCohomology H.analytification (2 * p))
    (hT : ∀ K : FiniteClosedCorrespondence V,
      K.RealizesAmbientOnPoints (H := H) (T K)) :
    (rationalPair A T hT).cycleOperator =
      correspondenceCycleNativeOperator A p := by
  classical
  induction A using Finsupp.induction with
  | zero => simp [rationalPair, correspondenceCycleNativeOperator, Pair.zero]
  | add_one K q A hK ih =>
      simp [rationalPair, correspondenceCycleNativeOperator,
        primitivePair, Pair.add, Pair.smul, ih, hK]

/-- The cohomological action is the matching rational sum of the independently
realized primitive correspondence actions. -/
theorem rationalPair_cohomologyOperator
    (A : RationalClosedCorrespondenceCycle V)
    (T : ∀ K : FiniteClosedCorrespondence V,
      RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
        RationalSingularCohomology H.analytification (2 * p))
    (hT : ∀ K : FiniteClosedCorrespondence V,
      K.RealizesAmbientOnPoints (H := H) (T K)) :
    (rationalPair A T hT).cohomologyOperator =
      A.sum (fun K q => q • T K) := by
  classical
  induction A using Finsupp.induction with
  | zero => simp [rationalPair, Pair.zero]
  | add_one K q A hK ih =>
      simp [rationalPair, primitivePair, Pair.add, Pair.smul, ih, hK]

/-- Direct naturality formula for the synthesized rational correspondence
cycle. -/
theorem rational_cycleClass_natural
    (A : RationalClosedCorrespondenceCycle V)
    (T : ∀ K : FiniteClosedCorrespondence V,
      RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
        RationalSingularCohomology H.analytification (2 * p))
    (hT : ∀ K : FiniteClosedCorrespondence V,
      K.RealizesAmbientOnPoints (H := H) (T K))
    (Z : codimensionCycles V.X p) :
    H.cycleClass p (correspondenceCycleNativeOperator A p Z) =
      (A.sum (fun K q => q • T K)) (H.cycleClass p Z) := by
  let P := rationalPair A T hT
  have h := P.cycleClass_cycleOperator Z
  rw [rationalPair_cycleOperator A T hT,
    rationalPair_cohomologyOperator A T hT] at h
  exact h

#check Pair.zero
#check Pair.add
#check Pair.smul
#check primitivePair
#check rationalPair
#check rationalPair_cycleOperator
#check rationalPair_cohomologyOperator
#check rational_cycleClass_natural

#print axioms rational_cycleClass_natural

end GSTClassicalHodgeRationalCorrespondenceOperatorSynthesis
