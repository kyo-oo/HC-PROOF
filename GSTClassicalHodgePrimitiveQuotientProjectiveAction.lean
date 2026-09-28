import GSTClassicalHodgePrimitiveQuotientLimitlessBridge
import GSTClassicalHodgeProjectiveWordOrbit

/-!
# GST CLASSICAL HODGE — PROJECTIVE ACTION ON THE PRIMITIVE QUOTIENT

The primitive geometric quotient divides target-weight cohomology by every
verified image arriving from a strictly lower Hodge weight.  That lower image
is automatically stable under every genuine same-weight projective word:
postcomposing a lower-weight graded program with a horizontal projective word
is still a lower-weight graded program.

Therefore the full independently verified projective-word algebra descends to
the primitive quotient.  This does not assume any abstract Hodge matrix unit or
basis-localization naturality.  The descended operators are exactly those built
from actual scheme endomorphisms by finite addition, rational scaling and
noncommutative composition.
-/

set_option maxHeartbeats 90000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgePrimitiveQuotientProjectiveAction

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeGradedGeometricProgramOrbit
open GSTClassicalHodgeProjectiveWordOrbit
open GSTClassicalHodgePrimitiveGeometricQuotient

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Every genuine same-weight projective word preserves the submodule generated
by all lower-weight verified geometric images. -/
theorem lowerGeometricImage_stable_projectiveWord
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (W : ProjectiveOperatorWord V p) :
    lowerGeometricImage G p ≤
      (lowerGeometricImage G p).comap (W.operatorPair G).cohomologyOperator := by
  apply Submodule.span_le.mpr
  intro y hy
  rcases hy with ⟨q, hq, P, alpha, rfl⟩
  change (W.operatorPair G).cohomologyOperator
      (P.cohomologyEval G alpha.1) ∈ lowerGeometricImage G p
  apply Submodule.subset_span
  refine ⟨q, hq, .comp P (.word W), alpha, ?_⟩
  rfl

/-- The ambient cohomological action of one genuine projective word therefore
induces a canonical linear endomorphism of the primitive geometric quotient. -/
noncomputable def primitiveProjectiveAction
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (W : ProjectiveOperatorWord V p) :
    PrimitiveGeometricQuotient G p →ₗ[ℚ]
      PrimitiveGeometricQuotient G p :=
  (lowerGeometricImage G p).mapQ
    (W.operatorPair G).cohomologyOperator
    (lowerGeometricImage_stable_projectiveWord G p W)

/-- The descended quotient action agrees exactly with the ambient projective
word on representatives. -/
theorem primitiveProjectiveAction_mk
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (W : ProjectiveOperatorWord V p)
    (x : RationalSingularCohomology H.analytification (2 * p)) :
    primitiveProjectiveAction G p W (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ((W.operatorPair G).cohomologyOperator x) := by
  rfl

/-- Identity projective word descends to the identity on the primitive
quotient. -/
theorem primitiveProjectiveAction_id
    (G : GeometricCycleClassSpine V H)
    (p : Nat) :
    primitiveProjectiveAction G p (.id) = LinearMap.id := by
  apply LinearMap.quotient_ext
  intro x
  rfl

/-- Addition of projective words descends to addition of quotient operators. -/
theorem primitiveProjectiveAction_add
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (A B : ProjectiveOperatorWord V p) :
    primitiveProjectiveAction G p (.add A B) =
      primitiveProjectiveAction G p A + primitiveProjectiveAction G p B := by
  apply LinearMap.quotient_ext
  intro x
  rfl

/-- Rational scaling of words descends to rational scaling on the quotient. -/
theorem primitiveProjectiveAction_smul
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (q : ℚ)
    (A : ProjectiveOperatorWord V p) :
    primitiveProjectiveAction G p (.smul q A) =
      q • primitiveProjectiveAction G p A := by
  apply LinearMap.quotient_ext
  intro x
  rfl

/-- Noncommutative word composition remains noncommutative composition after
passing to the primitive quotient. -/
theorem primitiveProjectiveAction_comp
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (A B : ProjectiveOperatorWord V p) :
    primitiveProjectiveAction G p (.comp A B) =
      (primitiveProjectiveAction G p A).comp
        (primitiveProjectiveAction G p B) := by
  apply LinearMap.quotient_ext
  intro x
  rfl

/-- **PRIMITIVE PROJECTIVE-ACTION CROWN.**
The quotient by all lower-weight verified geometry still carries the complete
genuine projective-word algebra. -/
theorem primitive_projective_action_crown
    (G : GeometricCycleClassSpine V H)
    (p : Nat) :
    (∀ W : ProjectiveOperatorWord V p,
      lowerGeometricImage G p ≤
        (lowerGeometricImage G p).comap
          (W.operatorPair G).cohomologyOperator)
    ∧ primitiveProjectiveAction G p (.id) = LinearMap.id := by
  exact ⟨lowerGeometricImage_stable_projectiveWord G p,
    primitiveProjectiveAction_id G p⟩

#check lowerGeometricImage_stable_projectiveWord
#check primitiveProjectiveAction
#check primitiveProjectiveAction_mk
#check primitiveProjectiveAction_id
#check primitiveProjectiveAction_add
#check primitiveProjectiveAction_smul
#check primitiveProjectiveAction_comp
#check primitive_projective_action_crown

#print axioms lowerGeometricImage_stable_projectiveWord
#print axioms primitiveProjectiveAction_mk
#print axioms primitiveProjectiveAction_comp
#print axioms primitive_projective_action_crown

end GSTClassicalHodgePrimitiveQuotientProjectiveAction
