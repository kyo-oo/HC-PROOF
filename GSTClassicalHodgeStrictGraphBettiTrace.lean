import GSTClassicalHodgeStrictGraphCorrespondence
import GSTClassicalHodgeStrictCorrespondenceBettiTracePushPull

/-!
# GST CLASSICAL HODGE — TRANSPOSED GRAPH BETTI TRACE WITHOUT A TRACE AXIOM

For the transpose of a finite graph correspondence, the right algebraic leg is
literally the identity.  Its intrinsic analytic carrier is therefore the graph
locus `(f(x),x)`.  Projection to the second coordinate has a canonical
continuous section obtained from analytification of `f`.

Pullback along that section is an exact left inverse to right pullback on
rational singular cohomology.  Hence the degree-one `RightFiniteBettiTrace`
used by the strict-relation compiler is constructed rather than supplied.

No Hodge class, target state, cycle-class surjectivity, or desired operator
action occurs in the construction.
-/

set_option maxHeartbeats 180000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicTopology

namespace GSTClassicalHodgeStrictGraphBettiTrace

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTClassicalHodgeAnalytificationFunctoriality
open GSTClassicalHodgeSingularCohomologyFunctoriality
open GSTClassicalHodgeStrictGraphCorrespondence
open GSTClassicalHodgeStrictCorrespondenceAnalyticSpan
open GSTClassicalHodgeStrictCorrespondenceBettiTracePushPull

variable {V : SmoothProjectiveComplexScheme}
variable (A : AnalytificationData V)

/-- A genuine complex point of `X` canonically determines a carrier point of
the transposed graph. -/
noncomputable def transposeGraphCarrierPoint
    (f : ComplexSchemeEndomorphism V)
    (hf : IsFinite f.hom)
    (x : ComplexPoint V) :
    CarrierComplexPoint ((strictGraph f hf).transpose) := by
  refine ⟨x.1, ?_⟩
  calc
    (x.1 ≫ ((strictGraph f hf).transpose.toSchemeFiniteClosedCorrespondence.left)) ≫
        V.structureMap =
      (x.1 ≫ f.hom) ≫ V.structureMap := by
        rw [strictGraph_transpose_left]
    _ = x.1 ≫ (f.hom ≫ V.structureMap) := by simp [Category.assoc]
    _ = x.1 ≫ V.structureMap := by rw [f.over_base]
    _ = 𝟙 complexBase := x.2

/-- The intrinsic analytic point of the transposed graph is exactly
`(f^an(x),x)`. -/
theorem transposeGraphCarrierPoint_pair
    (f : ComplexSchemeEndomorphism V)
    (hf : IsFinite f.hom)
    (x : ComplexPoint V) :
    carrierPointPair A ((strictGraph f hf).transpose)
        (transposeGraphCarrierPoint f hf x) =
      (A.pointsEquiv (ComplexSchemeEndomorphism.complexPointMap f x),
        A.pointsEquiv x) := by
  ext
  · apply A.pointsEquiv.injective
    apply Subtype.ext
    simp [carrierPointPair, leftComplexPoint, transposeGraphCarrierPoint,
      strictGraph_transpose_left,
      ComplexSchemeEndomorphism.complexPointMap]
  · apply A.pointsEquiv.injective
    apply Subtype.ext
    simp [carrierPointPair, rightComplexPoint, transposeGraphCarrierPoint,
      strictGraph_transpose_right]

/-- Canonical section of the analytic right projection of a transposed finite
graph.  Continuity is exactly the morphism-level analytification law already
present in the GST geometry. -/
noncomputable def transposeGraphAnalyticSection
    (F : AnalyticEndomorphism A)
    (hf : IsFinite F.algebraic.hom) :
    A.space ⟶ analyticCarrier A ((strictGraph F.algebraic hf).transpose) := by
  let s : A.space → analyticCarrier A ((strictGraph F.algebraic hf).transpose) :=
    fun x => ⟨(transportedPointMap A F.algebraic x, x), by
      let z := transposeGraphCarrierPoint F.algebraic hf (A.pointsEquiv.symm x)
      refine ⟨z, ?_⟩
      have hz := transposeGraphCarrierPoint_pair A F.algebraic hf
        (A.pointsEquiv.symm x)
      simpa [transportedPointMap] using hz⟩
  refine ConcreteCategory.ofHom (C := TopCat)
    ⟨s, ?_⟩
  apply continuous_induced_rng.2
  exact F.continuous_toFun.prod_mk continuous_id

/-- The right projection followed after the canonical graph section is
literally identity. -/
@[simp]
theorem transposeGraphAnalyticSection_right
    (F : AnalyticEndomorphism A)
    (hf : IsFinite F.algebraic.hom) :
    transposeGraphAnalyticSection A F hf ≫
      analyticRight A ((strictGraph F.algebraic hf).transpose) = 𝟙 A.space := by
  apply TopCat.ext
  intro x
  rfl

/-- Covariant singular-chain map of the canonical graph section. -/
noncomputable def transposeGraphSectionChainMap
    (F : AnalyticEndomorphism A)
    (hf : IsFinite F.algebraic.hom) :
    rationalSingularChains A ⟶
      carrierSingularChains A ((strictGraph F.algebraic hf).transpose) :=
  ((singularChainComplexFunctor (ModuleCat ℚ)).obj rationalCoefficient).map
    (transposeGraphAnalyticSection A F hf)

/-- Contravariant cochain pullback along the canonical graph section. -/
noncomputable def transposeGraphSectionCochainPullback
    (F : AnalyticEndomorphism A)
    (hf : IsFinite F.algebraic.hom) :
    carrierSingularCochains A ((strictGraph F.algebraic hf).transpose) ⟶
      rationalSingularCochains A := by
  let D :=
    ((CategoryTheory.linearYoneda ℚ (ModuleCat ℚ)).obj rationalCoefficient).rightOp
      |>.mapHomologicalComplex (ComplexShape.down ℕ)
  exact (D.map (transposeGraphSectionChainMap A F hf)).unop

/-- The section-induced map on carrier cohomology. -/
noncomputable def transposeGraphSectionCohomologyPullback
    (F : AnalyticEndomorphism A)
    (hf : IsFinite F.algebraic.hom)
    (n : Nat) :
    CarrierCohomology A ((strictGraph F.algebraic hf).transpose) n →ₗ[ℚ]
      RationalSingularCohomology A n :=
  (HomologicalComplex.homologyMap
    (transposeGraphSectionCochainPullback A F hf) n).hom

/-- At chain level, section followed by the right projection is identity. -/
theorem transposeGraphSectionChainMap_right
    (F : AnalyticEndomorphism A)
    (hf : IsFinite F.algebraic.hom) :
    transposeGraphSectionChainMap A F hf ≫
      rightChainMap A ((strictGraph F.algebraic hf).transpose) =
        𝟙 (rationalSingularChains A) := by
  simp [transposeGraphSectionChainMap, rightChainMap,
    transposeGraphAnalyticSection_right]

/-- Contravariance turns the preceding retraction into a cochain retraction. -/
theorem rightCochainPullback_transposeGraphSection
    (F : AnalyticEndomorphism A)
    (hf : IsFinite F.algebraic.hom) :
    rightCochainPullback A ((strictGraph F.algebraic hf).transpose) ≫
      transposeGraphSectionCochainPullback A F hf =
        𝟙 (rationalSingularCochains A) := by
  simp [rightCochainPullback, transposeGraphSectionCochainPullback,
    transposeGraphSectionChainMap_right]

/-- **GRAPH-RETRACTION COHOMOLOGY LAW.**
Pullback along the canonical section is an exact left inverse of the right
cohomology pullback. -/
theorem transposeGraphSectionCohomologyPullback_right
    (F : AnalyticEndomorphism A)
    (hf : IsFinite F.algebraic.hom)
    (n : Nat) :
    (transposeGraphSectionCohomologyPullback A F hf n).comp
      (rightCohomologyPullback A ((strictGraph F.algebraic hf).transpose) n) =
        LinearMap.id := by
  ext alpha
  unfold transposeGraphSectionCohomologyPullback rightCohomologyPullback
    rightCohomologyPullbackObj
  have hcochain := rightCochainPullback_transposeGraphSection A F hf
  have hhom := congrArg (fun q => HomologicalComplex.homologyMap q n) hcochain
  simpa [HomologicalComplex.homologyMap_comp] using congrArg ModuleCat.Hom.hom hhom

/-- **DEGREE-ONE TRACE FROM STRICT GRAPH GEOMETRY.**
The finite right trace of a transposed graph is no longer an input. -/
noncomputable def transposedStrictGraphRightTrace
    (F : AnalyticEndomorphism A)
    (hf : IsFinite F.algebraic.hom)
    (n : Nat) :
    RightFiniteBettiTrace A ((strictGraph F.algebraic hf).transpose) n where
  trace := transposeGraphSectionCohomologyPullback A F hf n
  degree := 1
  degree_ne_zero := one_ne_zero
  trace_rightPullback := by
    simpa using transposeGraphSectionCohomologyPullback_right A F hf n

/-- The normalized trace is definitionally the graph-section pullback because
the constructed finite degree is one. -/
theorem transposedStrictGraph_normalizedTrace_eq_section
    (F : AnalyticEndomorphism A)
    (hf : IsFinite F.algebraic.hom)
    (n : Nat) :
    (transposedStrictGraphRightTrace A F hf n).normalizedTrace =
      transposeGraphSectionCohomologyPullback A F hf n := by
  ext alpha
  simp [transposedStrictGraphRightTrace,
    RightFiniteBettiTrace.normalizedTrace]

/-- Consequently the transposed graph right pullback is injective with no
separate trace/injectivity hypothesis. -/
theorem transposedStrictGraph_rightPullback_injective
    (F : AnalyticEndomorphism A)
    (hf : IsFinite F.algebraic.hom)
    (n : Nat) :
    Function.Injective
      (rightCohomologyPullback A ((strictGraph F.algebraic hf).transpose) n) :=
  (transposedStrictGraphRightTrace A F hf n).rightPullback_injective

#check transposeGraphAnalyticSection
#check transposeGraphAnalyticSection_right
#check transposeGraphSectionCohomologyPullback_right
#check transposedStrictGraphRightTrace
#check transposedStrictGraph_rightPullback_injective

#print axioms transposeGraphAnalyticSection_right
#print axioms transposeGraphSectionCohomologyPullback_right
#print axioms transposedStrictGraphRightTrace
#print axioms transposedStrictGraph_rightPullback_injective

end GSTClassicalHodgeStrictGraphBettiTrace
