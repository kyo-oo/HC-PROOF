import GSTClassicalHodgeVerticalRayProjectiveApexFinale
import GSTClassicalHodgeStrictCorrespondenceBettiTracePushPull
import GSTClassicalHodgeRealizedCorrespondenceExpressionAlgebra

/-!
# GST CLASSICAL HODGE — STRICT BETTI / APEX L² FUSION

The omniverse apex finale asks only for a realized correspondence expression
whose action on one genuine algebraic apex agrees with the localized two-slot
`L²` firing toward a requested Hodge basis sheet.

For a strict scheme-bi-finite correspondence there is a more intrinsic way to
state that source action.  Its analytification gives the pullback relation

  l^*(alpha) = r^*(beta).

A nonzero finite right trace makes `r^*` injective and constructs the total
whole-Betti push-pull operator `Tr_r ∘ l^*`.  Therefore, whenever the strict
Betti relation holds between the apex `alpha` and the localized `L²` target
`beta`, uniqueness forces the independently constructed push-pull operator to
send the apex to exactly that target.

Together with point-cycle compatibility, the same strict correspondence is an
actual realized finite closed correspondence.  Hence the historical
`source_action` equation is no longer an arbitrary cohomology-operator field:
it is derived from the intrinsic analytic-span relation of a genuine
bi-finite correspondence.
-/

set_option maxHeartbeats 180000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeStrictBettiApexL2Fusion

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeSynchronizedDefectOrbit
open GSTClassicalHodgePrimitiveArsenalRationalization
open GSTClassicalHodgeTwoSlotLefschetzCollapse
open GSTClassicalHodgeOmniverseLefschetzRayCompiler
open GSTClassicalHodgeSchemeFiniteCorrespondenceFirewall
open GSTClassicalHodgeStrictCorrespondenceAnalyticSpan
open GSTClassicalHodgeStrictCorrespondenceBettiObstruction
open GSTClassicalHodgeStrictCorrespondenceMaximalBettiTransfer
open GSTClassicalHodgeStrictCorrespondenceBettiTracePushPull
open GSTClassicalHodgeFiniteClosedCorrespondence
open GSTClassicalHodgeGradedFiniteClosedCorrespondence
open GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra
open GSTClassicalHodgeRealizedCorrespondenceExpressionAlgebra
open GSTClassicalHodgeVerticalRayProjectiveApexFinale
open GSTClassicalHodgeLiveApexSpineFanFinale
open GSTClassicalHodgeExactVerticalCutRay
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeProjectiveDegreeTrace
open GSTClassicalHodgeExactClayStatement

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- The localized two-slot `L²` target emitted by the omniverse from one apex. -/
noncomputable def apexL2Target
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (j : ClassicalHodgeBasisIndex V H p) :
    RationalSingularCohomology H.analytification (2 * p) :=
  (liftFiniteHodgeOperator (pairBasisIndex S.sourceIndex j)
    (diagonalLefschetzQ 2 2) S.hodge).1

/-- **ONE STRICT-BETTI APEX L² SPOKE.**

The geometry is a genuine scheme-bi-finite correspondence.  `trace` is the
finite right Betti trace which constructs a total whole-Betti push-pull.
`pointCompatibility` identifies that independently constructed push-pull with
the native finite-incidence action on genuine point cycles.  The only
source/target equation is the intrinsic strict analytic relation
`l^* S = r^*(L² S)`; no arbitrary ambient action equation is supplied. -/
structure StrictBettiApexL2Spoke
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p))
    (j : ClassicalHodgeBasisIndex V H p) where
  correspondence : SchemeBiFiniteClosedCorrespondence V
  trace : RightFiniteBettiTrace H.analytification correspondence (2 * p)
  pointCompatibility :
    PointCycleCompatibility (n := p) correspondence trace
  related :
    BettiRelated H.analytification correspondence (2 * p)
      S.hodge.1 (apexL2Target S j)

namespace StrictBettiApexL2Spoke

variable
  {S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p)}
  {j : ClassicalHodgeBasisIndex V H p}

/-- The intrinsic relation itself proves that the apex lies in the maximal
transferable subspace, i.e. its strict transfer obstruction vanishes. -/
theorem transferObstruction_apex_eq_zero
    (R : StrictBettiApexL2Spoke S j) :
    transferObstruction H.analytification R.correspondence (2 * p) S.hodge.1 = 0 := by
  exact
    (transferObstruction_apply_eq_zero_iff_exists_related
      H.analytification R.correspondence (2 * p) S.hodge.1).2
      ⟨apexL2Target S j, R.related⟩

/-- **STRICT RELATION FORCES THE WHOLE-BETTI SOURCE ACTION.**

The finite trace makes the right pullback injective.  Its push-pull is already
related to every transferable source, while `related` supplies the requested
localized-`L²` target.  Uniqueness of strict-relation targets therefore forces
the two targets to coincide. -/
theorem pushPull_on_apex
    (R : StrictBettiApexL2Spoke S j) :
    R.trace.pushPull S.hodge.1 = apexL2Target S j := by
  let alphaT : transferableSubspace H.analytification R.correspondence (2 * p) :=
    ⟨S.hodge.1, R.transferObstruction_apex_eq_zero⟩
  have hpush :
      BettiRelated H.analytification R.correspondence (2 * p)
        S.hodge.1 (R.trace.pushPull S.hodge.1) := by
    simpa [alphaT] using R.trace.pushPull_related_of_transferable alphaT
  exact related_target_unique
    H.analytification R.correspondence (2 * p)
    R.trace.rightPullback_injective hpush R.related

/-- The strict correspondence and its independently constructed trace push-pull
form one genuine realized finite closed correspondence. -/
noncomputable def toRealizedFiniteClosedCorrespondence
    (R : StrictBettiApexL2Spoke S j) :
    RealizedFiniteClosedCorrespondence V H p where
  geometry :=
    R.correspondence.toBiFiniteClosedCorrespondence.toFiniteClosedCorrespondence
  cohomologyOperator := R.trace.pushPull
  realizes_on_points := by
    intro x
    have hx := R.pointCompatibility.point_natural x
    simpa only [GSTClassicalHodgeFiniteClosedCorrespondence.FiniteClosedCorrespondence.gradedNativePointImage_self]
      using hx

/-- Regard the strict correspondence as an atom of the full realized
noncommutative correspondence-expression algebra. -/
noncomputable def expression
    (R : StrictBettiApexL2Spoke S j) :
    RealizedCorrespondenceExpr V H p :=
  .atom R.toRealizedFiniteClosedCorrespondence

/-- The realized atom acts on the apex by exactly the omniverse localized
`L²` firing, now as a theorem derived from the strict Betti relation. -/
theorem expression_on_apex
    (R : StrictBettiApexL2Spoke S j) :
    R.expression.cohomologyOperator S.hodge.1 =
      (liftFiniteHodgeOperator (pairBasisIndex S.sourceIndex j)
        (diagonalLefschetzQ 2 2) S.hodge).1 := by
  change R.trace.pushPull S.hodge.1 = apexL2Target S j
  exact R.pushPull_on_apex

end StrictBettiApexL2Spoke

/-- One strict-Betti spoke to every target sheet leaving the same synchronized
algebraic apex. -/
structure StrictBettiApexL2Fan
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := p)) where
  spoke : ∀ j : ClassicalHodgeBasisIndex V H p,
    StrictBettiApexL2Spoke S j

namespace StrictBettiApexL2Fan

/-- A strict-Betti fan manufactures the exact apex-localized realized `L²`
receipt consumed by the upgraded omniverse finale. -/
noncomputable def toApexLocalizedL2Realization
    (F : StrictBettiApexL2Fan
      (V := V) (H := H) (p := p) S) :
    ApexLocalizedL2Realization S := by
  intro j
  exact ⟨(F.spoke j).expression, (F.spoke j).expression_on_apex⟩

end StrictBettiApexL2Fan

/-- **VERTICAL-RAY + STRICT-BETTI OMNIVERSE FINALE.**

At every live Hodge weight, one exact vertical ray supplies the genuine
algebraic apex.  A family of actual bi-finite correspondences whose intrinsic
Betti relations realize the localized `L²` targets then discharges the entire
horizontal omniverse.  The arbitrary cohomology `source_action` interface is
absent. -/
theorem exactHodge_of_verticalRays_and_strictBettiApexL2Fans
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (vertical : ∀ q : Nat, HodgeWeightLive H q →
      ExactVerticalCutRayCertificate V q)
    (fan : ∀ q : Nat, ∀ hlive : HodgeWeightLive H q,
      StrictBettiApexL2Fan
        (canonicalCutOrbitSeed G q
          (cycleClass_projectiveCutTower_ne_zero_of_certificate
            D (vertical q hlive)))) :
    EveryHodgeClassIsRationalAlgebraic H := by
  apply exactHodge_of_verticalRays_and_apexLocalizedL2 G D vertical
  intro q hlive
  exact (fan q hlive).toApexLocalizedL2Realization

#check apexL2Target
#check StrictBettiApexL2Spoke
#check StrictBettiApexL2Spoke.transferObstruction_apex_eq_zero
#check StrictBettiApexL2Spoke.pushPull_on_apex
#check StrictBettiApexL2Spoke.toRealizedFiniteClosedCorrespondence
#check StrictBettiApexL2Spoke.expression_on_apex
#check StrictBettiApexL2Fan
#check StrictBettiApexL2Fan.toApexLocalizedL2Realization
#check exactHodge_of_verticalRays_and_strictBettiApexL2Fans

#print axioms StrictBettiApexL2Spoke.transferObstruction_apex_eq_zero
#print axioms StrictBettiApexL2Spoke.pushPull_on_apex
#print axioms StrictBettiApexL2Spoke.expression_on_apex
#print axioms exactHodge_of_verticalRays_and_strictBettiApexL2Fans

end GSTClassicalHodgeStrictBettiApexL2Fusion
