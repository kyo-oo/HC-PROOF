import GSTClassicalHodgePrimitivePushforwardNaturality
import GSTClassicalHodgeGeometryFirstTwoGenerator
import GSTClassicalHodgeLimitlessTowerOrbitCrown
import GSTClassicalHodgeProjectiveSelfCorrespondences

/-!
# GST CLASSICAL HODGE — PROJECTIVE TWO-GENERATOR EXTERNALIZATION

The rank-free GST Hodge engine needs only two noncommuting primitive actions in
one ordered two-slot sector: the code observable and the two-step Lefschetz
operator.  This module removes arbitrary native operators from that interface.

A primitive is now realized by an actual algebraic endomorphism of the smooth
projective carrier.  Its native action is the genuine pushforward on algebraic
cycles.  The standard cycle-class functoriality square supplies kernel
stability automatically, and the induced ambient action is required only to
restrict to the corresponding GST primitive on the genuine Hodge fiber.

From those two actual projective transports we construct
`GeometryFirstTwoGenerator`, so all projector, Lefschetz, Poincare,
recoordination, polynomial and rank-free matrix-unit consequences already
proved in the limitless universe become available without another operator
hypothesis.
-/

set_option maxHeartbeats 70000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicGeometry

namespace GSTClassicalHodgeProjectiveTwoGeneratorExternalization

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeNativeOperatorCohomologyRealization
open GSTClassicalHodgePrimitivePushforwardNaturality
open GSTClassicalHodgeProjectivePointTransport
open GSTClassicalHodgeGeometryFirstTwoGenerator
open GSTClassicalHodgeRankFreePrimitiveGeneration
open GSTClassicalHodgeLimitlessTowerOrbitCrown

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- An actual projective endomorphism realizing one prescribed Hodge-fiber
operator.  The native operator is fixed to genuine cycle pushforward. -/
structure ProjectivePrimitiveRealization
    (T : Module.End ℚ (ClassicalHodgeFiber V H p)) where
  map : V.X ⟶ V.X
  naturality : GeometricPushforwardNaturality V H p map
  restricts_to_hodge :
    ∀ alpha : ClassicalHodgeFiber V H p,
      naturality.cohomologyPushforward alpha.1 = (T alpha).1

namespace ProjectivePrimitiveRealization

/-- Genuine native-cycle primitive induced by the projective endomorphism. -/
noncomputable def toNativeHodgePrimitive
    {T : Module.End ℚ (ClassicalHodgeFiber V H p)}
    (R : ProjectivePrimitiveRealization (V := V) (H := H) T) :
    NativeHodgePrimitive (V := V) (H := H) T where
  cycleOperator := smoothProjectiveNativePushforward V R.map p
  kernelStable := R.naturality.kernelStable
  restricts_to_hodge := by
    intro alpha
    have hcanonical :=
      ambientOperator_agrees_with_realization
        (H := H)
        (smoothProjectiveNativePushforward V R.map p)
        R.naturality.kernelStable
        R.naturality.cohomologyPushforward
        (by
          ext Z
          exact R.naturality.naturality Z)
        alpha.1
    rw [hcanonical]
    exact R.restricts_to_hodge alpha

/-- The canonical ambient action generated from the native pushforward agrees
with the supplied geometric cohomology action on the whole ambient space. -/
theorem ambient_eq_geometric
    {T : Module.End ℚ (ClassicalHodgeFiber V H p)}
    (R : ProjectivePrimitiveRealization (V := V) (H := H) T) :
    (R.toNativeHodgePrimitive).ambient =
      R.naturality.cohomologyPushforward := by
  apply LinearMap.ext
  intro alpha
  exact ambientOperator_agrees_with_realization
    (H := H)
    (smoothProjectiveNativePushforward V R.map p)
    R.naturality.kernelStable
    R.naturality.cohomologyPushforward
    (by
      ext Z
      exact R.naturality.naturality Z)
    alpha

end ProjectivePrimitiveRealization

/-- Exactly two genuine projective primitives for one ordered Hodge-basis pair. -/
structure ProjectiveTwoGenerator
    (i j : ClassicalHodgeBasisIndex V H p) where
  code : ProjectivePrimitiveRealization
    (V := V) (H := H) (twoSlotCodeHodge i j)
  lefschetz : ProjectivePrimitiveRealization
    (V := V) (H := H)
    (twoSlotHodgeOperator i j (diagonalLefschetzQ 2 2))

namespace ProjectiveTwoGenerator

/-- Projective two-generator data instantiate the already-proved
geometry-first two-generator GST machine. -/
noncomputable def toGeometryFirst
    {i j : ClassicalHodgeBasisIndex V H p}
    (R : ProjectiveTwoGenerator (V := V) (H := H) i j) :
    GeometryFirstTwoGenerator (V := V) (H := H) i j where
  code := R.code.toNativeHodgePrimitive
  lefschetz := R.lefschetz.toNativeHodgePrimitive

/-- Therefore the normalized finite GST word built from the two actual
projective maps acts as the rank-one matrix unit `i -> j` on every genuine
Hodge state. -/
theorem normalized_word_on_hodge
    {i j : ClassicalHodgeBasisIndex V H p}
    (R : ProjectiveTwoGenerator (V := V) (H := H) i j)
    (alpha : ClassicalHodgeFiber V H p) :
    (R.toGeometryFirst).ambientWord alpha.1 =
      (GSTClassicalHodgeRankFreeArsenalIrreducibility.hodgeMatrixUnit i j alpha).1 :=
  (R.toGeometryFirst).ambientWord_on_hodge alpha

end ProjectiveTwoGenerator

/-- A projective realization of the two primitive generators for every target
of the selected live source automatically provides the fixed-weight input to
the limitless synchronized orbit theorem. -/
noncomputable def projectiveTargetFamily_to_geometryFirst
    (S : GSTClassicalHodgeSynchronizedDefectOrbit.NativeHodgeOrbitSeed
      (V := V) (H := H) (p := p))
    (R : ∀ j : ClassicalHodgeBasisIndex V H p,
      ProjectiveTwoGenerator (V := V) (H := H) S.sourceIndex j) :
    ∀ j : ClassicalHodgeBasisIndex V H p,
      GeometryFirstTwoGenerator
        (V := V) (H := H) S.sourceIndex j :=
  fun j => (R j).toGeometryFirst

/-- Weight-wise projective externalization crown. -/
theorem hodge_weight_of_projective_two_generators
    (S : GSTClassicalHodgeSynchronizedDefectOrbit.NativeHodgeOrbitSeed
      (V := V) (H := H) (p := p))
    (R : ∀ j : ClassicalHodgeBasisIndex V H p,
      ProjectiveTwoGenerator (V := V) (H := H) S.sourceIndex j) :
    rationalHodgeSubspace (H.hodgeBigrading p) ≤
      LinearMap.range (H.cycleClass p) :=
  S.hodge_weight (projectiveTargetFamily_to_geometryFirst S R)

/-- **PROJECTIVE + LIMITLESS GLOBAL CROWN.**
A single projective/cosmic tower intertwining supplies all weight seeds; actual
projective realizations of the two GST primitives supply every within-weight
matrix-unit word; the exact Stage-2G Hodge statement follows. -/
theorem bigradedBettiHodge_of_projective_limitless_arsenal
    (C : ProjectiveTowerHodgeIntertwining (V := V) (H := H))
    (R : ∀ p : Nat,
      ∀ j : ClassicalHodgeBasisIndex V H p,
        ProjectiveTwoGenerator
          (V := V) (H := H) (C.orbitSeed p).sourceIndex j) :
    BigradedBettiHodgeStatement V H := by
  apply C.bigradedBettiHodge
  intro p j
  exact (R p j).toGeometryFirst

#check ProjectivePrimitiveRealization
#check ProjectivePrimitiveRealization.toNativeHodgePrimitive
#check ProjectiveTwoGenerator
#check ProjectiveTwoGenerator.toGeometryFirst
#check ProjectiveTwoGenerator.normalized_word_on_hodge
#check hodge_weight_of_projective_two_generators
#check bigradedBettiHodge_of_projective_limitless_arsenal

#print axioms ProjectivePrimitiveRealization.toNativeHodgePrimitive
#print axioms ProjectiveTwoGenerator.normalized_word_on_hodge
#print axioms hodge_weight_of_projective_two_generators
#print axioms bigradedBettiHodge_of_projective_limitless_arsenal

end GSTClassicalHodgeProjectiveTwoGeneratorExternalization
