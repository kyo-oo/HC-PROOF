import GSTClassicalHodgeOmniverseTwoSlotLefschetzBranch
import GSTClassicalHodgePiOmniverseBranchSynthesis
import GSTClassicalHodgeDiagonalIdentityCorrespondence

/-!
# GST CLASSICAL HODGE — OMNIVERSE LEFSCHETZ RAY COMPILER

A primitive branch arrow in the handwritten GST omniverse is already proved to
be a normalized localized two-slot `L^2` firing.  Therefore it is unnecessary
to geometrically materialize every matrix unit or every graph edge separately.

This file isolates the strictly smaller geometric burden: realize the BARE
localized `L^2` operator on each ordered two-slot Hodge chart by one expression
in genuine closed correspondences.  Rational scaling in the realized
correspondence algebra then supplies the universal inverse normalization.

The graph ontology contributes the second compression.  A long causal ray is
not a new primitive operator; it is a finite `OmniversalGraph.Path`.  Genuine
correspondence expressions are closed under noncommutative composition, so an
entire ray compiles to one realized expression.  The empty path is materialized
by the actual diagonal graph correspondence, not by an inserted formal
identity.

Thus one local geometric primitive propagates through the full GST Graph V2
causal closure:

  localized L^2 geometry
      -> every primitive branch event
      -> every finite causal ray
      -> every event-generated closure node.

Higher-arity branch synthesis remains handled by the already-proved omniverse
semantic-stability theorem once the primitive compiler has been manufactured.
No Hodge-surjectivity conclusion is assumed here.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeOmniverseLefschetzRayCompiler

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgePrimitiveArsenalRationalization
open GSTClassicalHodgeTwoSlotLefschetzCollapse
open GSTClassicalHodgeOmniverseCausalBranchPacket
open GSTClassicalHodgeOmniverseTwoSlotLefschetzBranch
open GSTClassicalHodgePiOmniverseBranchSynthesis
open GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra
open GSTClassicalHodgeRealizedCorrespondenceExpressionAlgebra
open GSTClassicalHodgeDiagonalIdentityCorrespondence
open GSTGraphV2OmniversalCore
open GSTGraphV2OmniversalHyperEvents

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- The only primitive geometry required by the new graph route.

For every ordered Hodge-basis pair `(i,j)`, one expression in ACTUAL realized
closed correspondences agrees, on every genuine Hodge-fiber state, with the
bare localized two-step Lefschetz operator on the corresponding two-slot
chart.  No projector or matrix-unit realization is supplied independently. -/
def LocalizedL2PrimitiveRealization : Prop :=
  forall i j : ClassicalHodgeBasisIndex V H p,
    exists E : RealizedCorrespondenceExpr V H p,
      forall alpha : ClassicalHodgeFiber V H p,
        E.cohomologyOperator alpha.1 =
          (liftFiniteHodgeOperator (pairBasisIndex i j)
            (diagonalLefschetzQ 2 2) alpha).1

/-- Bare localized `L^2` geometry automatically materializes EVERY primitive
omniverse branch edge.  The only extra operation is multiplication by the
already-proved nonzero universal inverse scalar. -/
theorem primitiveBranchCompiler_of_localizedL2
    (C : LocalizedL2PrimitiveRealization (V := V) (H := H) (p := p)) :
    PrimitiveBranchCompiler (V := V) (H := H) (p := p) := by
  intro u v huv
  obtain ⟨j, i, htarget⟩ :=
    event_target_eq_normalized_localized_L2
      (V := V) (H := H) (p := p) huv
  obtain ⟨E, hE⟩ := C i.1 j
  refine ⟨.smul (twoSlotScalar)⁻¹ E, ?_⟩
  unfold ExprMaterializesBranch
  change v.state.1 =
    (twoSlotScalar)⁻¹ • E.cohomologyOperator u.state.1
  rw [hE u.state]
  simpa using congrArg Subtype.val htarget

/-- The genuine diagonal graph correspondence materializes the zero-length
causal ray. -/
theorem diagonal_materializes_reflexive_branch
    (u : HodgeBranchNode (V := V) (H := H) (p := p)) :
    ExprMaterializesBranch
      (.atom (diagonalRealized (V := V) (H := H) (p := p))) u u := by
  unfold ExprMaterializesBranch
  change u.state.1 =
    (diagonalRealized (V := V) (H := H) (p := p)).cohomologyOperator u.state.1
  rw [diagonalRealized_cohomologyOperator]
  rfl

/-- **CAUSAL-RAY COMPILER.**
Every finite GST Graph V2 causal path is one genuine noncommutative expression
of realized closed correspondences.  Long diagonal rays therefore introduce
no new geometric primitive beyond the one-step localized `L^2` realization. -/
theorem causalPath_has_realized_expression
    (C : LocalizedL2PrimitiveRealization (V := V) (H := H) (p := p))
    {u v : HodgeBranchNode (V := V) (H := H) (p := p)}
    (gamma : OmniversalGraph.Path
      (hodgeBranchGraph (V := V) (H := H) (p := p)) u v) :
    exists E : RealizedCorrespondenceExpr V H p,
      ExprMaterializesBranch E u v := by
  have Cedge : PrimitiveBranchCompiler (V := V) (H := H) (p := p) :=
    primitiveBranchCompiler_of_localizedL2 C
  induction gamma with
  | nil x =>
      exact ⟨.atom (diagonalRealized (V := V) (H := H) (p := p)),
        diagonal_materializes_reflexive_branch x⟩
  | cons e tail ih =>
      obtain ⟨Eedge, hEdge⟩ := Cedge e
      obtain ⟨Etail, hTail⟩ := ih
      refine ⟨.comp Etail Eedge, ?_⟩
      unfold ExprMaterializesBranch at hEdge hTail ⊢
      rw [RealizedCorrespondenceExpr.comp_cohomology_apply]
      rw [← hEdge]
      exact hTail

/-- Reachability in the handwritten omniverse is therefore genuine
correspondence reachability once the single localized-`L^2` primitive family is
externalized. -/
theorem reachable_has_realized_expression
    (C : LocalizedL2PrimitiveRealization (V := V) (H := H) (p := p))
    {u v : HodgeBranchNode (V := V) (H := H) (p := p)}
    (h : OmniversalGraph.Reachable
      (hodgeBranchGraph (V := V) (H := H) (p := p)) u v) :
    exists E : RealizedCorrespondenceExpr V H p,
      ExprMaterializesBranch E u v := by
  rcases h with ⟨gamma⟩
  exact causalPath_has_realized_expression C gamma

/-- **FULL FAN / CLOSURE REALIZATION.**
Every node in the event closure of a seed family is connected to one actual
seed by a single compiled genuine correspondence expression.  This is the
formal graph-theoretic version of a whole fan of diagonal causal rays emitted
from source nodes. -/
theorem closure_node_has_realized_ray
    (C : LocalizedL2PrimitiveRealization (V := V) (H := H) (p := p))
    (Seed : HodgeBranchNode (V := V) (H := H) (p := p) → Prop)
    {v : HodgeBranchNode (V := V) (H := H) (p := p)}
    (hv : OmniversalGraph.Closure
      (hodgeBranchGraph (V := V) (H := H) (p := p)) Seed v) :
    exists u : HodgeBranchNode (V := V) (H := H) (p := p),
      Seed u ∧
        exists E : RealizedCorrespondenceExpr V H p,
          ExprMaterializesBranch E u v := by
  rcases hv with ⟨u, hu, huv⟩
  exact ⟨u, hu, reachable_has_realized_expression C huv⟩

/-- The same single primitive family also certifies algebraicity stability of
all unary graph arrows AND every finite higher-arity omniverse synthesis. -/
theorem localizedL2_semanticallyStable
    (C : LocalizedL2PrimitiveRealization (V := V) (H := H) (p := p)) :
    HyperEventSystem.SemanticallyStable
      (hodgeBranchHyperEvents (V := V) (H := H) (p := p))
      (AlgebraicBranchNode (V := V) (H := H) (p := p)) := by
  exact algebraicBranchNode_semanticallyStable
    (primitiveBranchCompiler_of_localizedL2 C)

/-- Consequently every unary/higher-event state generated from algebraic seeds
stays in the genuine cycle-class range, with no per-edge matrix-unit
externalization family. -/
theorem generated_from_algebraic_seeds_of_localizedL2
    (C : LocalizedL2PrimitiveRealization (V := V) (H := H) (p := p))
    (Seed : HodgeBranchNode (V := V) (H := H) (p := p) → Prop)
    (hSeed : forall u, Seed u →
      AlgebraicBranchNode (V := V) (H := H) (p := p) u) :
    forall {u},
      HyperEventSystem.Generated
        (hodgeBranchHyperEvents (V := V) (H := H) (p := p)) Seed u →
      AlgebraicBranchNode (V := V) (H := H) (p := p) u := by
  exact generated_from_algebraic_seeds_is_algebraic
    (primitiveBranchCompiler_of_localizedL2 C) Seed hSeed

#check LocalizedL2PrimitiveRealization
#check primitiveBranchCompiler_of_localizedL2
#check diagonal_materializes_reflexive_branch
#check causalPath_has_realized_expression
#check reachable_has_realized_expression
#check closure_node_has_realized_ray
#check localizedL2_semanticallyStable
#check generated_from_algebraic_seeds_of_localizedL2

#print axioms primitiveBranchCompiler_of_localizedL2
#print axioms causalPath_has_realized_expression
#print axioms closure_node_has_realized_ray
#print axioms localizedL2_semanticallyStable

end GSTClassicalHodgeOmniverseLefschetzRayCompiler
