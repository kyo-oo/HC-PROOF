import Mathlib.Topology.KrullDimension
import GSTClassicalHodgePointClosureIrreducible
import GSTClassicalHodgeSeparatorAmbientExactLanding

/-!
# GST CLASSICAL HODGE — GENERIC SEPARATOR AMBIENT EXACTNESS

For an irreducible smooth projective carrier, a codimension-zero source point
is the ambient generic point.  Its reduced point-closure therefore has full
underlying support.  The closed point-closure immersion is consequently also
an open embedding, and Mathlib's specialization-order coheight theorem for
open embeddings identifies relative and ambient coheight exactly.

Applied to the canonical separator successor, whose relative coheight is
already exactly one, this proves an unconditional ambient codimension-one
step from every projectively-live generic source.  The existing single
successor theorem then gives nonzero native successor mass and a nonzero
native graded successor operator.

No catenarity theorem, Hodge surjectivity, cycle representative assumption,
or new axiom is used.
-/

set_option maxHeartbeats 50000000
set_option maxRecDepth 1000000

noncomputable section

open TopologicalSpace
open AlgebraicGeometry
open GSTProjectiveOverC
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgePointClosurePrincipalCut
open GSTClassicalHodgePointClosureIrreducible
open GSTClassicalHodgePrincipalCutSuccessorOperator
open GSTClassicalHodgeSeparatorRelativeCoheightOne
open GSTClassicalHodgeSeparatorAmbientExactLanding
open GSTClassicalHodgeSingleExactSuccessorSurvival

namespace GSTClassicalHodgeSeparatorGenericExact

attribute [local instance] specializationOrder

/-- In an irreducible scheme, an ambient coheight-zero point is the generic
point, hence its singleton closure is the whole carrier. -/
theorem closure_source_eq_univ_of_coheight_zero
    (V : SmoothProjectiveComplexScheme)
    [IrreducibleSpace V.X]
    (x : CodimensionPoint V.X 0) :
    closure ({x.1} : Set V.X) = Set.univ := by
  obtain ⟨η, hη⟩ : ∃ η : V.X, IsGenericPoint η (Set.univ : Set V.X) :=
    QuasiSober.sober (IrreducibleSpace.isIrreducible_univ V.X) isClosed_univ
  have hmax : IsMax x.1 := (Order.coheight_eq_zero).mp x.2
  have hxη : x.1 ≤ η := hη.specializes (Set.mem_univ x.1)
  have hxeq : x.1 = η := le_antisymm hxη (hmax hxη)
  rw [hxeq]
  exact hη.def.symm

/-- The point-closure immersion of a codimension-zero point in an irreducible
carrier has full range, so the existing closed embedding is simultaneously an
open embedding. -/
theorem pointClosureι_isOpenEmbedding_of_coheight_zero
    (V : SmoothProjectiveComplexScheme)
    [IrreducibleSpace V.X]
    (x : CodimensionPoint V.X 0) :
    Topology.IsOpenEmbedding (pointClosureι V x.1) := by
  refine ⟨(pointClosureι V x.1).isEmbedding, ?_⟩
  rw [range_pointClosureι V x.1,
    closure_source_eq_univ_of_coheight_zero V x]
  exact isOpen_univ

/-- Relative coheight in the generic point-closure is exactly ambient
coheight.  This is the order-theoretic replacement for any catenarity argument
at weight zero. -/
theorem ambient_coheight_eq_relative_of_source_zero
    (V : SmoothProjectiveComplexScheme)
    [IrreducibleSpace V.X]
    (x : CodimensionPoint V.X 0)
    (y : pointClosureScheme V x.1) :
    Order.coheight (pointClosureι V x.1 y) = Order.coheight y := by
  exact Topology.IsOpenEmbedding.coheight_eq
    (pointClosureι V x.1)
    (pointClosureι_isOpenEmbedding_of_coheight_zero V x)

/-- **GENERIC SEPARATOR EXACTNESS.**  The canonical relative-height-one
separator successor of a projectively-live generic source is an actual ambient
codimension-one point. -/
theorem separatorSuccessor_ambient_coheight_one
    (V : SmoothProjectiveComplexScheme)
    [IrreducibleSpace V.X]
    (x : CodimensionPoint V.X 0)
    (hlive : ProjectivelyLiveSource V.projective.n
      (V.projective.immersion x.1)) :
    Order.coheight
      (ambientSuccessorPoint V x.1
        (relativeHeightOneSeparatorSuccessor V x.1 hlive)) = 1 := by
  rw [ambientSuccessorPoint]
  rw [ambient_coheight_eq_relative_of_source_zero V x]
  exact (relativeHeightOneSeparatorSuccessor V x.1 hlive).2

/-- Exact-stratum form consumed by the single-successor survival theorem. -/
theorem separatorSuccessor_ambient_exact_zero
    (V : SmoothProjectiveComplexScheme)
    [IrreducibleSpace V.X]
    (x : CodimensionPoint V.X 0)
    (hlive : ProjectivelyLiveSource V.projective.n
      (V.projective.immersion x.1)) :
    Order.coheight
      (ambientSuccessorPoint V x.1
        (relativeHeightOneSeparatorSuccessor V x.1 hlive)) = 0 + 1 := by
  simpa using separatorSuccessor_ambient_coheight_one V x hlive

/-- **UNCONDITIONAL GENERIC-SOURCE SURVIVAL.**  On an irreducible carrier the
canonical separator built from a projectively-live codimension-zero source
already survives the ambient exact-stratum filter. -/
theorem separator_successor_survives_from_generic_source
    (V : SmoothProjectiveComplexScheme)
    [IrreducibleSpace V.X]
    (x : CodimensionPoint V.X 0)
    (hlive : ProjectivelyLiveSource V.projective.n
      (V.projective.immersion x.1)) :
    successorMass V 0 x ≠ 0
      ∧ successorNativeOperator V 0
          (codimensionPointCycle V.X 0 x) ≠ 0 := by
  exact separator_successor_survives_of_ambient_exact
    V 0 x hlive (separatorSuccessor_ambient_exact_zero V x hlive)

#check closure_source_eq_univ_of_coheight_zero
#check pointClosureι_isOpenEmbedding_of_coheight_zero
#check ambient_coheight_eq_relative_of_source_zero
#check separatorSuccessor_ambient_coheight_one
#check separatorSuccessor_ambient_exact_zero
#check separator_successor_survives_from_generic_source

#print axioms closure_source_eq_univ_of_coheight_zero
#print axioms ambient_coheight_eq_relative_of_source_zero
#print axioms separatorSuccessor_ambient_coheight_one
#print axioms separator_successor_survives_from_generic_source

end GSTClassicalHodgeSeparatorGenericExact
