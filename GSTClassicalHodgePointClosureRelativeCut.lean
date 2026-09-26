import GSTClassicalHodgePointClosureIrreducible
import GSTClassicalHodgeProperCutCodimensionOne

/-!
# GST CLASSICAL HODGE — RELATIVE CODIMENSION-ONE SUCCESSORS

For an arbitrary generic point `x`, the reduced closure scheme of `x` is an
irreducible Noetherian carrier.  The source-specific principal section cuts
this closure by pullback.  The lifted generic point is not contained in the
cut because its ambient image is exactly `x`, while the chosen separator was
constructed to avoid `x`.

Therefore the cut is a proper closed subset of the irreducible point closure.
The pinned topological Krull theorem then makes its relative coheight-one locus
finite.  These points are the recursive codimension-successor candidates from
which the graded native cut operator is assembled.
-/

set_option maxHeartbeats 30000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicGeometry
open TopologicalSpace
open GSTProjectiveOverC
open GSTClassicalHodgeProjectivePrincipalSection
open GSTClassicalHodgePointClosurePrincipalCut
open GSTClassicalHodgePointClosureIrreducible
open GSTClassicalHodgeProperCutCodimensionOne

namespace GSTClassicalHodgePointClosureRelativeCut

/-- Closed subset of the point-closure carrier swept out by the restricted
principal cut. -/
def relativeCutSet
    (V : SmoothProjectiveComplexScheme) (x : V.X) :
    Set (pointClosureScheme V x) :=
  Set.range (closurePrincipalCutToClosure V x)

/-- The relative cut is closed. -/
theorem relativeCutSet_isClosed
    (V : SmoothProjectiveComplexScheme) (x : V.X) :
    IsClosed (relativeCutSet V x) := by
  exact (closurePrincipalCutToClosure V x).isClosedEmbedding.isClosed_range

/-- The lifted generic point of the closure is not contained in the restricted
principal cut. -/
theorem closureGenericPoint_not_mem_relativeCut
    (V : SmoothProjectiveComplexScheme) (x : V.X) :
    closureGenericPoint V x ∉ relativeCutSet V x := by
  rintro ⟨z, hz⟩
  have hamb :
      principalSectionAtι V x (closurePrincipalCutToSection V x z) = x := by
    have hcond := congrArg (fun f => f z)
      (closurePrincipalCut_condition V x)
    rw [Scheme.comp_apply, Scheme.comp_apply, hz,
      closureGenericPoint_maps_to_source V x] at hcond
    exact hcond.symm
  have hxrange : x ∈ Set.range (principalSectionAtι V x) :=
    ⟨closurePrincipalCutToSection V x z, hamb⟩
  have hxsupport : x ∈
      (principalSectionIdeal V
        (positiveHomogeneousSeparator V.projective.n
          (V.projective.immersion x)).equation).support := by
    exact (Scheme.IdealSheafData.range_subschemeι
      (principalSectionIdeal V
        (positiveHomogeneousSeparator V.projective.n
          (V.projective.immersion x)).equation)).subset hxrange
  exact source_not_mem_principalSection V x hxsupport

/-- The relative principal cut is genuinely proper in the point closure. -/
theorem relativeCutSet_ne_univ
    (V : SmoothProjectiveComplexScheme) (x : V.X) :
    relativeCutSet V x ≠ Set.univ := by
  intro h
  apply closureGenericPoint_not_mem_relativeCut V x
  rw [h]
  trivial

/-- The closure of the relative cut is still proper because the cut is closed. -/
theorem closure_relativeCutSet_ne_univ
    (V : SmoothProjectiveComplexScheme) (x : V.X) :
    closure (relativeCutSet V x) ≠ Set.univ := by
  rw [(relativeCutSet_isClosed V x).closure_eq]
  exact relativeCutSet_ne_univ V x

/-- The relative coheight-one successor locus is finite. -/
theorem finite_relative_coheight_one
    (V : SmoothProjectiveComplexScheme) (x : V.X) :
    {y ∈ relativeCutSet V x | Order.coheight y = 1}.Finite := by
  letI : IrreducibleSpace (pointClosureScheme V x) :=
    pointClosureIrreducibleSpace V x
  letI : IsNoetherian (pointClosureScheme V x) :=
    pointClosureIsNoetherian V x
  letI : NoetherianSpace (pointClosureScheme V x) := by infer_instance
  let C := relativeCutSet V x
  letI : QuasiSober C := Topology.IsClosedEmbedding.quasiSober
    (Topology.IsClosedEmbedding.subtypeVal (relativeCutSet_isClosed V x))
  exact TopologicalSpace.NoetherianSpace.finite_coheight_one_of_closure_ne_univ
    (closure_relativeCutSet_ne_univ V x)

/-- Finite relative successor finset. -/
noncomputable def relativeCodimensionOneFinset
    (V : SmoothProjectiveComplexScheme) (x : V.X) :
    Finset {y : pointClosureScheme V x // Order.coheight y = 1} := by
  classical
  let s : Set (pointClosureScheme V x) :=
    {y ∈ relativeCutSet V x | Order.coheight y = 1}
  have hs : s.Finite := finite_relative_coheight_one V x
  exact hs.toFinset.attach.map
    ⟨fun y => ⟨y.1, by
        have hy : y.1 ∈ s := by simpa using y.2
        exact (Set.mem_sep.mp hy).2⟩,
      by
        intro a b h
        apply Subtype.ext
        simpa using congrArg Subtype.val h⟩

/-- Relative-successor crown. -/
theorem point_closure_relative_successor_crown
    (V : SmoothProjectiveComplexScheme) (x : V.X) :
    IsClosed (relativeCutSet V x)
      ∧ relativeCutSet V x ≠ Set.univ
      ∧ {y ∈ relativeCutSet V x | Order.coheight y = 1}.Finite := by
  exact ⟨relativeCutSet_isClosed V x,
    relativeCutSet_ne_univ V x,
    finite_relative_coheight_one V x⟩

#check relativeCutSet
#check closureGenericPoint_not_mem_relativeCut
#check relativeCutSet_ne_univ
#check finite_relative_coheight_one
#check relativeCodimensionOneFinset
#check point_closure_relative_successor_crown

#print axioms closureGenericPoint_not_mem_relativeCut
#print axioms relativeCutSet_ne_univ
#print axioms finite_relative_coheight_one
#print axioms point_closure_relative_successor_crown

end GSTClassicalHodgePointClosureRelativeCut
