import Mathlib.Topology.KrullDimension
import GSTClassicalHodgePrincipalSectionDescent

/-!
# GST CLASSICAL HODGE — CODIMENSION-ONE POINTS OF PROPER PRINCIPAL CUTS

The principal-section engine gives a genuinely proper closed subset through
which recursive support cutting proceeds.  The pinned Mathlib topology now
contains the exact dimension-theoretic theorem needed at this point: in a
Noetherian quasi-sober irreducible space, the ambient coheight-one points of a
non-dense subspace are controlled by the coheight-zero points (generic points)
of that subspace, hence are finite.

This module packages that theorem for closed cuts and then specializes it to
the source-dependent principal cut produced by the projective geometry layer.
The result is the first numerical codimension step from the geometric cutting
machine.
-/

set_option maxHeartbeats 30000000
set_option maxRecDepth 1000000

noncomputable section

open TopologicalSpace
open AlgebraicGeometry
open GSTProjectiveOverC
open GSTClassicalHodgePrincipalSectionDescent
open GSTSmoothProjectiveNoetherian

namespace GSTClassicalHodgeProperCutCodimensionOne

/-- A proper closed subset of a Noetherian quasi-sober irreducible space has
only finitely many ambient points of coheight one. -/
attribute [local instance] specializationOrder in
theorem finite_coheight_one_of_proper_closed
    {X : Type*} [TopologicalSpace X] [QuasiSober X] [IrreducibleSpace X]
    [T0Space X] [NoetherianSpace X]
    (C : Set X) (hC : IsClosed C) (hproper : C ≠ Set.univ) :
    {x ∈ C | Order.coheight x = 1}.Finite := by
  letI : T0Space C := inferInstance
  letI : NoetherianSpace C := inferInstance
  letI : QuasiSober C := Topology.IsClosedEmbedding.quasiSober
    (Topology.IsClosedEmbedding.subtypeVal hC)
  apply TopologicalSpace.NoetherianSpace.finite_coheight_one_of_closure_ne_univ
  simpa [C.closure_eq] using hproper

/-- Every source-specific principal cut in an irreducible smooth projective
carrier has only finitely many ambient codimension-one points. -/
theorem finite_principal_cut_coheight_one
    (V : SmoothProjectiveComplexScheme)
    [IrreducibleSpace V.X]
    (x : V.X) :
    {y ∈ cutSupport V x | Order.coheight y = 1}.Finite := by
  letI : IsNoetherian V.X := smoothProjectiveIsNoetherian V
  letI : NoetherianSpace V.X := smoothProjectiveNoetherianSpace V
  apply finite_coheight_one_of_proper_closed
  · exact (principalSectionIdeal V
      (positiveHomogeneousSeparator V.projective.n
        (V.projective.immersion x)).equation).isClosed_support
  · exact principalSectionAt_support_ne_univ V x

/-- A nonempty codimension-one locus of the selected cut can be packaged as a
finite set of genuine Stage-2D codimension-one points. -/
noncomputable def principalCutCodimensionOneFinset
    (V : SmoothProjectiveComplexScheme)
    [IrreducibleSpace V.X]
    (x : V.X) : Finset (GSTNativeCodimensionCyclePresentation.CodimensionPoint V.X 1) := by
  classical
  let s : Set V.X := {y ∈ cutSupport V x | Order.coheight y = 1}
  have hs : s.Finite := finite_principal_cut_coheight_one V x
  exact hs.toFinset.attach.map
    ⟨fun y => (⟨y.1, y.2.2⟩ : GSTNativeCodimensionCyclePresentation.CodimensionPoint V.X 1),
      by
        intro a b h
        apply Subtype.ext
        simpa using congrArg Subtype.val h⟩

/-- Numerical one-step crown: strict projective cutting has a finite native
codimension-one target locus, expressed directly in the coheight convention
used by `codimensionCycles`. -/
theorem principal_cut_codimension_one_crown
    (V : SmoothProjectiveComplexScheme)
    [IrreducibleSpace V.X]
    (x : V.X) :
    {y ∈ cutSupport V x | Order.coheight y = 1}.Finite
      ∧ ∀ y : GSTNativeCodimensionCyclePresentation.CodimensionPoint V.X 1,
        y.1 ∈ cutSupport V x → Order.coheight y.1 = 1 := by
  refine ⟨finite_principal_cut_coheight_one V x, ?_⟩
  intro y _
  exact y.2

#check finite_coheight_one_of_proper_closed
#check finite_principal_cut_coheight_one
#check principalCutCodimensionOneFinset
#check principal_cut_codimension_one_crown

#print axioms finite_coheight_one_of_proper_closed
#print axioms finite_principal_cut_coheight_one
#print axioms principalCutCodimensionOneFinset
#print axioms principal_cut_codimension_one_crown

end GSTClassicalHodgeProperCutCodimensionOne
