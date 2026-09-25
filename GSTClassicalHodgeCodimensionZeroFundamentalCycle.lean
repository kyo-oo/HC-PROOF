import GSTSmoothProjectiveNoetherian
import GSTNativeCodimensionCyclePresentation
import Mathlib.Topology.KrullDimension

/-!
# GST CLASSICAL HODGE — CANONICAL CODIMENSION-ZERO FUNDAMENTAL CYCLE

A smooth projective carrier need not be irreducible.  The correct geometry-first
base cycle therefore sums over all irreducible components rather than choosing
one component by hypothesis.

For a sober `T0` space, Mathlib identifies the coheight-zero points in the
specialization order with the irreducible components.  The smooth projective
carrier is Noetherian, so it has finitely many irreducible components.  Hence
its coheight-zero locus is finite.

Summing one native point cycle at every coheight-zero generic point produces a
canonical rational codimension-zero algebraic cycle on every smooth projective
complex scheme, with no irreducibility assumption and no Hodge semantics.
-/

set_option maxHeartbeats 30000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open TopologicalSpace
open GSTProjectiveOverC
open GSTSmoothProjectiveNoetherian
open GSTNativeCodimensionCyclePresentation

namespace GSTClassicalHodgeCodimensionZeroFundamentalCycle

/-- The coheight-zero locus of a smooth projective carrier is finite. -/
theorem finite_coheight_zero
    (V : SmoothProjectiveComplexScheme) :
    {x : V.X | Order.coheight x = 0}.Finite := by
  letI : IsNoetherian V.X := smoothProjectiveIsNoetherian V
  letI : NoetherianSpace V.X := smoothProjectiveNoetherianSpace V
  have hcomp : (irreducibleComponents V.X).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  let e := coheightZeroSetOrderIsoIrreducibleComponents (X := V.X)
  exact (Equiv.finite_iff e.toEquiv).mpr hcomp

/-- Finite set of all genuine codimension-zero generic points. -/
noncomputable def codimensionZeroPointFinset
    (V : SmoothProjectiveComplexScheme) :
    Finset (CodimensionPoint V.X 0) := by
  classical
  let s : Set V.X := {x : V.X | Order.coheight x = 0}
  have hs : s.Finite := finite_coheight_zero V
  exact hs.toFinset.attach.map
    ⟨fun x => (⟨x.1, x.2⟩ : CodimensionPoint V.X 0),
      by
        intro a b h
        apply Subtype.ext
        simpa using congrArg Subtype.val h⟩

/-- Canonical finite codimension-zero presentation: coefficient one on every
irreducible-component generic point. -/
noncomputable def codimensionZeroPresentation
    (V : SmoothProjectiveComplexScheme) :
    FiniteCodimensionPresentation V.X 0 := by
  classical
  exact (codimensionZeroPointFinset V).sum
    (fun x => Finsupp.single x 1)

/-- Canonical native codimension-zero component cycle. -/
noncomputable def codimensionZeroFundamentalCycle
    (V : SmoothProjectiveComplexScheme) :
    codimensionCycles V.X 0 :=
  realizeFiniteCodimensionPresentation V.X 0
    (codimensionZeroPresentation V)

/-- Native codimension receipt. -/
theorem codimensionZeroFundamentalCycle_is_native
    (V : SmoothProjectiveComplexScheme) :
    (codimensionZeroFundamentalCycle V : AlgebraicCycle V.X ℚ) ∈
      codimensionCycles V.X 0 :=
  (codimensionZeroFundamentalCycle V).2

/-- Exact cycle-class formula under any rational cycle-class map. -/
theorem cycleClass_codimensionZeroFundamentalCycle
    {Coh : Type*} [AddCommGroup Coh] [Module ℚ Coh]
    (V : SmoothProjectiveComplexScheme)
    (cl : codimensionCycles V.X 0 →ₗ[ℚ] Coh) :
    cl (codimensionZeroFundamentalCycle V) =
      (codimensionZeroPresentation V).sum
        (fun x q => q • cl (codimensionPointCycle V.X 0 x)) := by
  exact linearMap_realizeFiniteCodimensionPresentation
    V.X 0 cl (codimensionZeroPresentation V)

/-- Every point appearing in the canonical base presentation is a genuine
coheight-zero point. -/
theorem mem_codimensionZeroPointFinset_coheight
    (V : SmoothProjectiveComplexScheme)
    (x : CodimensionPoint V.X 0)
    (hx : x ∈ codimensionZeroPointFinset V) :
    Order.coheight x.1 = 0 :=
  x.2

/-- Base geometry crown. -/
theorem codimension_zero_geometry_crown
    (V : SmoothProjectiveComplexScheme) :
    {x : V.X | Order.coheight x = 0}.Finite
      ∧ ∃ Z : codimensionCycles V.X 0,
        Z = codimensionZeroFundamentalCycle V := by
  exact ⟨finite_coheight_zero V,
    ⟨codimensionZeroFundamentalCycle V, rfl⟩⟩

#check finite_coheight_zero
#check codimensionZeroPointFinset
#check codimensionZeroPresentation
#check codimensionZeroFundamentalCycle
#check cycleClass_codimensionZeroFundamentalCycle
#check codimension_zero_geometry_crown

#print axioms finite_coheight_zero
#print axioms codimensionZeroFundamentalCycle
#print axioms cycleClass_codimensionZeroFundamentalCycle
#print axioms codimension_zero_geometry_crown

end GSTClassicalHodgeCodimensionZeroFundamentalCycle
