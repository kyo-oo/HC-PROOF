import HodgeConjecture
import GSTClassicalHodgePointReducedGeometricSpine
import GSTClassicalHodgeProjectivePointOmniverseSource

/-!
# THE FINAL FRONTIER — the conjecture reduced to its last native laws

This file is the hypothesis-crush landing of the whole campaign.  The master
assembly (`HodgeConjecture.hodge_conjecture_master_assembly`) still carried
four bundled inputs: the Stage-2G finiteness package `F`, the five-field
geometric spine `G`, the native-mass conserved charge `D`, and the
all-ordered-pairs projective two-generator family `R`.  The corpus meanwhile
proved far stronger reductions piece by piece.  This file composes them into
ONE crown with the smallest native law system that remains:

* **`F` is eliminated.**  No finiteness of the rational Hodge fibers is
  needed anywhere on the statement route: the unrestricted choice basis
  `classicalHodgeBasis` carries every weight, and dead weights (bottom
  fibers) are vacuous.
* **`G` collapses from five fields to three laws.**  Whole-cycle Hodge
  typing is manufactured from point atoms by the point normal form, and the
  pushforward/principal-cut operator pairs are manufactured from kernel
  stability.  What remains is: point classes are Hodge, pushforwards
  preserve the cycle-class kernel, and the principal-cut successor admits
  its kernel realization.
* **`D` (the native-mass bridge) is superseded.**  The degree-certified
  route needs only genuine projective degree semantics: a linear trace per
  weight, strictly positive on genuine point classes, certifying that point
  classes are nonzero.
* **`R` (all ordered pairs) is eliminated.**  The omniverse branch-material
  law replaces the two-generator family: strict scheme materialization of
  the primitive GST branch events at each live weight.

What remains open is exactly the residual native geometry: the three spine
laws, the degree semantics, live codimension points, and the branch
materialization.  For an arbitrary `HodgeBigradedBettiData` these are
genuine geometric content, not packaging — the corpus itself proves the
separation (`spine_laws_do_not_force_hodge`).  This file names that residual
system precisely and crushes everything above it.
-/

set_option maxHeartbeats 40000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeFinalFrontier

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTCompactNativeCyclePresentation
open GSTClassicalHodgePointNormalForm
open GSTClassicalHodgeProjectivePointTransport
open GSTClassicalHodgeNativeOperatorCohomologyRealization
open GSTClassicalHodgeGeometricSpineKernelReduction
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgePointReducedGeometricSpine
open GSTClassicalHodgeProjectiveDegreeTrace
open GSTClassicalHodgeOmniverseCausalBranchPacket
open GSTClassicalHodgeOmniverseStrictEventStability
open GSTClassicalHodgeProjectivePointOmniverseSource

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-! ## The final spine law system

Three native laws.  Everything else about the historical five-field spine is
manufactured: whole-cycle Hodge typing from point atoms (point normal form),
the pushforward cohomology action from kernel stability, and the complete
principal-cut operator pair from graded kernel stability.
-/

/-- **THE FINAL SPINE LAW SYSTEM.**  Point-level Hodge typing, pushforward
kernel stability, and the principal-cut kernel realization.  These are the
only non-packaging spine data that remain after the point normal form and
the kernel reduction theorems. -/
structure FinalFrontierSpineLaw where
  pointClass_is_hodge :
    ∀ p : Nat, ∀ x : CodimensionPoint V.X p,
      H.cycleClass p (codimensionPointCycle V.X p x) ∈
        rationalHodgeSubspace (H.hodgeBigrading p)
  pushforward_kernelStable :
    ∀ p : Nat, ∀ f : V.X ⟶ V.X,
      KernelStable (H := H) (smoothProjectiveNativePushforward V f p)
  principalCut : PrincipalCutKernelRealization (V := V) (H := H)

namespace FinalFrontierSpineLaw

/-- The final spine law system manufactures the point-reduced spine. -/
noncomputable def toPointReduced
    (L : FinalFrontierSpineLaw (V := V) (H := H)) :
    PointReducedGeometricCycleClassSpine (V := V) (H := H) where
  pointClass_is_hodge := L.pointClass_is_hodge
  pushforward_kernelStable := L.pushforward_kernelStable
  principalCut := L.principalCut

/-- The final spine law system manufactures the complete historical
geometric cycle-class spine: whole-cycle Hodge typing, pushforward
naturality squares, and the full principal-cut operator pair are all
generated theorems. -/
noncomputable def toSpine
    (L : FinalFrontierSpineLaw (V := V) (H := H)) :
    GeometricCycleClassSpine V H :=
  (L.toPointReduced).toKernelReduced.toGeometricCycleClassSpine

end FinalFrontierSpineLaw

/-! ## The final frontier geometry

The three spine laws, the projective degree semantics, live codimension
points, and the omniverse branch materialization.  Nothing else is assumed.
-/

/-- **THE FINAL FRONTIER.**  The complete residual native law system of the
Hodge route: spine laws, degree semantics, live points, branch
materialization.  Every hypothesis of the master assembly above this system
is a theorem. -/
structure FinalFrontierNativeGeometry where
  spine : FinalFrontierSpineLaw (V := V) (H := H)
  degree : ProjectiveDegreeTraceSemantics V H
  livePoint :
    ∀ p : Nat,
      rationalHodgeSubspace (H.hodgeBigrading p) ≠ ⊥ →
        Nonempty (CodimensionPoint V.X p)
  branch :
    ∀ p : Nat,
      ∀ {u v : HodgeBranchNode (V := V) (H := H) (p := p)},
        (hodgeBranchGraph (V := V) (H := H) (p := p)).Event u v →
          StrictlyMaterializedBranch u v

/-! ## The crown
-/

/-- **THE FINAL FRONTIER CROWN.**  The exact Stage-2G Hodge statement
follows from the residual native law system alone: no finiteness package,
no conserved-charge package, no all-pairs projective two-generator family. -/
theorem bigradedBettiHodge_of_final_frontier
    (F : FinalFrontierNativeGeometry (V := V) (H := H)) :
    BigradedBettiHodgeStatement V H :=
  bigradedBettiHodge_of_projectivePoint_strictOmniverse
    F.spine.toSpine F.degree F.livePoint F.branch

/-- **THE CLASSICAL TARGET FROM THE FINAL FRONTIER.**  `ClassicalHodgeTarget`
is by definition the exact bigraded statement, so the classical sentence —
every rational Hodge class on a smooth projective complex variety is the
class of an actual rational algebraic cycle — follows from the final
frontier alone. -/
theorem classicalHodgeTarget_of_final_frontier
    (F : FinalFrontierNativeGeometry (V := V) (H := H)) :
    HodgeConjecture.ClassicalHodgeTarget V H :=
  bigradedBettiHodge_of_final_frontier F

/-- **ELEMENTWISE NATIVE-CYCLE FORM.**  Every rational (p,p) class on the
variety is literally the cycle class of an actual codimension-p rational
algebraic cycle, under the final frontier alone. -/
theorem every_hodge_class_has_native_cycle_of_final_frontier
    (F : FinalFrontierNativeGeometry (V := V) (H := H))
    (p : Nat)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p)) :
    ∃ Z : codimensionCycles V.X p, H.cycleClass p Z = alpha :=
  LinearMap.mem_range.mp
    (bigradedBettiHodge_of_final_frontier F p halpha)

#check FinalFrontierSpineLaw
#check FinalFrontierSpineLaw.toSpine
#check FinalFrontierNativeGeometry
#check bigradedBettiHodge_of_final_frontier
#check classicalHodgeTarget_of_final_frontier
#check every_hodge_class_has_native_cycle_of_final_frontier

#print axioms FinalFrontierSpineLaw.toPointReduced
#print axioms FinalFrontierSpineLaw.toSpine
#print axioms bigradedBettiHodge_of_final_frontier
#print axioms classicalHodgeTarget_of_final_frontier
#print axioms every_hodge_class_has_native_cycle_of_final_frontier

end GSTClassicalHodgeFinalFrontier
