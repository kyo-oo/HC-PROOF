import GSTClassicalHodgeOneExactSuccessorNonErasure
import GSTClassicalHodgeRelativeSuccessorNonempty
import GSTClassicalHodgeSeparatorRelativeCoheightOne

/-!
# GST CLASSICAL HODGE — CANONICAL SEPARATOR NON-ERASURE

The separator construction already manufactures a distinguished relative
height-one successor in every projectively live source closure.  The sharp
one-successor theorem shows that the principal-cut operator does not need a
global exact-stratum theorem: it needs only this distinguished successor to
have the expected absolute ambient codimension.

This file packages that one remaining geometric equality and immediately
feeds it into native non-erasure.  The packaged statement is pure scheme
geometry.  It contains no Hodge basis, cycle-class surjectivity, separator
functional, or algebraicity conclusion.
-/

set_option maxHeartbeats 40000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgePointClosureRelativeCut
open GSTClassicalHodgePrincipalCutSuccessorOperator
open GSTClassicalHodgeHeightOneProjectiveRelevance
open GSTClassicalHodgeSeparatorRelativeCoheightOne
open GSTClassicalHodgeRelativeSuccessorNonempty
open GSTClassicalHodgeOneExactSuccessorNonErasure

namespace GSTClassicalHodgeCanonicalSeparatorNonErasure

/-- The single absolute-grading statement still needed for the distinguished
separator successor.  Relative coheight one is already proved independently;
this asks only that codimension add along that one cover. -/
def CanonicalSeparatorAmbientExact
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hlive : ProjectivelyLiveSource V.projective.n
      (V.projective.immersion x.1)) : Prop :=
  Order.coheight
      (ambientSuccessorPoint V x.1
        (relativeHeightOneSeparatorSuccessor V x.1 hlive)) = p + 1

/-- The canonical separator successor is genuinely one of the finite relative
successors used by the principal-cut presentation. -/
theorem canonicalSeparator_mem_relativeFinset
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hlive : ProjectivelyLiveSource V.projective.n
      (V.projective.immersion x.1)) :
    relativeHeightOneSeparatorSuccessor V x.1 hlive ∈
      relativeCodimensionOneFinset V x.1 := by
  exact relativeHeightOneSeparatorSuccessor_mem_finset V x.1 hlive

/-- **CANONICAL-SEPARATOR MASS NON-ERASURE.**
The single absolute-grade equality for the distinguished separator successor
already forces strictly positive principal-cut mass. -/
theorem successorMass_pos_of_canonicalSeparator
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hlive : ProjectivelyLiveSource V.projective.n
      (V.projective.immersion x.1))
    (hExact : CanonicalSeparatorAmbientExact V p x hlive) :
    0 < successorMass V p x := by
  exact successorMass_pos_of_one_exact V p x
    (relativeHeightOneSeparatorSuccessor V x.1 hlive)
    (canonicalSeparator_mem_relativeFinset V p x hlive)
    hExact

/-- **CANONICAL-SEPARATOR NATIVE NON-ERASURE.**
Once the canonical projective separator cover has absolute grade p+1, the
actual geometry-built principal-cut operator sends the source point atom to a
nonzero native codimension-(p+1) cycle. -/
theorem successorNativeOperator_point_ne_zero_of_canonicalSeparator
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hlive : ProjectivelyLiveSource V.projective.n
      (V.projective.immersion x.1))
    (hExact : CanonicalSeparatorAmbientExact V p x hlive) :
    successorNativeOperator V p (codimensionPointCycle V.X p x) ≠ 0 := by
  exact successorNativeOperator_point_ne_zero_of_one_exact V p x
    (relativeHeightOneSeparatorSuccessor V x.1 hlive)
    (canonicalSeparator_mem_relativeFinset V p x hlive)
    hExact

/-- The entire principal-cut non-erasure frontier has therefore collapsed to
one pure geometric equality for one canonical successor. -/
theorem canonical_separator_non_erasure_crown
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hlive : ProjectivelyLiveSource V.projective.n
      (V.projective.immersion x.1))
    (hExact : CanonicalSeparatorAmbientExact V p x hlive) :
    0 < successorMass V p x
      ∧ successorNativeOperator V p
          (codimensionPointCycle V.X p x) ≠ 0 := by
  exact ⟨successorMass_pos_of_canonicalSeparator V p x hlive hExact,
    successorNativeOperator_point_ne_zero_of_canonicalSeparator
      V p x hlive hExact⟩

#check CanonicalSeparatorAmbientExact
#check canonicalSeparator_mem_relativeFinset
#check successorMass_pos_of_canonicalSeparator
#check successorNativeOperator_point_ne_zero_of_canonicalSeparator
#check canonical_separator_non_erasure_crown

#print axioms successorMass_pos_of_canonicalSeparator
#print axioms successorNativeOperator_point_ne_zero_of_canonicalSeparator
#print axioms canonical_separator_non_erasure_crown

end GSTClassicalHodgeCanonicalSeparatorNonErasure
