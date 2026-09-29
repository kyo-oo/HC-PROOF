import GSTClassicalHodgeSingleExactSuccessorSurvival
import GSTClassicalHodgeSeparatorRelativeCutLanding
import GSTClassicalHodgeRelativeSuccessorLowerBound

/-!
# GST CLASSICAL HODGE — SEPARATOR AMBIENT EXACT LANDING

This layer isolates the last numerical statement needed by the canonical
single-separator successor route.

The geometry below this file already proves that the canonical separator
successor

* is a genuine point of the source-closure principal cut;
* has relative coheight exactly one;
* is strictly below its source point in the ambient specialization order.

Consequently its ambient coheight is already bounded below by `p + 1` for a
source of ambient codimension `p`.  Therefore the entire exact-stratum and
nonvanishing problem reduces to one honest geometric inequality:

  `coheight(separator successor) <= p + 1`.

Once that upper bound is proved from smooth local geometry, equality follows
by antisymmetry and the existing single-successor survival theorem immediately
produces a nonzero native graded successor operator.

No Hodge class, cycle-class surjectivity, projective visibility assumption, or
new axiom occurs here.
-/

set_option maxHeartbeats 50000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgePointClosurePrincipalCut
open GSTClassicalHodgePointClosureRelativeCut
open GSTClassicalHodgePrincipalCutSuccessorOperator
open GSTClassicalHodgeRelativeSuccessorLowerBound
open GSTClassicalHodgeHeightOneProjectiveRelevance
open GSTClassicalHodgeSeparatorPointClosureLift
open GSTClassicalHodgeSeparatorRelativeCutLanding
open GSTClassicalHodgeSeparatorRelativeCoheightOne
open GSTClassicalHodgeSingleExactSuccessorSurvival

namespace GSTClassicalHodgeSeparatorAmbientExactLanding

/-- The already-proved strict ambient specialization gives the canonical
separator successor the unconditional lower ambient grading bound `p + 1`. -/
theorem separatorSuccessor_ambient_coheight_ge_succ
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hlive : ProjectivelyLiveSource V.projective.n (V.projective.immersion x.1)) :
    (p + 1 : ℕ∞) ≤
      Order.coheight
        (ambientSuccessorPoint V x.1
          (relativeHeightOneSeparatorSuccessor V x.1 hlive)) := by
  have h := ambient_coheight_ge_succ V p x
    (pointClosureSeparatorSuccessor V x.1 hlive)
    (pointClosureSeparatorSuccessor_mem_relativeCut V x.1 hlive)
  simpa [ambientSuccessorPoint, relativeHeightOneSeparatorSuccessor] using h

/-- The missing smooth-geometric upper bound is sufficient to force exact
ambient codimension `p + 1`; no stronger global exact-stratum statement is
required for the canonical separator. -/
theorem separatorSuccessor_ambient_coheight_exact_of_upper_bound
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hlive : ProjectivelyLiveSource V.projective.n (V.projective.immersion x.1))
    (hupper :
      Order.coheight
        (ambientSuccessorPoint V x.1
          (relativeHeightOneSeparatorSuccessor V x.1 hlive)) ≤
        (p + 1 : ℕ∞)) :
    Order.coheight
        (ambientSuccessorPoint V x.1
          (relativeHeightOneSeparatorSuccessor V x.1 hlive)) = p + 1 := by
  exact le_antisymm hupper
    (separatorSuccessor_ambient_coheight_ge_succ V p x hlive)

/-- **UPPER-BOUND-ONLY SURVIVAL LANDING.**
To make the geometry-built successor operator nonzero it is enough to prove the
single ambient upper bound for the canonical separator successor.  The lower
bound and exactness are already internal theorems. -/
theorem separator_successor_survives_of_ambient_upper_bound
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hlive : ProjectivelyLiveSource V.projective.n (V.projective.immersion x.1))
    (hupper :
      Order.coheight
        (ambientSuccessorPoint V x.1
          (relativeHeightOneSeparatorSuccessor V x.1 hlive)) ≤
        (p + 1 : ℕ∞)) :
    successorMass V p x ≠ 0
      ∧ successorNativeOperator V p
          (codimensionPointCycle V.X p x) ≠ 0 := by
  apply separator_successor_survives_of_ambient_exact V p x hlive
  exact separatorSuccessor_ambient_coheight_exact_of_upper_bound
    V p x hlive hupper

#check separatorSuccessor_ambient_coheight_ge_succ
#check separatorSuccessor_ambient_coheight_exact_of_upper_bound
#check separator_successor_survives_of_ambient_upper_bound

#print axioms separatorSuccessor_ambient_coheight_ge_succ
#print axioms separatorSuccessor_ambient_coheight_exact_of_upper_bound
#print axioms separator_successor_survives_of_ambient_upper_bound

end GSTClassicalHodgeSeparatorAmbientExactLanding
