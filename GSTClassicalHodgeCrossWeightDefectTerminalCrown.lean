import GSTClassicalHodgeCrossWeightDefectRetraction

/-!
# GST CLASSICAL HODGE — CROSS-WEIGHT DEFECT TERMINAL CROWN

The previous file proved that a genuine nonzero-scaled return law makes every
principal-cut step injective on the atomic-defect quotient.  This file isolates
the complementary terminal input and proves the global consequence.

There are two terminality levels:

* `DefectTerminality`: sufficiently far above every starting weight, the whole
  atomic-defect quotient is zero;
* `AmbientCohomologyTerminality`: sufficiently far above every starting weight,
  the ambient rational singular cohomology itself is zero.

The second implies the first formally.  Combined with a family of genuine
principal-cut return laws, either terminality condition propagates zero defect
backwards through the entire graded ladder.  Using the already-proved exact
atomic-defect reformulation of Stage-2G Hodge, this yields the complete Hodge
statement.

The point of this crown is to expose a sharply geometric remaining route:
prove finite-dimensional top-degree cohomology vanishing for the actual
analytification, and construct the genuine principal-cut return reciprocity.
No same-weight matrix-unit externalization is needed.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeCrossWeightDefectTerminalCrown

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeAtomicDefectDuality
open GSTClassicalHodgeCrossWeightAtomicDefectDescent
open GSTClassicalHodgeCrossWeightDefectRetraction
open GSTClassicalHodgeGeometricCycleClassSpine

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Eventually the complete atomic-defect quotient vanishes above every
starting codimension. -/
structure DefectTerminality
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) where
  terminal :
    ∀ p : Nat,
      ∃ n : Nat, Subsingleton (DefectAt V H (p + n))

/-- Stronger geometric/topological form: actual rational singular cohomology
vanishes in some sufficiently high even degree above every starting weight. -/
structure AmbientCohomologyTerminality
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) where
  terminal :
    ∀ p : Nat,
      ∃ n : Nat, Subsingleton (CohAt H (p + n))

namespace AmbientCohomologyTerminality

/-- Zero ambient cohomology forces the corresponding atomic quotient to be
zero, independently of the cycle-class map. -/
noncomputable def toDefectTerminality
    (T : AmbientCohomologyTerminality V H) :
    DefectTerminality V H where
  terminal p := by
    rcases T.terminal p with ⟨n, hcoh⟩
    refine ⟨n, ?_⟩
    letI : Subsingleton (CohAt H (p + n)) := hcoh
    constructor
    intro x y
    refine Submodule.Quotient.induction_on x ?_
    intro a
    refine Submodule.Quotient.induction_on y ?_
    intro b
    congr 1
    exact Subsingleton.elim a b

end AmbientCohomologyTerminality

/-- Under injective principal-cut defect transport, eventual zero defect
propagates all the way back to every starting weight. -/
theorem atomicDefectLinearMap_zero_of_return_and_terminal
    (G : GeometricCycleClassSpine V H)
    (F : PrincipalCutReturnFamily G)
    (T : DefectTerminality V H) :
    ∀ p : Nat, atomicDefectLinearMap V H p = 0 := by
  intro p
  apply LinearMap.ext
  intro alpha
  rcases T.terminal p with ⟨n, hterminal⟩
  letI : Subsingleton (DefectAt V H (p + n)) := hterminal
  have htop :
      principalCutDefectIterate G p n
          (atomicDefectLinearMap V H p alpha) = 0 :=
    Subsingleton.elim _ _
  exact F.defect_eq_zero_of_iterate_eq_zero p n
    (atomicDefectLinearMap V H p alpha) htop

/-- **GRADED DEFECT TERMINAL CROWN.**  Genuine return reciprocity plus eventual
zero defect proves the full Stage-2G Hodge statement. -/
theorem bigradedBettiHodge_of_return_and_defectTerminality
    (G : GeometricCycleClassSpine V H)
    (F : PrincipalCutReturnFamily G)
    (T : DefectTerminality V H) :
    BigradedBettiHodgeStatement V H := by
  exact (bigradedBettiHodgeStatement_iff_atomicDefect_zero V H).2
    (atomicDefectLinearMap_zero_of_return_and_terminal G F T)

/-- **AMBIENT TERMINAL CROWN.**  It is enough to prove ordinary high-degree
vanishing for the actual analytification: zero ambient cohomology gives zero
defect automatically, and the return laws propagate that vanishing downward. -/
theorem bigradedBettiHodge_of_return_and_ambientTerminality
    (G : GeometricCycleClassSpine V H)
    (F : PrincipalCutReturnFamily G)
    (T : AmbientCohomologyTerminality V H) :
    BigradedBettiHodgeStatement V H := by
  exact bigradedBettiHodge_of_return_and_defectTerminality
    G F T.toDefectTerminality

#check DefectTerminality
#check AmbientCohomologyTerminality
#check AmbientCohomologyTerminality.toDefectTerminality
#check atomicDefectLinearMap_zero_of_return_and_terminal
#check bigradedBettiHodge_of_return_and_defectTerminality
#check bigradedBettiHodge_of_return_and_ambientTerminality

#print axioms AmbientCohomologyTerminality.toDefectTerminality
#print axioms atomicDefectLinearMap_zero_of_return_and_terminal
#print axioms bigradedBettiHodge_of_return_and_defectTerminality
#print axioms bigradedBettiHodge_of_return_and_ambientTerminality

end GSTClassicalHodgeCrossWeightDefectTerminalCrown
