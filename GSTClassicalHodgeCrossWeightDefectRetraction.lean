import GSTClassicalHodgeCrossWeightAtomicDefectDescent

/-!
# GST CLASSICAL HODGE — CROSS-WEIGHT DEFECT RETRACTION

The genuine principal-cut geometry already gives an unconditional forward map

  Defect_p -> Defect_(p+1)

on the atomic cycle-class quotient.  What is still missing geometrically is a
return transport.  This file isolates the exact noncircular strength needed
from such a return map.

A `GradedDefectRetraction` consists of two genuine graded cycle-class operator
pairs and a nonzero rational scalar such that the cohomological round trip is
that scalar times the identity.  Because both operators are already natural on
actual algebraic cycles, the same round-trip law descends automatically to the
atomic-defect quotient.  Hence the forward defect operator is injective.

Specializing to the projective principal-cut spine gives the precise geometry
frontier:

  principal cut p -> p+1
  + genuine native return p+1 -> p
  + nonzero scaled round-trip on cohomology
  => principal-cut transport is injective on atomic defects.

Therefore a terminal zero defect at any later weight propagates backwards to
all earlier weights along a family of such return laws.  No basis-cycle
representative, Hodge surjectivity, same-weight matrix unit, or bare L^2 lift
is assumed here.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeCrossWeightDefectRetraction

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeCrossWeightNativePropagation
open GSTClassicalHodgeCrossWeightAtomicDefectDescent
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeAtomicDefectDuality

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p q : Nat}

/-- Two genuine graded native/cohomological transports whose round trip is a
nonzero scalar on the ambient rational cohomology.  This is an operator law,
not a Hodge-surjectivity statement. -/
structure GradedDefectRetraction
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p q : Nat) where
  forward : GradedCycleClassOperatorPair V H p q
  backward : GradedCycleClassOperatorPair V H q p
  scalar : ℚ
  scalar_ne_zero : scalar ≠ 0
  cohomology_roundtrip :
    ∀ alpha : CohAt H p,
      backward.cohomologyOperator
          (forward.cohomologyOperator alpha) =
        scalar • alpha

namespace GradedDefectRetraction

/-- **DEFECT ROUND-TRIP.**  The nonzero-scaled reciprocity law descends
verbatim to the quotient by the complete atomic cycle-class span. -/
theorem defect_roundtrip
    (R : GradedDefectRetraction V H p q)
    (z : DefectAt V H p) :
    R.backward.defectOperator (R.forward.defectOperator z) =
      R.scalar • z := by
  refine Submodule.Quotient.induction_on z ?_
  intro alpha
  rw [GradedCycleClassOperatorPair.defectOperator_mk,
      GradedCycleClassOperatorPair.defectOperator_mk,
      R.cohomology_roundtrip alpha]
  exact (Submodule.mkQ (AtomicSpanAt H p)).map_smul R.scalar alpha

/-- A forward genuine graded transport admitting a nonzero-scaled return is
injective on atomic defects.  Thus a nonzero Hodge defect cannot disappear
under the forward geometry. -/
theorem forward_defect_injective
    (R : GradedDefectRetraction V H p q) :
    Function.Injective R.forward.defectOperator := by
  intro x y hxy
  have h := congrArg R.backward.defectOperator hxy
  rw [R.defect_roundtrip x, R.defect_roundtrip y] at h
  have h' := congrArg (fun z => R.scalar⁻¹ • z) h
  simpa [smul_smul, R.scalar_ne_zero] using h'

/-- In particular, if the forward image of a defect vanishes, the original
defect already vanished. -/
theorem eq_zero_of_forward_eq_zero
    (R : GradedDefectRetraction V H p q)
    (z : DefectAt V H p)
    (hz : R.forward.defectOperator z = 0) :
    z = 0 := by
  apply R.forward_defect_injective
  simpa using hz

end GradedDefectRetraction

/-- The exact return law needed for the genuine projective principal-cut
successor.  The forward half is not supplied: it is the already-constructed
`GeometricCycleClassSpine.principalCutPair`. -/
structure PrincipalCutReturnLaw
    (G : GeometricCycleClassSpine V H)
    (p : Nat) where
  returnPair : GradedCycleClassOperatorPair V H (p + 1) p
  scalar : ℚ
  scalar_ne_zero : scalar ≠ 0
  cohomology_roundtrip :
    ∀ alpha : CohAt H p,
      returnPair.cohomologyOperator
          ((G.principalCutPair p).cohomologyOperator alpha) =
        scalar • alpha

namespace PrincipalCutReturnLaw

/-- Package a principal-cut return law as a general graded defect retraction. -/
noncomputable def toGradedDefectRetraction
    (R : PrincipalCutReturnLaw G p) :
    GradedDefectRetraction V H p (p + 1) where
  forward := G.principalCutPair p
  backward := R.returnPair
  scalar := R.scalar
  scalar_ne_zero := R.scalar_ne_zero
  cohomology_roundtrip := R.cohomology_roundtrip

/-- **PRINCIPAL-CUT DEFECT INJECTIVITY.**  A genuine nonzero-scaled return
transport makes the already-constructed projective cut injective on atomic
defects. -/
theorem principalCutDefectOperator_injective
    (R : PrincipalCutReturnLaw G p) :
    Function.Injective (principalCutDefectOperator G p) := by
  change Function.Injective ((G.principalCutPair p).defectOperator)
  exact R.toGradedDefectRetraction.forward_defect_injective

/-- Vanishing after one principal-cut step propagates backwards. -/
theorem defect_eq_zero_of_principalCut_eq_zero
    (R : PrincipalCutReturnLaw G p)
    (z : DefectAt V H p)
    (hz : principalCutDefectOperator G p z = 0) :
    z = 0 := by
  apply R.principalCutDefectOperator_injective
  simpa using hz

end PrincipalCutReturnLaw

/-- A genuine return law at every step of the projective principal-cut tower. -/
structure PrincipalCutReturnFamily
    (G : GeometricCycleClassSpine V H) where
  law : ∀ p : Nat, PrincipalCutReturnLaw G p

namespace PrincipalCutReturnFamily

/-- Every finite principal-cut defect iterate is injective under a return law
at each intermediate weight. -/
theorem principalCutDefectIterate_injective
    (F : PrincipalCutReturnFamily G)
    (p n : Nat) :
    Function.Injective (principalCutDefectIterate G p n) := by
  induction n with
  | zero =>
      simpa using (Function.injective_id : Function.Injective (id : DefectAt V H p → DefectAt V H p))
  | succ n ih =>
      rw [principalCutDefectIterate_succ]
      exact (F.law (p + n)).principalCutDefectOperator_injective.comp ih

/-- **BACKWARD EXTINCTION ALONG THE GRADED LADDER.**  If an n-step genuine
principal-cut image has zero atomic defect, then the starting defect was zero. -/
theorem defect_eq_zero_of_iterate_eq_zero
    (F : PrincipalCutReturnFamily G)
    (p n : Nat)
    (z : DefectAt V H p)
    (hz : principalCutDefectIterate G p n z = 0) :
    z = 0 := by
  apply F.principalCutDefectIterate_injective p n
  simpa using hz

end PrincipalCutReturnFamily

#check GradedDefectRetraction
#check GradedDefectRetraction.defect_roundtrip
#check GradedDefectRetraction.forward_defect_injective
#check PrincipalCutReturnLaw
#check PrincipalCutReturnLaw.principalCutDefectOperator_injective
#check PrincipalCutReturnFamily
#check PrincipalCutReturnFamily.principalCutDefectIterate_injective
#check PrincipalCutReturnFamily.defect_eq_zero_of_iterate_eq_zero

#print axioms GradedDefectRetraction.defect_roundtrip
#print axioms GradedDefectRetraction.forward_defect_injective
#print axioms PrincipalCutReturnLaw.principalCutDefectOperator_injective
#print axioms PrincipalCutReturnFamily.principalCutDefectIterate_injective
#print axioms PrincipalCutReturnFamily.defect_eq_zero_of_iterate_eq_zero

end GSTClassicalHodgeCrossWeightDefectRetraction
