import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Isomorphisms
import GSTClassicalHodgePrincipalCutFlagHomologicalDescent
import GSTClassicalHodgeCrossWeightNativePropagation

/-!
# GST CLASSICAL HODGE — PRINCIPAL-CUT FLAG COHOMOLOGICAL DESCENT

The homological-descent layer proves that the native reverse principal-cut flag
annihilates the kernel of the genuine target cycle-class map as soon as the
local incidence/intersection projection formula is available.

That kernel statement is exactly the universal algebraic condition required to
construct a cohomological realization of the reverse flag.  This file performs
that construction canonically on the actual cycle-class range:

  cycles / ker(cycleClass)  ~=  range(cycleClass)

by Mathlib's first isomorphism theorem.  The reverse native flag descends to the
quotient, is transported to the cycle-class range, then composed with the
source cycle-class map.  Since rational cohomology is a vector space, the
resulting map on the cycle-class range extends linearly to the full ambient
cohomology group.

The chosen extension is irrelevant to algebraic inputs: on every actual target
cycle class it is proved to equal the cycle class of the native reverse flag.
Hence the projection formula produces a genuine cross-weight
`GradedCycleClassOperatorPair` for the reverse flag.

No Hodge preservation, Hodge surjectivity, target basis representative,
projective visibility, or ghost-specific action is assumed.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgePrincipalCutFlagCohomologicalDescent

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgePrincipalCutFlagNativeReturn
open GSTClassicalHodgePrincipalCutFlagHomologicalDescent
open GSTClassicalHodgeCrossWeightNativePropagation

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

abbrev SourceCohomology
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) :=
  RationalSingularCohomology H.analytification (2 * p)

namespace PrincipalCutFlagProjectionFormula

/-- Reverse flag descended to the quotient by homological equivalence. -/
noncomputable def reverseFlagOnCycleQuotient
    {sigma : Finset (CodimensionPoint V.X p)}
    (P : PrincipalCutFlagProjectionFormula V H p sigma) :
    (codimensionCycles V.X (p + 1) ⧸
      LinearMap.ker (H.cycleClass (p + 1))) →ₗ[ℚ]
        codimensionCycles V.X p :=
  (LinearMap.ker (H.cycleClass (p + 1))).liftQ
    (localTransposeNativeOperator V p sigma)
    P.cycleClass_kernel_le_reverseFlag_kernel

/-- On a quotient class represented by an actual target cycle, the descended
operator is literally the native reverse flag. -/
@[simp]
theorem reverseFlagOnCycleQuotient_mk
    {sigma : Finset (CodimensionPoint V.X p)}
    (P : PrincipalCutFlagProjectionFormula V H p sigma)
    (Z : codimensionCycles V.X (p + 1)) :
    P.reverseFlagOnCycleQuotient (Submodule.Quotient.mk Z) =
      localTransposeNativeOperator V p sigma Z := by
  rfl

/-- Transport the quotient reverse flag across the canonical first-isomorphism
identification with the genuine target cycle-class range. -/
noncomputable def reverseFlagOnCycleClassRange
    {sigma : Finset (CodimensionPoint V.X p)}
    (P : PrincipalCutFlagProjectionFormula V H p sigma) :
    LinearMap.range (H.cycleClass (p + 1)) →ₗ[ℚ]
      codimensionCycles V.X p :=
  P.reverseFlagOnCycleQuotient.comp
    ((H.cycleClass (p + 1)).quotKerEquivRange.symm.toLinearMap)

/-- Evaluation on an honest cycle class recovers the native reverse flag
exactly. -/
theorem reverseFlagOnCycleClassRange_apply_cycleClass
    {sigma : Finset (CodimensionPoint V.X p)}
    (P : PrincipalCutFlagProjectionFormula V H p sigma)
    (Z : codimensionCycles V.X (p + 1)) :
    P.reverseFlagOnCycleClassRange
        ⟨H.cycleClass (p + 1) Z, ⟨Z, rfl⟩⟩ =
      localTransposeNativeOperator V p sigma Z := by
  unfold reverseFlagOnCycleClassRange
  rw [LinearMap.comp_apply]
  rw [LinearMap.quotKerEquivRange_symm_apply_image]
  rfl

/-- Cohomological return on the actual algebraic cycle-class range. -/
noncomputable def reverseFlagRangeCohomology
    {sigma : Finset (CodimensionPoint V.X p)}
    (P : PrincipalCutFlagProjectionFormula V H p sigma) :
    LinearMap.range (H.cycleClass (p + 1)) →ₗ[ℚ]
      SourceCohomology V H p :=
  (H.cycleClass p).comp P.reverseFlagOnCycleClassRange

/-- On every actual target cycle class, the range-level cohomological return is
the genuine source cycle class of the native reverse flag. -/
theorem reverseFlagRangeCohomology_apply_cycleClass
    {sigma : Finset (CodimensionPoint V.X p)}
    (P : PrincipalCutFlagProjectionFormula V H p sigma)
    (Z : codimensionCycles V.X (p + 1)) :
    P.reverseFlagRangeCohomology
        ⟨H.cycleClass (p + 1) Z, ⟨Z, rfl⟩⟩ =
      H.cycleClass p (localTransposeNativeOperator V p sigma Z) := by
  unfold reverseFlagRangeCohomology
  rw [LinearMap.comp_apply]
  rw [P.reverseFlagOnCycleClassRange_apply_cycleClass Z]

/-- Extend the canonically descended return from the actual cycle-class range
to the full target rational cohomology vector space.  No property of this
extension outside the algebraic range is used in the naturality theorem. -/
noncomputable def reverseFlagCohomologyOperator
    {sigma : Finset (CodimensionPoint V.X p)}
    (P : PrincipalCutFlagProjectionFormula V H p sigma) :
    TargetCohomology V H p →ₗ[ℚ] SourceCohomology V H p :=
  Classical.choose (LinearMap.exists_extend P.reverseFlagRangeCohomology)

/-- The chosen ambient extension agrees with the canonical range-level return. -/
theorem reverseFlagCohomologyOperator_comp_rangeSubtype
    {sigma : Finset (CodimensionPoint V.X p)}
    (P : PrincipalCutFlagProjectionFormula V H p sigma) :
    P.reverseFlagCohomologyOperator.comp
        (LinearMap.range (H.cycleClass (p + 1))).subtype =
      P.reverseFlagRangeCohomology :=
  Classical.choose_spec (LinearMap.exists_extend P.reverseFlagRangeCohomology)

/-- **REVERSE FLAG CYCLE-CLASS NATURALITY.**
The ambient cohomological return produced from homological descent agrees with
the native reverse flag on every genuine algebraic cycle. -/
theorem reverseFlag_cycleClass_natural
    {sigma : Finset (CodimensionPoint V.X p)}
    (P : PrincipalCutFlagProjectionFormula V H p sigma)
    (Z : codimensionCycles V.X (p + 1)) :
    H.cycleClass p (localTransposeNativeOperator V p sigma Z) =
      P.reverseFlagCohomologyOperator (H.cycleClass (p + 1) Z) := by
  have hcomp := LinearMap.congr_fun
    P.reverseFlagCohomologyOperator_comp_rangeSubtype
    ⟨H.cycleClass (p + 1) Z, ⟨Z, rfl⟩⟩
  have hrange := P.reverseFlagRangeCohomology_apply_cycleClass Z
  simpa [hrange] using hcomp.symm

/-- **COHOMOLOGICALLY DESCENDED REVERSE PRINCIPAL-CUT FLAG.**
The single local incidence/intersection projection formula canonically yields a
genuine cross-weight native/cohomological operator pair from weight `p+1` back
to weight `p`. -/
noncomputable def toGradedCycleClassOperatorPair
    {sigma : Finset (CodimensionPoint V.X p)}
    (P : PrincipalCutFlagProjectionFormula V H p sigma) :
    GradedCycleClassOperatorPair V H (p + 1) p where
  cycleOperator := localTransposeNativeOperator V p sigma
  cohomologyOperator := P.reverseFlagCohomologyOperator
  cycleClass_natural := fun Z => P.reverseFlag_cycleClass_natural Z

/-- The operator-pair cycle face is definitionally the incidence-built native
reverse flag. -/
@[simp]
theorem toGradedCycleClassOperatorPair_cycleOperator
    {sigma : Finset (CodimensionPoint V.X p)}
    (P : PrincipalCutFlagProjectionFormula V H p sigma) :
    P.toGradedCycleClassOperatorPair.cycleOperator =
      localTransposeNativeOperator V p sigma := rfl

/-- Crown: projection formula -> homological descent -> genuine cohomological
reverse flag with exact cycle-class naturality. -/
theorem cohomological_descent_crown
    {sigma : Finset (CodimensionPoint V.X p)}
    (P : PrincipalCutFlagProjectionFormula V H p sigma) :
    ∀ Z : codimensionCycles V.X (p + 1),
      H.cycleClass p
          (P.toGradedCycleClassOperatorPair.cycleOperator Z) =
        P.toGradedCycleClassOperatorPair.cohomologyOperator
          (H.cycleClass (p + 1) Z) := by
  intro Z
  exact P.reverseFlag_cycleClass_natural Z

end PrincipalCutFlagProjectionFormula

#check PrincipalCutFlagProjectionFormula.reverseFlagOnCycleQuotient
#check PrincipalCutFlagProjectionFormula.reverseFlagOnCycleClassRange
#check PrincipalCutFlagProjectionFormula.reverseFlagRangeCohomology
#check PrincipalCutFlagProjectionFormula.reverseFlagCohomologyOperator
#check PrincipalCutFlagProjectionFormula.reverseFlag_cycleClass_natural
#check PrincipalCutFlagProjectionFormula.toGradedCycleClassOperatorPair
#check PrincipalCutFlagProjectionFormula.cohomological_descent_crown

#print axioms PrincipalCutFlagProjectionFormula.reverseFlag_cycleClass_natural
#print axioms PrincipalCutFlagProjectionFormula.toGradedCycleClassOperatorPair
#print axioms PrincipalCutFlagProjectionFormula.cohomological_descent_crown

end GSTClassicalHodgePrincipalCutFlagCohomologicalDescent
