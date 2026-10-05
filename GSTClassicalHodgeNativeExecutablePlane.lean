import GSTClassicalHodgeGradedCorrespondenceProgramOrbit
import GSTClassicalHodgeExactClayStatement

/-!
# GST CLASSICAL HODGE — NATIVE-ONLY EXECUTABLE GST PLANE

This is the strongest semantic cleanup of the plane route.

A graded correspondence/cut program has a completely geometric native-cycle
execution before any cohomological descent is chosen:

* correspondence atoms execute by their genuine native cycle operator;
* cuts execute by the geometry-built principal-cut successor;
* addition, scaling and composition execute literally.

The terminal geometric GST plane asks that for every Hodge basis sheet there
is one such native program whose ACTUAL final cycle class is that sheet.

No GeometricCycleClassSpine, no kernel-stability law, no point-Hodge law, no
cohomological operator, no ghost criterion and no Hodge-surjectivity premise
occurs in this definition.
-/

set_option maxHeartbeats 180000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry

namespace GSTClassicalHodgeNativeExecutablePlane

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgePrincipalCutSuccessorOperator
open GSTClassicalHodgeGradedCorrespondenceProgramOrbit
open GSTClassicalHodgeGradedCorrespondenceProgramOrbit.GradedCorrespondenceProgram
open GSTClassicalHodgeExactClayStatement

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Native execution of the full verified program syntax, independent of any
cohomological interpretation of principal cuts. -/
noncomputable def nativeEval :
    {p q : Nat} → GradedCorrespondenceProgram V H p q →
      codimensionCycles V.X p →ₗ[ℚ] codimensionCycles V.X q
  | _, _, .id _ => LinearMap.id
  | _, _, .correspondence E => E.cycleOperator
  | _, _, .cut p => successorNativeOperator V p
  | _, _, .add A B => nativeEval A + nativeEval B
  | _, _, .smul a A => a • nativeEval A
  | _, _, .comp A B => (nativeEval B).comp (nativeEval A)

/-- Native geometric origin. -/
noncomputable def originCycle : codimensionCycles V.X 0 :=
  GSTClassicalHodgeCodimensionZeroFundamentalCycle.codimensionZeroFundamentalCycle V

/-- Native output of one root-to-weight program. -/
noncomputable def nativeOutput
    {q : Nat}
    (P : GradedCorrespondenceProgram V H 0 q) :
    codimensionCycles V.X q :=
  nativeEval P (originCycle (V := V))

/-- **NATIVE-ONLY EXECUTABLE GST PLANE COMPLETENESS.**
Every genuine rational Hodge basis sheet is the actual cycle class of the
native output of one verified correspondence/cut program from the canonical
geometric origin. -/
def NativeExecutableGSTPlaneCompleteness : Prop :=
  ∀ q : Nat, ∀ j : ClassicalHodgeBasisIndex V H q,
    ∃ P : GradedCorrespondenceProgram V H 0 q,
      H.cycleClass q (nativeOutput P) =
        (classicalHodgeBasis V H q j).1

/-- Choose the native program output for one target sheet. -/
noncomputable def basisCycle
    (hplane : NativeExecutableGSTPlaneCompleteness (V := V) (H := H))
    (q : Nat)
    (j : ClassicalHodgeBasisIndex V H q) :
    codimensionCycles V.X q :=
  nativeOutput (Classical.choose (hplane q j))

/-- The chosen program output has exactly the requested basis class. -/
theorem basisCycle_spec
    (hplane : NativeExecutableGSTPlaneCompleteness (V := V) (H := H))
    (q : Nat)
    (j : ClassicalHodgeBasisIndex V H q) :
    H.cycleClass q (basisCycle hplane q j) =
      (classicalHodgeBasis V H q j).1 := by
  exact Classical.choose_spec (hplane q j)

/-- Reconstruct an arbitrary rational Hodge class by the finite support of its
basis coordinates and the native program cycles for those sheets. -/
noncomputable def targetCycle
    (hplane : NativeExecutableGSTPlaneCompleteness (V := V) (H := H))
    (q : Nat)
    (alpha : ClassicalHodgeFiber V H q) :
    codimensionCycles V.X q :=
  ∑ j ∈ ((classicalHodgeBasis V H q).repr alpha).support,
    ((classicalHodgeBasis V H q).repr alpha j) •
      basisCycle hplane q j

/-- **FINITE NATIVE COLLAPSE SPECIFICATION.**
The target-cycle constructor lands exactly on the requested Hodge class. -/
theorem targetCycle_spec
    (hplane : NativeExecutableGSTPlaneCompleteness (V := V) (H := H))
    (q : Nat)
    (alpha : ClassicalHodgeFiber V H q) :
    H.cycleClass q (targetCycle hplane q alpha) = alpha.1 := by
  unfold targetCycle
  rw [map_sum]
  simp only [LinearMap.map_smul]
  rw [show alpha =
      ∑ j ∈ ((classicalHodgeBasis V H q).repr alpha).support,
        ((classicalHodgeBasis V H q).repr alpha j) •
          classicalHodgeBasis V H q j by
    exact (classicalHodgeBasis V H q).sum_repr alpha]
  apply congrArg Subtype.val
  apply Finset.sum_congr rfl
  intro j hj
  apply Subtype.ext
  simp [basisCycle_spec hplane q j]

/-- **NATIVE EXECUTABLE GST PLANE ⇒ EXACT STAGE-2G HODGE.** -/
theorem hodge_of_nativeExecutableGSTPlane
    (hplane : NativeExecutableGSTPlaneCompleteness (V := V) (H := H)) :
    BigradedBettiHodgeStatement V H := by
  intro q alpha halpha
  let alphaH : ClassicalHodgeFiber V H q := ⟨alpha, halpha⟩
  exact ⟨targetCycle hplane q alphaH, targetCycle_spec hplane q alphaH⟩

/-- Exact rational-algebraic form. -/
theorem rationalHodge_of_nativeExecutableGSTPlane
    (hplane : NativeExecutableGSTPlaneCompleteness (V := V) (H := H)) :
    EveryHodgeClassIsRationalAlgebraic H :=
  (everyHodgeClassIsRationalAlgebraic_iff_stage2G H).2
    (hodge_of_nativeExecutableGSTPlane hplane)

/-- Literal finite rational-combination form. -/
theorem finiteRationalCombination_of_nativeExecutableGSTPlane
    (hplane : NativeExecutableGSTPlaneCompleteness (V := V) (H := H)) :
    EveryHodgeClassIsFiniteRationalCombination H :=
  (rationalAlgebraic_iff_finiteRationalCombination H).1
    (rationalHodge_of_nativeExecutableGSTPlane hplane)

#check nativeEval
#check NativeExecutableGSTPlaneCompleteness
#check basisCycle
#check basisCycle_spec
#check targetCycle
#check targetCycle_spec
#check hodge_of_nativeExecutableGSTPlane
#check rationalHodge_of_nativeExecutableGSTPlane
#check finiteRationalCombination_of_nativeExecutableGSTPlane

#print axioms basisCycle_spec
#print axioms targetCycle_spec
#print axioms hodge_of_nativeExecutableGSTPlane
#print axioms finiteRationalCombination_of_nativeExecutableGSTPlane

end GSTClassicalHodgeNativeExecutablePlane
