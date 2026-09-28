import GSTClassicalHodgeQuasiFinitePointCorrespondence
import GSTClassicalHodgeNativeOperatorCohomologyRealization
import GSTCompactNativeCyclePresentation

/-!
# GST CLASSICAL HODGE — QUASI-FINITE CORRESPONDENCE OPERATOR

A quasi-finite point correspondence already produces an honest finite target
presentation for every source generic point.  This file linearly extends that
geometric relation to all native algebraic cycles on a smooth projective
carrier.

No ambient cohomological action is chosen.  The only descent condition is the
mathematically necessary one: the resulting native operator must preserve the
kernel of the actual cycle-class map.  Once that holds, the existing native
operator realization theorem constructs the ambient Betti operator and its
exact cycle-class commuting square automatically.

Thus the external geometry required from a multivalued correspondence is now
separated into:

1. actual finite point geometry (already constructed from the left fibre);
2. kernel stability of the induced native cycle operator.

There is no whole-Hodge action hypothesis anywhere in this layer.
-/

set_option maxHeartbeats 90000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicGeometry

namespace GSTClassicalHodgeQuasiFiniteCorrespondenceOperator

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTCompactNativeCyclePresentation
open GSTClassicalHodgeQuasiFinitePointCorrespondence
open GSTClassicalHodgeNativeOperatorCohomologyRealization

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Linear extension of the finite multivalued point relation to finite native
presentations. -/
noncomputable def presentationOperator
    (C : QuasiFinitePointCorrespondence V.X p) :
    FiniteCodimensionPresentation V.X p →ₗ[ℚ]
      FiniteCodimensionPresentation V.X p :=
  Finsupp.total (CodimensionPoint V.X p)
    (FiniteCodimensionPresentation V.X p) ℚ C.transition

@[simp]
theorem presentationOperator_single
    (C : QuasiFinitePointCorrespondence V.X p)
    (x : CodimensionPoint V.X p) :
    presentationOperator C (Finsupp.single x 1) = C.transition x := by
  simp [presentationOperator]

/-- Native cycle operator obtained directly from the genuine finite relation. -/
noncomputable def nativeCycleOperator
    (C : QuasiFinitePointCorrespondence V.X p) :
    codimensionCycles V.X p →ₗ[ℚ] codimensionCycles V.X p := by
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  exact (realizePresentationLinear V.X p).comp
    ((presentationOperator C).comp
      (presentationOfNativeCycleLinear V.X p))

/-- On one genuine point generator the native operator is exactly the realized
finite correspondence fibre. -/
@[simp]
theorem nativeCycleOperator_point
    (C : QuasiFinitePointCorrespondence V.X p)
    (x : CodimensionPoint V.X p) :
    nativeCycleOperator C (codimensionPointCycle V.X p x) =
      realizeFiniteCodimensionPresentation V.X p (C.transition x) := by
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  simp [nativeCycleOperator, presentationOperator,
    realizePresentationLinear_apply,
    presentationOfNativeCycleLinear,
    presentationOfNativeCycle,
    codimensionPointCycle]

/-- Exact descent condition for a quasi-finite correspondence: equivalent
cycle presentations must remain equivalent after applying the multivalued
geometric relation. -/
def CorrespondenceKernelStable
    (C : QuasiFinitePointCorrespondence V.X p) : Prop :=
  KernelStable (H := H) (nativeCycleOperator C)

/-- A kernel-stable quasi-finite correspondence acquires an ambient Betti
operator automatically; no Hodge-fibre action is supplied. -/
noncomputable def operatorPair
    (C : QuasiFinitePointCorrespondence V.X p)
    (hC : CorrespondenceKernelStable (H := H) C) :
    GSTClassicalHodgeCycleOperatorNaturality.CycleClassOperatorPair V H p :=
  toCycleClassOperatorPair (nativeCycleOperator C) hC

/-- Exact cycle-class commuting square of the derived correspondence action. -/
theorem operatorPair_naturality
    (C : QuasiFinitePointCorrespondence V.X p)
    (hC : CorrespondenceKernelStable (H := H) C)
    (Z : codimensionCycles V.X p) :
    H.cycleClass p ((operatorPair C hC).cycleOperator Z) =
      (operatorPair C hC).cohomologyOperator (H.cycleClass p Z) := by
  exact (operatorPair C hC).cycleClass_cycleOperator Z

/-- On point generators, the cohomological action is exactly the cycle class
of the finite geometric correspondence fibre. -/
theorem operatorPair_point
    (C : QuasiFinitePointCorrespondence V.X p)
    (hC : CorrespondenceKernelStable (H := H) C)
    (x : CodimensionPoint V.X p) :
    (operatorPair C hC).cohomologyOperator
        (H.cycleClass p (codimensionPointCycle V.X p x)) =
      H.cycleClass p
        (realizeFiniteCodimensionPresentation V.X p (C.transition x)) := by
  rw [← operatorPair_naturality C hC]
  rw [nativeCycleOperator_point C x]
  rfl

/-- Point-lift formulation: every kernel-stable quasi-finite correspondence is
independently native-natural in exactly the sense used by the minimal-ghost
extinction theorem. -/
theorem operatorPair_hasNativePointLifts
    (C : QuasiFinitePointCorrespondence V.X p)
    (hC : CorrespondenceKernelStable (H := H) C) :
    GSTClassicalHodgeNativeGeneratorNaturality.HasNativePointLifts
      (p := p) (cl := H.cycleClass p)
      (operatorPair C hC).cohomologyOperator := by
  intro x
  refine ⟨realizeFiniteCodimensionPresentation V.X p (C.transition x), ?_⟩
  exact (operatorPair_point C hC x).symm

#check presentationOperator
#check nativeCycleOperator
#check nativeCycleOperator_point
#check CorrespondenceKernelStable
#check operatorPair
#check operatorPair_naturality
#check operatorPair_point
#check operatorPair_hasNativePointLifts

#print axioms nativeCycleOperator_point
#print axioms operatorPair_naturality
#print axioms operatorPair_point
#print axioms operatorPair_hasNativePointLifts

end GSTClassicalHodgeQuasiFiniteCorrespondenceOperator
