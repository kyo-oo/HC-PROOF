import GSTClassicalHodgePrincipalCutFlagNativeReturn
import GSTClassicalHodgeFiberedSeparatorDefect
import GSTClassicalHodgeFiberedDefectEquivariance

/-!
# GST CLASSICAL HODGE — LIMITLESS SINGLETON FLAG NORMAL

The final first-ghost attack only needs one live geometric seed.  On that
single seed there is no reason to retain an arbitrary finite source chart.
Taking the principal-cut incidence chart to be the singleton `{x}` removes all
off-diagonal cross-talk exactly:

    K_x^t K_x [x] = lambda_x [x].

For an exact live principal cut, `lambda_x` is nonzero.  Thus the normalized
native round trip is literally the identity on the distinguished source cycle.

The second half of this file places arbitrary native motions into the existing
multiplicity-preserving fibered limitless cosmos.  A basis separator kills the
cycle class of every genuine native output.  Consequently, on an atom in the
obstructed Hodge sheet, the separator reads the fibered defect only through the
retained multiplicity label.  The read is scaled by the exact native transition
mass, and dividing by a nonzero transition mass preserves the obstruction
scalar exactly.

This is deliberately a single-seed statement.  It does not identify a ghost
basis vector with an algebraic cycle and it does not assert a global Hodge
matrix-unit descent.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeLimitlessSingletonFlagNormal

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgePrincipalCutSuccessorOperator
open GSTClassicalHodgePrincipalCutIncidenceTransposeCosmology
open GSTClassicalHodgePrincipalCutFlagNativeReturn
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeFiberedNativePullback
open GSTClassicalHodgeFiberedNativeOperatorLift
open GSTClassicalHodgeFiberedCycleClassDefect
open GSTClassicalHodgeFiberedDefectEquivariance
open GSTClassicalHodgeProjectiveCorrespondenceAlgebra
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeAtomicAnnihilator
open GSTClassicalHodgeSingleSheetCrown

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- The finite incidence transpose has no coefficient outside its chosen source
chart. -/
theorem localSuccessorTranspose_apply_of_not_mem
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (sigma : Finset (CodimensionPoint V.X p))
    (psi : FiniteCodimensionPresentation V.X (p + 1))
    (z : CodimensionPoint V.X p)
    (hz : z ∉ sigma) :
    localSuccessorTranspose V p sigma psi z = 0 := by
  classical
  simp [localSuccessorTranspose, localTransposeColumn, hz]

/-- Hence the local normal also has no output outside the chosen source chart. -/
theorem localSuccessorNormal_apply_of_not_mem
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (sigma : Finset (CodimensionPoint V.X p))
    (phi : FiniteCodimensionPresentation V.X p)
    (z : CodimensionPoint V.X p)
    (hz : z ∉ sigma) :
    localSuccessorNormal V p sigma phi z = 0 := by
  rw [localSuccessorNormal, LinearMap.comp_apply]
  exact localSuccessorTranspose_apply_of_not_mem
    V p sigma (successorPresentationOperator V p phi) z hz

/-- On the singleton source chart the general off-diagonal correction vanishes
as an entire presentation, not merely at the distinguished coordinate. -/
theorem successorCrossTalk_singleton_eq_zero
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p) :
    successorCrossTalk V p {x} x = 0 := by
  apply Finsupp.ext
  intro z
  by_cases hzx : z = x
  · subst z
    exact successorCrossTalk_apply_self V p {x} x (by simp)
  · rw [successorCrossTalk, Finsupp.sub_apply]
    have hz : z ∉ ({x} : Finset (CodimensionPoint V.X p)) := by
      simp [hzx]
    rw [localSuccessorNormal_apply_of_not_mem
      V p {x} (Finsupp.single x (1 : ℚ)) z hz]
    simp [hzx]

/-- **SINGLETON GRAM NORMAL FORM.**  The principal-cut normal is exactly its
self-energy scalar on the one-seed chart. -/
theorem localSuccessorNormal_singleton_eq_selfEnergy
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p) :
    localSuccessorNormal V p {x} (Finsupp.single x (1 : ℚ)) =
      successorSelfEnergy V p x • Finsupp.single x (1 : ℚ) := by
  rw [localSuccessorNormal_decomposition]
  rw [successorCrossTalk_singleton_eq_zero]
  simp

/-- Native-cycle form of the singleton Gram identity. -/
theorem localFlagNormalNative_singleton_eq_selfEnergy
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p) :
    localFlagNormalNative V p {x} (codimensionPointCycle V.X p x) =
      successorSelfEnergy V p x • codimensionPointCycle V.X p x := by
  rw [localFlagNormalNative_point]
  rw [localSuccessorNormal_singleton_eq_selfEnergy]
  rw [map_smul]
  simp [realizeFiniteCodimensionPresentation_single]

/-- Whenever the self-energy is nonzero, the mass-normalized native flag
round-trip fixes the distinguished geometric seed exactly. -/
theorem normalized_localFlagNormalNative_singleton_fixes_point
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hlambda : successorSelfEnergy V p x ≠ 0) :
    ((successorSelfEnergy V p x)⁻¹ • localFlagNormalNative V p {x})
        (codimensionPointCycle V.X p x) =
      codimensionPointCycle V.X p x := by
  simp [localFlagNormalNative_singleton_eq_selfEnergy,
    smul_smul, hlambda]

/-- Exact live version: the existing exact-stratum/nonempty hypotheses produce
both the nonzero normalization and the fixed-point round trip. -/
theorem normalized_singleton_flag_live_crown
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hExact :
      GSTClassicalHodgeRelativeSuccessorExactStratum.RelativeSuccessorAmbientExact
        V p x)
    (hNonempty : (relativeCodimensionOneFinset V x.1).Nonempty) :
    let lambda := successorSelfEnergy V p x
    lambda ≠ 0 ∧
      (lambda⁻¹ • localFlagNormalNative V p {x})
          (codimensionPointCycle V.X p x) =
        codimensionPointCycle V.X p x := by
  dsimp
  have hlambda := successorSelfEnergy_ne_zero_of_exact_nonempty
    V p x hExact hNonempty
  exact ⟨hlambda,
    normalized_localFlagNormalNative_singleton_fixes_point V p x hlambda⟩

/-- A basis separator kills the cycle class of every genuine native cycle, not
only the individual point generators. -/
theorem separator_kills_native_cycleClass
    {i : ClassicalHodgeBasisIndex V H p}
    (Sep : BasisAtomicSeparator V H p i)
    (Z : codimensionCycles V.X p) :
    Sep.detector (H.cycleClass p Z) = 0 := by
  have hker :
      pointCycleClassSpan p (H.cycleClass p) ≤ LinearMap.ker Sep.detector :=
    (annihilatesPointCycles_iff_atomicSpan_le_ker
      p (H.cycleClass p) Sep.detector).mp Sep.annihilates_atoms
  apply hker
  rw [← smoothProjective_cycleClass_range_eq_atomic_span V H p]
  exact ⟨Z, rfl⟩

/-- **FIBERED LIMITLESS SEPARATOR TRANSPORT LAW.**
Lift any genuine native operator while retaining one obstructed Hodge sheet.
The native part is invisible to the separator, so the complete defect read is
exactly minus the transition mass times the fixed sheet reading. -/
theorem separator_reads_liftNativeOperator_atom
    {i : ClassicalHodgeBasisIndex V H p}
    (Sep : BasisAtomicSeparator V H p i)
    (A : Module.End ℚ (codimensionCycles V.X p))
    (x : CodimensionPoint V.X p) :
    Sep.detector
      (fiberedCycleClassDefect (V := V) (H := H) (p := p)
        (liftNativeOperator A (atom V H p i x))) =
      - pointTransitionMass A x *
        Sep.detector (classicalHodgeBasis V H p i).1 := by
  rw [liftNativeOperator_atom]
  unfold fiberedCycleClassDefect fiberedNativeCycleClass fiberedHodgeAmbient
  rw [LinearMap.sub_apply]
  simp only [LinearMap.comp_apply]
  rw [toNativeCycle_labelPresentation]
  rw [operatorPointPresentation_realize]
  rw [fiberedHodgeClass_labelPresentation]
  rw [map_sub]
  rw [separator_kills_native_cycleClass Sep]
  rw [map_smul]
  simp [pointTransitionMass, smul_eq_mul]

/-- Dividing by any nonzero native transition mass makes the obstruction read
strictly invariant.  This is the scalar form of recoordination/geometry
independence needed by a one-seed limitless worldtrace attack. -/
theorem separator_reads_massNormalized_lift_eq_atom
    {i : ClassicalHodgeBasisIndex V H p}
    (Sep : BasisAtomicSeparator V H p i)
    (A : Module.End ℚ (codimensionCycles V.X p))
    (x : CodimensionPoint V.X p)
    (hmass : pointTransitionMass A x ≠ 0) :
    Sep.detector
      (fiberedCycleClassDefect (V := V) (H := H) (p := p)
        ((pointTransitionMass A x)⁻¹ •
          liftNativeOperator A (atom V H p i x))) =
      Sep.detector
        (fiberedCycleClassDefect (V := V) (H := H) (p := p)
          (atom V H p i x)) := by
  simp only [LinearMap.map_smul, smul_eq_mul]
  rw [separator_reads_liftNativeOperator_atom Sep A x]
  rw [GSTClassicalHodgeFiberedSeparatorDefect.separator_reads_atom_defect Sep x]
  field_simp [hmass]

#check localSuccessorNormal_singleton_eq_selfEnergy
#check localFlagNormalNative_singleton_eq_selfEnergy
#check normalized_singleton_flag_live_crown
#check separator_reads_liftNativeOperator_atom
#check separator_reads_massNormalized_lift_eq_atom

#print axioms localSuccessorNormal_singleton_eq_selfEnergy
#print axioms localFlagNormalNative_singleton_eq_selfEnergy
#print axioms normalized_singleton_flag_live_crown
#print axioms separator_reads_liftNativeOperator_atom
#print axioms separator_reads_massNormalized_lift_eq_atom

end GSTClassicalHodgeLimitlessSingletonFlagNormal
