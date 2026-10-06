import GSTClassicalHodgeCoherentNativeDescent
import GSTClassicalHodgeCommonClassPlaneReduction

/-!
# GST CLASSICAL HODGE — COHERENT NATIVE GHOST OBSTRUCTION

The coherent native descent theorem constructs an ambient cohomology action
from two finite native laws: agreement of all labelled columns after actual
cycle class, and preservation of the native cycle-class kernel by one anchor
column.  This file computes what every such action does at a genuine native
Hodge seed in the presence of a hypothetical omniversal separator ghost.

The answer is rigid.  Its value on the seed remains the class of an actual
native cycle and is therefore invisible to the ghost.  The GST matrix-unit
target selected by that ghost has a nonzero detector reading.  Consequently
the detector of their discrepancy is exactly

    - sourceCoefficient * detector(detectedBasisSheet),

and is nonzero.

No target cycle representative, strict relation packet, common-class plane,
Hodge completeness premise, or desired source-to-target action equation is
used.  The theorem closes the possibility that routing, label cancellation,
finite tensor coherence, or a rational-linear ambient extension secretly
supplies the missing strict geometric carrier.
-/

set_option maxHeartbeats 180000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeCoherentNativeGhostObstruction

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeFiberedNativePullback
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeGradedGeometricProgramOrbit
open GSTClassicalHodgeSynchronizedDefectOrbit
open GSTClassicalHodgeOmniversalSeparatorGhostCrown
open GSTClassicalHodgeNativePointRelationDescent
open GSTClassicalHodgeCoherentNativeDescent

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- An omniversal ghost annihilates the actual class of every genuine native
cycle in its own weight.  This is the identity-program face of the ghost law. -/
theorem ghost_kills_nativeCycleClass
    (G : GeometricCycleClassSpine V H)
    (E : OmniversalSeparatorGhost G)
    (Z : codimensionCycles V.X E.weight) :
    E.separator.detector (H.cycleClass E.weight Z) = 0 := by
  have hkill :=
    E.kills_all_native_programs E.weight
      (GradedGeometricProgram.id E.weight) Z
  simpa [GradedGeometricProgram.cohomologyEval,
    GradedGeometricProgram.toPair,
    GradedCycleClassOperatorPair.idPair] using hkill

/-- Every ambient action which genuinely descends from a labelled native
operator remains invisible to the ghost on a genuine native seed.

The statement is deliberately local to the actual cycle-class range.  It
makes no claim about the chosen ambient extension on non-native classes. -/
theorem ghost_kills_descendingAction_on_seed
    (G : GeometricCycleClassSpine V H)
    (E : OmniversalSeparatorGhost G)
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := E.weight))
    (i₀ : ClassicalHodgeBasisIndex V H E.weight)
    (U : Module.End ℚ (FiberedNativeAddress V H E.weight))
    (T : Module.End ℚ
      (RationalSingularCohomology H.analytification (2 * E.weight)))
    (hT :
      (((H.cycleClass E.weight).comp
          (toNativeCycle V H E.weight)).comp U) =
        T.comp ((H.cycleClass E.weight).comp
          (toNativeCycle V H E.weight))) :
    E.separator.detector (T S.hodge.1) = 0 := by
  have hcomm := LinearMap.congr_fun hT (nativeSection i₀ S.cycle)
  have haction :
      T S.hodge.1 =
        H.cycleClass E.weight
          (toNativeCycle V H E.weight (U (nativeSection i₀ S.cycle))) := by
    simpa only [LinearMap.comp_apply, toNativeCycle_nativeSection,
      S.class_eq] using hcomm.symm
  rw [haction]
  exact ghost_kills_nativeCycleClass G E _

/-- **EXACT COHERENT-NATIVE GST BRANCH DEFECT.**

The detector component of the discrepancy between an arbitrary descending
native action and the ghost-selected matrix-unit branch is exactly minus the
live source coefficient times the detector's nonzero target reading. -/
theorem ghostSeedTarget_descendingAction_mismatch_formula
    (G : GeometricCycleClassSpine V H)
    (E : OmniversalSeparatorGhost G)
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := E.weight))
    (i₀ : ClassicalHodgeBasisIndex V H E.weight)
    (U : Module.End ℚ (FiberedNativeAddress V H E.weight))
    (T : Module.End ℚ
      (RationalSingularCohomology H.analytification (2 * E.weight)))
    (hT :
      (((H.cycleClass E.weight).comp
          (toNativeCycle V H E.weight)).comp U) =
        T.comp ((H.cycleClass E.weight).comp
          (toNativeCycle V H E.weight))) :
    E.separator.detector
        (T S.hodge.1 -
          (hodgeMatrixUnit S.sourceIndex E.sheet S.hodge).1) =
      -(hodgeCoordinate S.sourceIndex S.hodge *
        E.separator.detector
          (classicalHodgeBasis V H E.weight E.sheet).1) := by
  have hkill := ghost_kills_descendingAction_on_seed G E S i₀ U T hT
  have hbranch := congrArg Subtype.val
    (hodgeMatrixUnit_apply S.sourceIndex E.sheet S.hodge)
  rw [map_sub, hkill, hbranch, map_smul]
  simp only [zero_sub, smul_eq_mul]

/-- The coherent-native branch defect is nonzero for every descending ambient
action. -/
theorem ghostSeedTarget_descendingAction_mismatch_ne_zero
    (G : GeometricCycleClassSpine V H)
    (E : OmniversalSeparatorGhost G)
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := E.weight))
    (i₀ : ClassicalHodgeBasisIndex V H E.weight)
    (U : Module.End ℚ (FiberedNativeAddress V H E.weight))
    (T : Module.End ℚ
      (RationalSingularCohomology H.analytification (2 * E.weight)))
    (hT :
      (((H.cycleClass E.weight).comp
          (toNativeCycle V H E.weight)).comp U) =
        T.comp ((H.cycleClass E.weight).comp
          (toNativeCycle V H E.weight))) :
    E.separator.detector
      (T S.hodge.1 -
        (hodgeMatrixUnit S.sourceIndex E.sheet S.hodge).1) ≠ 0 := by
  rw [ghostSeedTarget_descendingAction_mismatch_formula G E S i₀ U T hT]
  apply neg_ne_zero.mpr
  apply mul_ne_zero
  · exact S.sourceCoefficient_ne_zero
  · exact E.separator.detects_basis

/-- No cycle-class-descending native action sends the genuine seed to the
matrix-unit branch target detected by a surviving ghost. -/
theorem ghostSeedTarget_descendingAction_ne_target
    (G : GeometricCycleClassSpine V H)
    (E : OmniversalSeparatorGhost G)
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := E.weight))
    (i₀ : ClassicalHodgeBasisIndex V H E.weight)
    (U : Module.End ℚ (FiberedNativeAddress V H E.weight))
    (T : Module.End ℚ
      (RationalSingularCohomology H.analytification (2 * E.weight)))
    (hT :
      (((H.cycleClass E.weight).comp
          (toNativeCycle V H E.weight)).comp U) =
        T.comp ((H.cycleClass E.weight).comp
          (toNativeCycle V H E.weight))) :
    T S.hodge.1 ≠
      (hodgeMatrixUnit S.sourceIndex E.sheet S.hodge).1 := by
  intro heq
  have hnonzero :=
    ghostSeedTarget_descendingAction_mismatch_ne_zero G E S i₀ U T hT
  rw [heq, sub_self, map_zero] at hnonzero
  exact hnonzero rfl

/-- Existential form: no ambient action together with a genuine native
commuting square can realize the ghost-selected GST branch target. -/
theorem no_descendingAction_realizes_ghostSeedTarget
    (G : GeometricCycleClassSpine V H)
    (E : OmniversalSeparatorGhost G)
    (S : NativeHodgeOrbitSeed (V := V) (H := H) (p := E.weight))
    (i₀ : ClassicalHodgeBasisIndex V H E.weight)
    (U : Module.End ℚ (FiberedNativeAddress V H E.weight)) :
    ¬ ∃ T : Module.End ℚ
        (RationalSingularCohomology H.analytification (2 * E.weight)),
      (((H.cycleClass E.weight).comp
          (toNativeCycle V H E.weight)).comp U) =
        T.comp ((H.cycleClass E.weight).comp
          (toNativeCycle V H E.weight)) ∧
      T S.hodge.1 =
        (hodgeMatrixUnit S.sourceIndex E.sheet S.hodge).1 := by
  rintro ⟨T, hT, htarget⟩
  exact (ghostSeedTarget_descendingAction_ne_target
    G E S i₀ U T hT) htarget

#check ghost_kills_nativeCycleClass
#check ghost_kills_descendingAction_on_seed
#check ghostSeedTarget_descendingAction_mismatch_formula
#check ghostSeedTarget_descendingAction_mismatch_ne_zero
#check ghostSeedTarget_descendingAction_ne_target
#check no_descendingAction_realizes_ghostSeedTarget

#print axioms ghost_kills_nativeCycleClass
#print axioms ghostSeedTarget_descendingAction_mismatch_formula
#print axioms ghostSeedTarget_descendingAction_mismatch_ne_zero
#print axioms no_descendingAction_realizes_ghostSeedTarget

end GSTClassicalHodgeCoherentNativeGhostObstruction
