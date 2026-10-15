import GSTBlowupHodgeTransfer
import GSTGeometricRealizationStage2G
import GSTClassicalHodgeFiberedCosmology

/-!
# GST actual-scheme-carrier codimension-three blow-up bridge

This module removes the unconstrained abstract cycle and Hodge vector spaces
from the earlier blow-up transfer theorem. ALL native cycles are actual Mathlib
rational AlgebraicCycle submodules on scheme carriers, and ALL Hodge spaces
are the Stage-2G Hodge (p,p) subtypes of rational singular Betti cohomology.

The geometric maps are explicitly typed as the projective pullback and two
exceptional Gysin operations. Their concrete construction from a specific
Mathlib blow-up scheme and the comparison with analytic Betti classes are
still GEOMETRIC OBLIGATIONS, not hidden proofs or arbitrary Hodge lifts.

Specialization: a codimension-three smooth curve center C in a smooth
projective fourfold X, and its smooth blow-up Y = Bl_C X.
The exceptional source weights are 1 and 0, target weight is 2.
-/

set_option maxHeartbeats 10000000
noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTBlowupHodgeTransfer

namespace GSTBlowupSchemeNativeBridge

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Minimal actual geometric fact: rational cycle classes have Hodge
type (p,p). No Hodge-surjectivity premise is included. -/
structure AlgebraicCycleHodgeSemantics
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) (p : Nat) where
  cycle_is_hodge :
    ∀ Z : codimensionCycles V.X p,
      H.cycleClass p Z ∈ rationalHodgeSubspace (H.hodgeBigrading p)

/-- The actual scheme-specific cycle-class map, restricted to the
real rational Hodge subspace, is Q-linear by construction. -/
noncomputable def AlgebraicCycleHodgeSemantics.toHodge
    {p : Nat} (G : AlgebraicCycleHodgeSemantics V H p) :
    codimensionCycles V.X p →ₗ[ℚ] ClassicalHodgeFiber V H p where
  toFun Z := ⟨H.cycleClass p Z, G.cycle_is_hodge Z⟩
  map_add' := by
    intro z w
    apply Subtype.ext
    exact map_add (H.cycleClass p) z w
  map_smul' := by
    intro c z
    apply Subtype.ext
    exact map_smul (H.cycleClass p) c z

/-- The geometric blow-up interface is now pinned to actual smooth
projective scheme carriers and actual cohomology of their analytifications.
All three cycle maps use the real native codimension cycle modules.

The three Hodge maps and their inverses/projectors must be supplied by
an independent cohomological blow-up theorem. They carry no arbitrary
target Hodge-to-cycle reverse arrow.
-/
structure ActualSchemeCurveBlowupGeometry
    (X C Y : SmoothProjectiveComplexScheme)
    (HX : HodgeBigradedBettiData X)
    (HC : HodgeBigradedBettiData C)
    (HY : HodgeBigradedBettiData Y) where
  XcycleHodge : AlgebraicCycleHodgeSemantics X HX 2
  CpointHodge : AlgebraicCycleHodgeSemantics C HC 1
  CunitHodge : AlgebraicCycleHodgeSemantics C HC 0
  YcycleHodge : AlgebraicCycleHodgeSemantics Y HY 2
  nativePullback :
    codimensionCycles X.X 2 →ₗ[ℚ] codimensionCycles Y.X 2
  nativeExceptionalPoint :
    codimensionCycles C.X 1 →ₗ[ℚ] codimensionCycles Y.X 2
  nativeExceptionalUnit :
    codimensionCycles C.X 0 →ₗ[ℚ] codimensionCycles Y.X 2
  hodgePullback :
    ClassicalHodgeFiber X HX 2 →ₗ[ℚ] ClassicalHodgeFiber Y HY 2
  hodgeExceptionalPoint :
    ClassicalHodgeFiber C HC 1 →ₗ[ℚ] ClassicalHodgeFiber Y HY 2
  hodgeExceptionalUnit :
    ClassicalHodgeFiber C HC 0 →ₗ[ℚ] ClassicalHodgeFiber Y HY 2
  projectBase :
    ClassicalHodgeFiber Y HY 2 →ₗ[ℚ] ClassicalHodgeFiber X HX 2
  projectPoint :
    ClassicalHodgeFiber Y HY 2 →ₗ[ℚ] ClassicalHodgeFiber C HC 1
  projectUnit :
    ClassicalHodgeFiber Y HY 2 →ₗ[ℚ] ClassicalHodgeFiber C HC 0
  geometricDecomposition : ∀ alpha : ClassicalHodgeFiber Y HY 2,
    hodgePullback (projectBase alpha) +
      hodgeExceptionalPoint (projectPoint alpha) +
      hodgeExceptionalUnit (projectUnit alpha) = alpha
  baseNaturality : ∀ Z : codimensionCycles X.X 2,
    YcycleHodge.toHodge (nativePullback Z) =
      hodgePullback (XcycleHodge.toHodge Z)
  pointNaturality : ∀ Z : codimensionCycles C.X 1,
    YcycleHodge.toHodge (nativeExceptionalPoint Z) =
      hodgeExceptionalPoint (CpointHodge.toHodge Z)
  unitNaturality : ∀ Z : codimensionCycles C.X 0,
    YcycleHodge.toHodge (nativeExceptionalUnit Z) =
      hodgeExceptionalUnit (CunitHodge.toHodge Z)

/-- Forget only the geometry-specific *types*, not their actual values:
this realizes the earlier constructor interface with real Stage-2G maps. -/
noncomputable def ActualSchemeCurveBlowupGeometry.toTransfer
    {X C Y : SmoothProjectiveComplexScheme}
    {HX : HodgeBigradedBettiData X}
    {HC : HodgeBigradedBettiData C}
    {HY : HodgeBigradedBettiData Y}
    (G : ActualSchemeCurveBlowupGeometry X C Y HX HC HY) :
    CodimThreeBlowupData
      (codimensionCycles X.X 2)
      (codimensionCycles C.X 1)
      (codimensionCycles C.X 0)
      (codimensionCycles Y.X 2)
      (ClassicalHodgeFiber X HX 2)
      (ClassicalHodgeFiber C HC 1)
      (ClassicalHodgeFiber C HC 0)
      (ClassicalHodgeFiber Y HY 2) where
  clBase := G.XcycleHodge.toHodge
  clExceptionalOne := G.CpointHodge.toHodge
  clExceptionalTwo := G.CunitHodge.toHodge
  clTarget := G.YcycleHodge.toHodge
  nativeBasePullback := G.nativePullback
  nativeGysinOne := G.nativeExceptionalPoint
  nativeGysinTwo := G.nativeExceptionalUnit
  hodgeBasePullback := G.hodgePullback
  hodgeGysinOne := G.hodgeExceptionalPoint
  hodgeGysinTwo := G.hodgeExceptionalUnit
  componentBase := G.projectBase
  componentExceptionalOne := G.projectPoint
  componentExceptionalTwo := G.projectUnit
  geometricDecomposition := G.geometricDecomposition
  nativeBaseNaturality := G.baseNaturality
  nativeGysinOneNaturality := G.pointNaturality
  nativeGysinTwoNaturality := G.unitNaturality

/-- A cycle on the actual blow-up scheme is constructed from cycles on
the actual base and center schemes. The inputs are source algebraicity,
not a representative of the target class. -/
theorem actual_scheme_blowup_constructs_all_middle_hodge_cycles
    {X C Y : SmoothProjectiveComplexScheme}
    {HX : HodgeBigradedBettiData X}
    {HC : HodgeBigradedBettiData C}
    {HY : HodgeBigradedBettiData Y}
    (G : ActualSchemeCurveBlowupGeometry X C Y HX HC HY)
    (hX : ∀ beta : ClassicalHodgeFiber X HX 2,
      ∃ Z : codimensionCycles X.X 2, G.XcycleHodge.toHodge Z = beta)
    (hC1 : ∀ beta : ClassicalHodgeFiber C HC 1,
      ∃ Z : codimensionCycles C.X 1, G.CpointHodge.toHodge Z = beta)
    (hC0 : ∀ beta : ClassicalHodgeFiber C HC 0,
      ∃ Z : codimensionCycles C.X 0, G.CunitHodge.toHodge Z = beta)
    (alpha : ClassicalHodgeFiber Y HY 2) :
    ∃ Z : codimensionCycles Y.X 2, HY.cycleClass 2 Z = alpha.1 := by
  obtain ⟨Z, hZ⟩ :=
    every_blowup_hodge_class_has_native_cycle
      G.toTransfer hX hC1 hC0 alpha
  exact ⟨Z, congrArg Subtype.val hZ⟩

#check AlgebraicCycleHodgeSemantics.toHodge
#check ActualSchemeCurveBlowupGeometry.toTransfer
#check actual_scheme_blowup_constructs_all_middle_hodge_cycles
#print axioms actual_scheme_blowup_constructs_all_middle_hodge_cycles

end GSTBlowupSchemeNativeBridge
