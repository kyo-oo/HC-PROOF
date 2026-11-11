import GSTImageThreeAllNOriginalXSourceTransport
import GSTImageThreePureCMCurvatureNative
import GSTGraphV2NativeCurvatureBirth

/-!
# GST Image3 pure ORIGINAL CM-curvature N-wave on the ORIGINAL X

No abstract 12x12 matrix is falsely called an actual algebraic
correspondence. We input ONLY certified original-X
CycleClassOperatorPair J and M, which each act on genuine original-X
rational native Chow cycles with canonical rational Betti naturality.
Then the derived commutator [J,M] is a NEW, actual X-native
cycle-operator pair and its Betti action is the true corresponding
commutator, with no preselected Hodge class cycle representative.

We then use the already-kernel-checked ALL-N original-X source
transport theorem to compile every rational curvature-only companion
C_N and navigation address B_N from this derived original-X source.
The full Hodge cyclicity/rank landing is not deduced without actual
Hodge-geometry data; this is the exact stage-01 naturality part.
-/

set_option maxHeartbeats 6000000
noncomputable section

namespace GSTImageThreePureCMOriginalXLanding

open GSTClassicalHodgeCycleOperatorNaturality
open GSTImageThreeAllNOriginalXSourceTransport
open GSTImageThreeCompanionSourceTransport
open GSTGraphV2NativeCurvatureBirth
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- A REAL ORIGINAL-X CM curvature operator pair built only from
already-realized certified rational Chow and Betti J/M actions.
This provides a genuine new native cycle-source OPERATION, not
the existence of a missing Hodge class. -/
def pureCMSourcePair
    (J M : CycleClassOperatorPair V H p) :
    CycleClassOperatorPair V H p where
  cycleOperator :=
    (J.cycleOperator.comp M.cycleOperator) -
      (M.cycleOperator.comp J.cycleOperator)
  cohomologyOperator :=
    (J.cohomologyOperator.comp M.cohomologyOperator) -
      (M.cohomologyOperator.comp J.cohomologyOperator)
  cycleClass_natural := by
    apply LinearMap.ext
    intro z
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, map_sub]
    rw [J.cycleClass_cycleOperator,
      M.cycleClass_cycleOperator,
      M.cycleClass_cycleOperator,
      J.cycleClass_cycleOperator]

/-- The actual original-X Chow output of derived GST CM curvature
is EXACTLY its canonical rational Betti commutator class. -/
theorem pureCM_originalX_cycleClass
    (J M : CycleClassOperatorPair V H p)
    (Z : codimensionCycles V.X p) :
    H.cycleClass p ((pureCMSourcePair J M).cycleOperator Z) =
      (pureCMSourcePair J M).cohomologyOperator (H.cycleClass p Z) :=
  (pureCMSourcePair J M).cycleClass_cycleOperator Z

/-- ALL finite N and ALL rational source/address matrices, the
CM-only source has an EXACT original-X canonical Chow–Betti square.
No preconstructed inverse Hodge cycle-class map is supplied. -/
theorem allN_pureCM_originalX_class_square
    (N : Nat)
    (U J M : CycleClassOperatorPair V H p)
    (source address : Matrix (Fin N) (Fin N) ℚ)
    (Z : NativeChannels (V := V) (p := p) N) :
    channelCycleClass N
      (allNNativeF N U J (pureCMSourcePair J M) source address Z) =
    allNBettiF N U J (pureCMSourcePair J M) source address
      (channelCycleClass N Z) :=
  allN_originalX_cycleClass_square N U J
    (pureCMSourcePair J M) source address Z

/-- The genuine original-X pure curvature source is completely
interworld for the user's trace-zero companion scheme. -/
theorem allN_pureCM_companion_zero_local
    (N : Nat) (coeff : Nat → ℚ)
    (htrace : coeff (N-1) = 0)
    (i : Fin N) :
    companionSource N coeff i i = 0 :=
  companionSource_zero_diagonal N coeff htrace i

/-- Exact original-X Chow–Betti square for the actual true CM
curvature-only companion C_N with arbitrary navigation B_N. -/
theorem allN_pureCM_companion_class_square
    (N : Nat) (U J M : CycleClassOperatorPair V H p)
    (coeff : Nat → ℚ)
    (address : Matrix (Fin N) (Fin N) ℚ)
    (Z : NativeChannels (V := V) (p := p) N) :
    channelCycleClass N
      (allNNativeF N U J (pureCMSourcePair J M)
        (companionSource N coeff) address Z) =
    allNBettiF N U J (pureCMSourcePair J M)
      (companionSource N coeff) address
      (channelCycleClass N Z) :=
  allN_originalX_cycleClass_square N U J
    (pureCMSourcePair J M) (companionSource N coeff) address Z

#check pureCMSourcePair
#check pureCM_originalX_cycleClass
#check allN_pureCM_originalX_class_square
#check allN_pureCM_companion_zero_local
#check allN_pureCM_companion_class_square
#print axioms pureCM_originalX_cycleClass
#print axioms allN_pureCM_companion_class_square

end GSTImageThreePureCMOriginalXLanding
