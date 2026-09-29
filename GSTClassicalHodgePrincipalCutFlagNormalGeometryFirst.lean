import GSTClassicalHodgePrincipalCutFlagCorrespondenceDescent
import GSTClassicalHodgeGeometricCycleClassSpine
import GSTClassicalHodgeGeometryFirstTwoGenerator

/-!
# GST CLASSICAL HODGE — PRINCIPAL-CUT FLAG NORMAL, GEOMETRY FIRST

The forward principal cut is already a genuine graded cycle-class operator in
`GeometricCycleClassSpine`.  The geometric correspondence-descent module gives
an equally genuine reverse operator whenever the finite principal-cut incidence
is realized by one bi-finite closed correspondence and its actual factor-swap
transpose.

This file composes those two geometric arrows.

The result is a same-weight native flag-normal operator

    codim p --cut--> codim (p+1) --transpose-return--> codim p

with an exact cycle-class square.  Consequently its native operator is kernel
stable automatically.  This removes both the abstract coefficient projection
formula and the over-strong requirement that arbitrary two-slot operators come
from self-maps `X ⟶ X`.

For the geometry-first Hodge route, the only remaining comparison is therefore
an honest Hodge-fiber statement: identify the ambient action forced by this
native flag normal with the desired two-slot GST primitive.  No kernel
stability, basis-cycle lift, or arbitrary ambient extension is separately
postulated here.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgePrincipalCutFlagNormalGeometryFirst

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeCrossWeightNativePropagation
open GSTClassicalHodgeNativeOperatorCohomologyRealization
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgePrincipalCutFlagCorrespondenceDescent
open GSTClassicalHodgePrincipalCutFlagCorrespondenceDescent.PrincipalCutFlagBiFiniteRealization
open GSTClassicalHodgeGradedFiniteClosedCorrespondence
open GSTClassicalHodgeGeometryFirstTwoGenerator

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p q r : Nat}

/-- Composition of genuine graded cycle-class operator pairs. -/
noncomputable def composeGradedCycleClassOperatorPair
    (T : GradedCycleClassOperatorPair V H q r)
    (S : GradedCycleClassOperatorPair V H p q) :
    GradedCycleClassOperatorPair V H p r where
  cycleOperator := T.cycleOperator.comp S.cycleOperator
  cohomologyOperator := T.cohomologyOperator.comp S.cohomologyOperator
  cycleClass_natural := by
    intro Z
    simp only [LinearMap.comp_apply]
    rw [T.cycleClass_natural, S.cycleClass_natural]

namespace GradedCycleClassOperatorPair

/-- A same-weight genuine cycle-class pair has kernel-stable native side. -/
theorem kernelStable
    (T : GradedCycleClassOperatorPair V H p p) :
    KernelStable (H := H) T.cycleOperator := by
  intro Z hZ
  rw [T.cycleClass_natural, hZ]
  exact T.cohomologyOperator.map_zero

/-- The canonical ambient extension manufactured from the native operator and
its already-proved kernel stability agrees with the original genuine
cohomology operator on every actual algebraic cycle class. -/
theorem ambientOperator_agrees_on_cycleClass
    (T : GradedCycleClassOperatorPair V H p p)
    (Z : codimensionCycles V.X p) :
    ambientOperator (H := H) T.cycleOperator T.kernelStable
        (H.cycleClass p Z) =
      T.cohomologyOperator (H.cycleClass p Z) := by
  rw [cycleClass_ambientOperator]
  exact T.cycleClass_natural Z

end GradedCycleClassOperatorPair

variable
  (G : GeometricCycleClassSpine V H)
  {sigma : Finset (CodimensionPoint V.X p)}
  (R : PrincipalCutFlagBiFiniteRealization V p sigma)
  (N : GradedCorrespondencePointNaturality
    R.correspondence.transpose H (p + 1) p)

/-- The genuine reverse pair supplied by the actual factor-swap transpose of
an incidence correspondence. -/
noncomputable def geometricReverseFlagPair :
    GradedCycleClassOperatorPair V H (p + 1) p :=
  R.reverseFlagOperatorPair N

/-- **SAME-WEIGHT GEOMETRIC FLAG NORMAL.**
First perform the genuine principal cut from the cycle-class spine, then return
through the actual transposed incidence correspondence. -/
noncomputable def principalCutFlagNormalPair :
    GradedCycleClassOperatorPair V H p p :=
  composeGradedCycleClassOperatorPair
    (geometricReverseFlagPair (G := G) R N)
    (G.principalCutPair p)

/-- The native flag normal is exactly reverse-after-forward on cycles. -/
@[simp]
theorem principalCutFlagNormalPair_cycleOperator :
    (principalCutFlagNormalPair (G := G) R N).cycleOperator =
      (localTransposeNativeOperator V p sigma).comp
        (G.principalCutPair p).cycleOperator := by
  rfl

/-- The cohomological flag normal is exactly reverse-after-forward on rational
singular cohomology. -/
@[simp]
theorem principalCutFlagNormalPair_cohomologyOperator :
    (principalCutFlagNormalPair (G := G) R N).cohomologyOperator =
      N.cohomologyOperator.comp
        (G.principalCutPair p).cohomologyOperator := by
  rfl

/-- **AUTOMATIC KERNEL STABILITY OF THE FLAG NORMAL.**
This is the critical same-weight native fact required by geometry-first
externalization.  It is a theorem of the two genuine cycle-class squares, not
an independent hypothesis. -/
theorem principalCutFlagNormal_kernelStable :
    KernelStable (H := H)
      (principalCutFlagNormalPair (G := G) R N).cycleOperator :=
  (principalCutFlagNormalPair (G := G) R N).kernelStable

/-- The canonical ambient operator forced from the native flag normal agrees
with the geometric forward/transpose cohomology composition on every actual
cycle class. -/
theorem principalCutFlagNormal_ambient_agrees_on_cycleClass
    (Z : codimensionCycles V.X p) :
    ambientOperator (H := H)
        (principalCutFlagNormalPair (G := G) R N).cycleOperator
        (principalCutFlagNormal_kernelStable (G := G) R N)
        (H.cycleClass p Z) =
      N.cohomologyOperator
        ((G.principalCutPair p).cohomologyOperator
          (H.cycleClass p Z)) := by
  rw [(principalCutFlagNormalPair (G := G) R N).ambientOperator_agrees_on_cycleClass]
  rfl

/-- A Hodge primitive can now be certified by a principal-cut flag normal with
only one genuinely new comparison: its geometry-forced ambient action on the
Hodge fiber.  Kernel stability is discharged by the flag geometry above. -/
noncomputable def nativeHodgePrimitiveOfFlagNormal
    (T : Module.End ℚ (ClassicalHodgeFiber V H p))
    (hrestrict :
      ∀ alpha : ClassicalHodgeFiber V H p,
        ambientOperator (H := H)
            (principalCutFlagNormalPair (G := G) R N).cycleOperator
            (principalCutFlagNormal_kernelStable (G := G) R N)
            alpha.1 =
          (T alpha).1) :
    NativeHodgePrimitive (V := V) (H := H) T where
  cycleOperator := (principalCutFlagNormalPair (G := G) R N).cycleOperator
  kernelStable := principalCutFlagNormal_kernelStable (G := G) R N
  restricts_to_hodge := hrestrict

/-- Two geometric separator flags whose forced ambient actions realize the two
GST primitives give the exact `GeometryFirstTwoGenerator` consumed by the
rank-free Hodge saturation theorem.  All native operators and all kernel
stability obligations are constructed above; only the two Hodge restriction
identities remain as mathematical comparison goals. -/
noncomputable def geometryFirstTwoGeneratorOfFlagNormals
    {i j : ClassicalHodgeBasisIndex V H p}
    {sigmaCode sigmaLef : Finset (CodimensionPoint V.X p)}
    (Rcode : PrincipalCutFlagBiFiniteRealization V p sigmaCode)
    (Ncode : GradedCorrespondencePointNaturality
      Rcode.correspondence.transpose H (p + 1) p)
    (Rlef : PrincipalCutFlagBiFiniteRealization V p sigmaLef)
    (Nlef : GradedCorrespondencePointNaturality
      Rlef.correspondence.transpose H (p + 1) p)
    (hcode :
      ∀ alpha : ClassicalHodgeFiber V H p,
        ambientOperator (H := H)
            (principalCutFlagNormalPair (G := G) Rcode Ncode).cycleOperator
            (principalCutFlagNormal_kernelStable (G := G) Rcode Ncode)
            alpha.1 =
          (twoSlotCodeHodge i j alpha).1)
    (hlef :
      ∀ alpha : ClassicalHodgeFiber V H p,
        ambientOperator (H := H)
            (principalCutFlagNormalPair (G := G) Rlef Nlef).cycleOperator
            (principalCutFlagNormal_kernelStable (G := G) Rlef Nlef)
            alpha.1 =
          (twoSlotHodgeOperator i j (diagonalLefschetzQ 2 2) alpha).1) :
    GeometryFirstTwoGenerator (V := V) (H := H) i j where
  code := nativeHodgePrimitiveOfFlagNormal
    (G := G) Rcode Ncode (twoSlotCodeHodge i j) hcode
  lefschetz := nativeHodgePrimitiveOfFlagNormal
    (G := G) Rlef Nlef
      (twoSlotHodgeOperator i j (diagonalLefschetzQ 2 2)) hlef

#check composeGradedCycleClassOperatorPair
#check GradedCycleClassOperatorPair.kernelStable
#check GradedCycleClassOperatorPair.ambientOperator_agrees_on_cycleClass
#check principalCutFlagNormalPair
#check principalCutFlagNormal_kernelStable
#check principalCutFlagNormal_ambient_agrees_on_cycleClass
#check nativeHodgePrimitiveOfFlagNormal
#check geometryFirstTwoGeneratorOfFlagNormals

#print axioms principalCutFlagNormal_kernelStable
#print axioms principalCutFlagNormal_ambient_agrees_on_cycleClass
#print axioms nativeHodgePrimitiveOfFlagNormal
#print axioms geometryFirstTwoGeneratorOfFlagNormals

end GSTClassicalHodgePrincipalCutFlagNormalGeometryFirst
