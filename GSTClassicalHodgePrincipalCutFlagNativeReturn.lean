import GSTClassicalHodgePrincipalCutFlagAdjointCosmology
import GSTCompactNativeCyclePresentation

/-!
# GST CLASSICAL HODGE — PRINCIPAL-CUT FLAG NATIVE RETURN

The preceding flag-adjoint layer constructed the reverse principal-cut kernel
on finite point presentations.  This file conjugates that reverse kernel
through the exact compact point-presentation normal form of native algebraic
cycles.

For every finite codimension-p source chart `sigma` we therefore obtain a
literal native codimension-lowering operator

    R_sigma : Z^{p+1}(X)_Q -> Z^p(X)_Q.

Composing it with the already-geometric principal-cut successor gives a native
round trip.  On every source point atom in the chart, the round trip satisfies
an exact cycle equation

    R_sigma (L [x]) = lambda_x [x] + Z_cross,

where `lambda_x` is the positive/nonzero principal-cut incidence energy and
`Z_cross` is the realized off-diagonal cross-talk presentation.

This is the cycle-level equation sought by the first-ghost transpose route,
but proved here where it is honestly available: on genuine native point
atoms.  No cycle-class surjectivity, Hodge basis representative, or
cohomological transpose is assumed.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgePrincipalCutFlagNativeReturn

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTNativeCodimensionCyclePresentation
open GSTCompactNativeCyclePresentation
open GSTClassicalHodgePointNormalForm
open GSTClassicalHodgePrincipalCutSuccessorOperator
open GSTClassicalHodgePrincipalCutIncidenceTransposeCosmology
open GSTClassicalHodgePrincipalCutFlagAdjointCosmology

/-- Native reverse flag obtained by conjugating the finite incidence transpose
through the exact compact cycle/presentation equivalence. -/
noncomputable def localTransposeNativeOperator
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (sigma : Finset (CodimensionPoint V.X p)) :
    codimensionCycles V.X (p + 1) →ₗ[ℚ] codimensionCycles V.X p := by
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  exact
    (compactCyclePresentationLinearEquiv V.X p).toLinearMap.comp
      ((localSuccessorTranspose V p sigma).comp
        (compactCyclePresentationLinearEquiv V.X (p + 1)).symm.toLinearMap)

/-- On an explicitly realized finite presentation the reverse native flag is
exactly realization of the transposed presentation. -/
theorem localTransposeNativeOperator_realize
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (sigma : Finset (CodimensionPoint V.X p))
    (psi : FiniteCodimensionPresentation V.X (p + 1)) :
    localTransposeNativeOperator V p sigma
        (realizeFiniteCodimensionPresentation V.X (p + 1) psi) =
      realizeFiniteCodimensionPresentation V.X p
        (localSuccessorTranspose V p sigma psi) := by
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  change
    realizeFiniteCodimensionPresentation V.X p
      (localSuccessorTranspose V p sigma
        (presentationOfNativeCycle V.X (p + 1)
          (realizeFiniteCodimensionPresentation V.X (p + 1) psi))) = _
  rw [presentation_realizeFiniteCodimensionPresentation]

/-- Native normal/round-trip operator: principal cut followed by the reverse
flag on one finite source chart. -/
noncomputable def localFlagNormalNative
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (sigma : Finset (CodimensionPoint V.X p)) :
    codimensionCycles V.X p →ₗ[ℚ] codimensionCycles V.X p :=
  (localTransposeNativeOperator V p sigma).comp
    (successorNativeOperator V p)

/-- Exact pointwise description of the native flag round trip. -/
theorem localFlagNormalNative_point
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (sigma : Finset (CodimensionPoint V.X p))
    (x : CodimensionPoint V.X p) :
    localFlagNormalNative V p sigma (codimensionPointCycle V.X p x) =
      realizeFiniteCodimensionPresentation V.X p
        (localSuccessorNormal V p sigma (Finsupp.single x (1 : ℚ))) := by
  rw [localFlagNormalNative, LinearMap.comp_apply]
  rw [successorNativeOperator_point]
  rw [localTransposeNativeOperator_realize]
  unfold localSuccessorNormal
  rw [LinearMap.comp_apply]
  rw [successorPresentationOperator_single]

/-- Realized off-diagonal correction cycle. -/
noncomputable def crossTalkCycle
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (sigma : Finset (CodimensionPoint V.X p))
    (x : CodimensionPoint V.X p) :
    codimensionCycles V.X p :=
  realizeFiniteCodimensionPresentation V.X p
    (successorCrossTalk V p sigma x)

/-- **EXACT NATIVE FLAG ROUND-TRIP EQUATION.**
The reverse flag followed by the principal-cut incidence returns a nonzero
self coefficient plus one actual algebraic correction cycle. -/
theorem localFlagNormalNative_point_decomposition
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (sigma : Finset (CodimensionPoint V.X p))
    (x : CodimensionPoint V.X p) :
    localFlagNormalNative V p sigma (codimensionPointCycle V.X p x) =
      successorSelfEnergy V p x • codimensionPointCycle V.X p x +
        crossTalkCycle V p sigma x := by
  rw [localFlagNormalNative_point]
  rw [localSuccessorNormal_decomposition]
  unfold crossTalkCycle
  rw [map_add, map_smul]
  simp [realizeFiniteCodimensionPresentation,
    codimensionPointCycle]

/-- The correction really is off-diagonal in the exact compact point normal
form: its coefficient at the distinguished source point is zero. -/
theorem crossTalkCycle_sourceCoefficient_zero
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (sigma : Finset (CodimensionPoint V.X p))
    (x : CodimensionPoint V.X p)
    (hx : x ∈ sigma) :
    letI : CompactSpace V.X := smoothProjectiveCompactSpace V
    presentationOfNativeCycle V.X p (crossTalkCycle V p sigma x) x = 0 := by
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  unfold crossTalkCycle
  rw [presentation_realizeFiniteCodimensionPresentation]
  exact successorCrossTalk_apply_self V p sigma x hx

/-- Live exact principal-cut geometry upgrades the pointwise decomposition to a
nonzero-scaled native cycle identity. -/
theorem localFlagNormalNative_live_crown
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (sigma : Finset (CodimensionPoint V.X p))
    (x : CodimensionPoint V.X p)
    (hx : x ∈ sigma)
    (hExact : GSTClassicalHodgeRelativeSuccessorExactStratum.RelativeSuccessorAmbientExact V p x)
    (hNonempty : (relativeCodimensionOneFinset V x.1).Nonempty) :
    let lambda := successorSelfEnergy V p x
    lambda ≠ 0
      ∧ localFlagNormalNative V p sigma (codimensionPointCycle V.X p x) =
          lambda • codimensionPointCycle V.X p x +
            crossTalkCycle V p sigma x
      ∧ (letI : CompactSpace V.X := smoothProjectiveCompactSpace V
          presentationOfNativeCycle V.X p (crossTalkCycle V p sigma x) x = 0) := by
  dsimp
  exact ⟨
    successorSelfEnergy_ne_zero_of_exact_nonempty
      V p x hExact hNonempty,
    localFlagNormalNative_point_decomposition V p sigma x,
    crossTalkCycle_sourceCoefficient_zero V p sigma x hx⟩

#check localTransposeNativeOperator
#check localTransposeNativeOperator_realize
#check localFlagNormalNative
#check localFlagNormalNative_point
#check crossTalkCycle
#check localFlagNormalNative_point_decomposition
#check crossTalkCycle_sourceCoefficient_zero
#check localFlagNormalNative_live_crown

#print axioms localTransposeNativeOperator_realize
#print axioms localFlagNormalNative_point_decomposition
#print axioms crossTalkCycle_sourceCoefficient_zero
#print axioms localFlagNormalNative_live_crown

end GSTClassicalHodgePrincipalCutFlagNativeReturn
