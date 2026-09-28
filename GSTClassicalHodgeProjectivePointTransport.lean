import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
import GSTCompactNativeCyclePresentation
import GSTClassicalHodgeGeneratorwiseAtomicStability

/-!
# GST CLASSICAL HODGE — PROJECTIVE POINT TRANSPORT

This module is the first external geometric transport layer of the classical
landing.  It works with actual Mathlib schemes, actual scheme morphisms, and
actual native algebraic cycles.

Mathlib's pushforward of algebraic cycles attaches the residue-degree weight
to the image of a generic point and may be filtered by a weight function.  For
the codimension-p layer we use coheight itself as that weight.  On generators
this says exactly:

* a genuine codimension-p generic point `x` is transported to `f x` when the
  target point still has coheight p;
* its coefficient is multiplied by the residue degree of `f` at `x`;
* if the image leaves codimension p, the codimension-p component is zero.

The free finite-presentation module lets us extend this point transport
linearly, and the compact/projective normal form then extends it to every
native codimension-p cycle on a smooth projective scheme.

No cohomological surjectivity or Hodge conclusion appears here.  This is a
pure native-cycle transport construction.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTNativeCodimensionCyclePresentation
open GSTCompactNativeCyclePresentation
open GSTClassicalHodgeGeneratorwiseAtomicStability
open GSTClassicalHodgePointNormalForm

namespace GSTClassicalHodgeProjectivePointTransport

universe u

variable {X Y : Scheme.{u}}

/-- Residue-degree coefficient carried by one point under a scheme morphism. -/
noncomputable def pointResidueWeight
    (f : X ⟶ Y) (x : X) : ℚ :=
  (Scheme.Hom.residueDegree f x : ℚ)

/-- Codimension-p component of the geometric pushforward of one genuine point
cycle. -/
noncomputable def pointPushforwardPresentation
    (f : X ⟶ Y) (p : Nat)
    (x : CodimensionPoint X p) :
    FiniteCodimensionPresentation Y p := by
  classical
  by_cases hcod : Order.coheight (f x.1) = p
  · exact Finsupp.single ⟨f x.1, hcod⟩ (pointResidueWeight f x.1)
  · exact 0

/-- The point pushforward presentation is supported on exactly the geometric
image point whenever codimension is preserved. -/
theorem pointPushforwardPresentation_eq_single
    (f : X ⟶ Y) (p : Nat)
    (x : CodimensionPoint X p)
    (hcod : Order.coheight (f x.1) = p) :
    pointPushforwardPresentation f p x =
      Finsupp.single ⟨f x.1, hcod⟩ (pointResidueWeight f x.1) := by
  classical
  simp [pointPushforwardPresentation, hcod]

/-- If the geometric image leaves codimension p, the p-component vanishes. -/
theorem pointPushforwardPresentation_eq_zero
    (f : X ⟶ Y) (p : Nat)
    (x : CodimensionPoint X p)
    (hcod : Order.coheight (f x.1) ≠ p) :
    pointPushforwardPresentation f p x = 0 := by
  classical
  simp [pointPushforwardPresentation, hcod]

/-- Linear extension of the geometric point transport to arbitrary finite
codimension-p presentations. -/
noncomputable def pushforwardPresentation
    (f : X ⟶ Y) (p : Nat) :
    FiniteCodimensionPresentation X p →ₗ[ℚ]
      FiniteCodimensionPresentation Y p where
  toFun φ := φ.sum fun x q => q • pointPushforwardPresentation f p x
  map_add' := by
    intro φ ψ
    classical
    exact Finsupp.sum_add_index'
      (fun a => by simp) (fun a b₁ b₂ => by rw [add_smul])
  map_smul' := by
    intro q φ
    classical
    have h0 : ∀ i, (fun x c => c • pointPushforwardPresentation f p x) i 0 = 0 :=
      fun i => by simp
    have key : ∀ (r c : ℚ) (x : CodimensionPoint X p),
        (r • c) • pointPushforwardPresentation f p x
          = r • (c • pointPushforwardPresentation f p x) := by
      intro r c x
      rw [smul_smul, smul_eq_mul]
    rw [Finsupp.sum_smul_index' h0]
    simp only [key]
    show (Finsupp.sum φ fun i c => q • (c • pointPushforwardPresentation f p i))
        = q • (Finsupp.sum φ fun i c => c • pointPushforwardPresentation f p i)
    simp only [Finsupp.sum, Finset.sum_smul]

@[simp]
theorem pushforwardPresentation_single
    (f : X ⟶ Y) (p : Nat)
    (x : CodimensionPoint X p) (q : ℚ) :
    pushforwardPresentation f p (Finsupp.single x q) =
      q • pointPushforwardPresentation f p x := by
  classical
  simp [pushforwardPresentation]

/-- Realize the transported point presentation as an actual native target
codimension-p algebraic cycle. -/
noncomputable def nativePointPushforward
    (f : X ⟶ Y) (p : Nat)
    (x : CodimensionPoint X p) : codimensionCycles Y p :=
  realizeFiniteCodimensionPresentation Y p
    (pointPushforwardPresentation f p x)

/-- Native point transport has the expected single-point formula whenever
codimension is preserved. -/
theorem nativePointPushforward_eq
    (f : X ⟶ Y) (p : Nat)
    (x : CodimensionPoint X p)
    (hcod : Order.coheight (f x.1) = p) :
    nativePointPushforward f p x =
      pointResidueWeight f x.1 •
        codimensionPointCycle Y p ⟨f x.1, hcod⟩ := by
  rw [nativePointPushforward,
    pointPushforwardPresentation_eq_single f p x hcod]
  exact realizeFiniteCodimensionPresentation_single
    Y p ⟨f x.1, hcod⟩ (pointResidueWeight f x.1)

/-- Realize finite geometric transport as a native codimension-p cycle. -/
noncomputable def realizePushforwardPresentation
    (f : X ⟶ Y) (p : Nat) :
    FiniteCodimensionPresentation X p →ₗ[ℚ] codimensionCycles Y p :=
  (realizePresentationLinear Y p).comp (pushforwardPresentation f p)

@[simp]
theorem realizePushforwardPresentation_single
    (f : X ⟶ Y) (p : Nat)
    (x : CodimensionPoint X p) :
    realizePushforwardPresentation f p (Finsupp.single x 1) =
      nativePointPushforward f p x := by
  simp [realizePushforwardPresentation, nativePointPushforward,
    pushforwardPresentation_single, realizePresentationLinear_apply,
    one_smul]


/-- On a smooth projective source, every native codimension-p cycle admits a
finite point normal form, so point transport extends canonically to all native
cycles. -/
noncomputable def smoothProjectiveNativePushforward
    (V : SmoothProjectiveComplexScheme)
    (f : V.X ⟶ V.X) (p : Nat) :
    codimensionCycles V.X p →ₗ[ℚ] codimensionCycles V.X p := by
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  exact (realizePushforwardPresentation f p).comp
    (presentationOfNativeCycleLinear V.X p)

/-- The smooth-projective native transport is determined by its action on
point-cycle generators. -/
theorem smoothProjectiveNativePushforward_point
    (V : SmoothProjectiveComplexScheme)
    (f : V.X ⟶ V.X) (p : Nat)
    (x : CodimensionPoint V.X p) :
    smoothProjectiveNativePushforward V f p
        (codimensionPointCycle V.X p x) =
      nativePointPushforward f p x := by
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  have hcomp : smoothProjectiveNativePushforward V f p =
      (realizePushforwardPresentation f p).comp
        (presentationOfNativeCycleLinear V.X p) := rfl
  have h1 : presentationOfNativeCycleLinear V.X p
      (codimensionPointCycle V.X p x) = Finsupp.single x (1 : ℚ) := by
    classical
    rw [presentationOfNativeCycleLinear_apply]
    ext y
    show ((codimensionPointCycle V.X p x).1 : AlgebraicCycle V.X ℚ) y.1
      = (Finsupp.single x (1 : ℚ)) y
    by_cases hy : y = x
    · rw [hy]
      simp [codimensionPointCycle, Function.locallyFinsuppWithin.single_apply]
    · have hne : y.1 ≠ x.1 := fun heq => hy (Subtype.ext heq)
      have hz : ((codimensionPointCycle V.X p x).1 : AlgebraicCycle V.X ℚ) y.1 = 0 := by
        simp [codimensionPointCycle, hne, Function.locallyFinsuppWithin.single_apply]
      rw [hz]
      simp [hy]
  rw [hcomp, LinearMap.coe_comp, Function.comp_apply, h1,
    realizePushforwardPresentation_single]

/-- The native transport construction itself supplies a point-lift family for
its own point-generator action. -/
theorem nativePointPushforward_exists
    (V : SmoothProjectiveComplexScheme)
    (f : V.X ⟶ V.X) (p : Nat)
    (x : CodimensionPoint V.X p) :
    ∃ Z : codimensionCycles V.X p,
      Z = smoothProjectiveNativePushforward V f p
        (codimensionPointCycle V.X p x) := by
  exact ⟨nativePointPushforward f p x,
    (smoothProjectiveNativePushforward_point V f p x).symm⟩

#check pointResidueWeight
#check pointPushforwardPresentation
#check pushforwardPresentation
#check nativePointPushforward
#check realizePushforwardPresentation
#check smoothProjectiveNativePushforward
#check smoothProjectiveNativePushforward_point

#print axioms pointPushforwardPresentation_eq_single
#print axioms nativePointPushforward_eq
#print axioms smoothProjectiveNativePushforward_point

end GSTClassicalHodgeProjectivePointTransport
