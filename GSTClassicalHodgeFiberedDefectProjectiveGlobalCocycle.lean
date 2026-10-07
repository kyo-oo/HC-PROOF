import GSTClassicalHodgeFiberedDefectProjectiveCocycle
import GSTClassicalHodgeFiberedNativeProjectiveTransport

/-!
# GST CLASSICAL HODGE — GLOBAL FIBERED PROJECTIVE DEFECT COCYCLE

The atom-level projective defect law extends to every finite fibered-native
state.

For an actual scheme endomorphism `f`, the fibered-native pushforward commutes
with the genuine native cycle projection.  Primitive cycle-class naturality
then gives the exact global cocycle

  defect(f_* Phi)
    = f_*^H(defect Phi)
      + (f_*^H(hodgeFace Phi) - hodgeFace(f_* Phi)).

Thus genuine projective geometry can change the classical landing defect only
through the mismatch between its actual cohomological pushforward and the
multiplicity/Hodge face transported by the common fibered state.

This statement is fully linear and target-free.  It contains no ghost, no
chosen bad sheet, no Hodge-surjectivity premise, no branch packet, and no
projective apex-spoke existence hypothesis.
-/

set_option maxHeartbeats 90000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicGeometry

namespace GSTClassicalHodgeFiberedDefectProjectiveGlobalCocycle

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeFiberedNativePullback
open GSTClassicalHodgeFiberedCycleClassDefect
open GSTClassicalHodgeFiberedNativeProjectiveTransport
open GSTClassicalHodgeProjectivePointTransport
open GSTClassicalHodgePrimitivePushforwardNaturality
open GSTNativeCodimensionCyclePresentation

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- **GLOBAL NATIVE-FACE FUNCTORIALITY.**
The fibered finite-state transport projects to exactly the genuine native
smooth-projective pushforward on every state, not merely on atoms. -/
theorem nativeFace_fiberedPushforward
    (f : V.X ⟶ V.X)
    (Φ : FiberedNativeAddress V H p) :
    toNativeCycle V H p (fiberedNativePushforward f Φ) =
      smoothProjectiveNativePushforward V f p (toNativeCycle V H p Φ) := by
  classical
  induction Φ using Finsupp.induction_linear with
  | zero =>
      simp
  | add a b ha hb =>
      simp [ha, hb]
  | single ix q =>
      rcases ix with ⟨i, x⟩
      have hsingle :
          Finsupp.single (i, x) q =
            q • atom V H p i x := by
        simp [atom]
      rw [hsingle, map_smul, map_smul]
      rw [fiberedNativePushforward_smul_atom]
      rw [map_smul, nativeFace_transportAtom]
      rw [map_smul, toNativeCycle_atom]
      exact congrArg (fun Z => q • Z)
        (smoothProjectiveNativePushforward_point V f p x).symm

/-- The actual native cohomology face of the fibered transport is exactly the
geometric cohomological pushforward of the original native face. -/
theorem nativeCycleClass_fiberedPushforward
    (f : V.X ⟶ V.X)
    (N : GeometricPushforwardNaturality V H p f)
    (Φ : FiberedNativeAddress V H p) :
    fiberedNativeCycleClass (V := V) (H := H) (p := p)
        (fiberedNativePushforward f Φ) =
      N.cohomologyPushforward
        (fiberedNativeCycleClass (V := V) (H := H) (p := p) Φ) := by
  unfold fiberedNativeCycleClass
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  rw [nativeFace_fiberedPushforward]
  exact N.naturality _

/-- **GLOBAL PROJECTIVE DEFECT COCYCLE.**

For every finite fibered-native state, the defect after genuine projective
transport equals the transported old defect plus one explicit Hodge-face
transport mismatch. -/
theorem fiberedCycleClassDefect_pushforward_cocycle
    (f : V.X ⟶ V.X)
    (N : GeometricPushforwardNaturality V H p f)
    (Φ : FiberedNativeAddress V H p) :
    fiberedCycleClassDefect (V := V) (H := H) (p := p)
        (fiberedNativePushforward f Φ) =
      N.cohomologyPushforward
        (fiberedCycleClassDefect (V := V) (H := H) (p := p) Φ)
      +
      (N.cohomologyPushforward
          (fiberedHodgeAmbient (V := V) (H := H) (p := p) Φ)
        -
        fiberedHodgeAmbient (V := V) (H := H) (p := p)
          (fiberedNativePushforward f Φ)) := by
  unfold fiberedCycleClassDefect
  rw [nativeCycleClass_fiberedPushforward f N Φ]
  rw [LinearMap.map_sub]
  abel

/-- If the source state is already a genuine classical landing state, then the
entire transported defect is exactly the Hodge-face transport mismatch. -/
theorem defect_pushforward_of_source_zero
    (f : V.X ⟶ V.X)
    (N : GeometricPushforwardNaturality V H p f)
    (Φ : FiberedNativeAddress V H p)
    (hΦ :
      fiberedCycleClassDefect (V := V) (H := H) (p := p) Φ = 0) :
    fiberedCycleClassDefect (V := V) (H := H) (p := p)
        (fiberedNativePushforward f Φ) =
      N.cohomologyPushforward
          (fiberedHodgeAmbient (V := V) (H := H) (p := p) Φ)
        -
        fiberedHodgeAmbient (V := V) (H := H) (p := p)
          (fiberedNativePushforward f Φ) := by
  rw [fiberedCycleClassDefect_pushforward_cocycle f N Φ, hΦ,
    LinearMap.map_zero, zero_add]

/-- **EXACT GLOBAL ZERO-DEFECT TRANSPORT CRITERION.**
For a defect-zero source, genuine projective transport remains defect-zero iff
its actual cohomological action agrees with the transported Hodge face. -/
theorem pushforward_defect_zero_iff_hodgeFace_natural
    (f : V.X ⟶ V.X)
    (N : GeometricPushforwardNaturality V H p f)
    (Φ : FiberedNativeAddress V H p)
    (hΦ :
      fiberedCycleClassDefect (V := V) (H := H) (p := p) Φ = 0) :
    fiberedCycleClassDefect (V := V) (H := H) (p := p)
        (fiberedNativePushforward f Φ) = 0 ↔
      N.cohomologyPushforward
          (fiberedHodgeAmbient (V := V) (H := H) (p := p) Φ) =
        fiberedHodgeAmbient (V := V) (H := H) (p := p)
          (fiberedNativePushforward f Φ) := by
  rw [defect_pushforward_of_source_zero f N Φ hΦ]
  exact sub_eq_zero

#check nativeFace_fiberedPushforward
#check nativeCycleClass_fiberedPushforward
#check fiberedCycleClassDefect_pushforward_cocycle
#check defect_pushforward_of_source_zero
#check pushforward_defect_zero_iff_hodgeFace_natural

#print axioms nativeFace_fiberedPushforward
#print axioms nativeCycleClass_fiberedPushforward
#print axioms fiberedCycleClassDefect_pushforward_cocycle
#print axioms pushforward_defect_zero_iff_hodgeFace_natural

end GSTClassicalHodgeFiberedDefectProjectiveGlobalCocycle
