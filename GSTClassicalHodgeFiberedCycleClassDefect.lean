import GSTClassicalHodgeNormalizedFiberedSpectralAtom
import GSTClassicalHodgeAtomicDefectDuality
import GSTWorldRecoordinationGroupoid
import GSTClassicalHodgeNativeInteractionNormalForm

/-!
# GST CLASSICAL HODGE — FIBERED CYCLE-CLASS DEFECT

The common-refinement universe remembers both pieces of data that must agree
in the classical landing:

* the classical Hodge multiplicity coordinate;
* the genuine native codimension-p algebraic cycle.

The limitless GST base address of those faces already agrees identically.  The
remaining classical question is therefore the vertical defect between the
actual cohomology class of the native face and the actual Hodge vector encoded
by the multiplicity face.

This file packages that difference as one linear map.  It is the precise
quantity on which the limitless projector, Poincare, recoordination and native
correspondence arsenal must act.  No cycle-class surjectivity statement is
assumed.
-/

set_option maxHeartbeats 60000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeFiberedCycleClassDefect

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTWorldRecoordinationGroupoid
open GSTClassicalHodgeFiberedNativeRecoordination
open GSTClassicalHodgeFiniteSupportArsenalConjugation
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeFiberedNativePullback
open GSTClassicalHodgeNormalizedFiberedSpectralAtom
open GSTClassicalHodgeNativeInteractionNormalForm

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Reconstruct the genuine Hodge vector encoded by the multiplicity face of a
fibered native state. -/
noncomputable def fiberedHodgeClass :
    FiberedNativeAddress V H p →ₗ[ℚ] ClassicalHodgeFiber V H p :=
  (classicalHodgeBasis V H p).repr.symm.toLinearMap.comp
    (forgetPoint V H p)

/-- Ambient rational cohomology class carried by the Hodge face. -/
noncomputable def fiberedHodgeAmbient :
    FiberedNativeAddress V H p →ₗ[ℚ]
      RationalSingularCohomology H.analytification (2 * p) :=
  (rationalHodgeSubspace (H.hodgeBigrading p)).subtype.comp
    (fiberedHodgeClass (V := V) (H := H) (p := p))

/-- Actual cohomology class carried by the genuine native cycle face. -/
noncomputable def fiberedNativeCycleClass :
    FiberedNativeAddress V H p →ₗ[ℚ]
      RationalSingularCohomology H.analytification (2 * p) :=
  (H.cycleClass p).comp (toNativeCycle V H p)

/-- **THE FIBERED CLASSICAL DEFECT.**
Native cycle class minus the genuine Hodge class encoded by the multiplicity
face. -/
noncomputable def fiberedCycleClassDefect :
    FiberedNativeAddress V H p →ₗ[ℚ]
      RationalSingularCohomology H.analytification (2 * p) :=
  fiberedNativeCycleClass (V := V) (H := H) (p := p) -
    fiberedHodgeAmbient (V := V) (H := H) (p := p)

@[simp]
theorem fiberedHodgeClass_atom
    (i : ClassicalHodgeBasisIndex V H p)
    (x : GSTNativeCodimensionCyclePresentation.CodimensionPoint V.X p) :
    fiberedHodgeClass (V := V) (H := H) (p := p)
      (atom V H p i x) = classicalHodgeBasis V H p i := by
  simp [fiberedHodgeClass]

@[simp]
theorem fiberedHodgeAmbient_atom
    (i : ClassicalHodgeBasisIndex V H p)
    (x : GSTNativeCodimensionCyclePresentation.CodimensionPoint V.X p) :
    fiberedHodgeAmbient (V := V) (H := H) (p := p)
      (atom V H p i x) = (classicalHodgeBasis V H p i).1 := by
  simp [fiberedHodgeAmbient]

@[simp]
theorem fiberedNativeCycleClass_atom
    (i : ClassicalHodgeBasisIndex V H p)
    (x : GSTNativeCodimensionCyclePresentation.CodimensionPoint V.X p) :
    fiberedNativeCycleClass (V := V) (H := H) (p := p)
      (atom V H p i x) =
      H.cycleClass p
        (GSTNativeCodimensionCyclePresentation.codimensionPointCycle V.X p x) := by
  simp [fiberedNativeCycleClass]

/-- On one common atom the defect is exactly the difference between the genuine
point-cycle class and the selected genuine Hodge basis vector. -/
@[simp]
theorem fiberedCycleClassDefect_atom
    (i : ClassicalHodgeBasisIndex V H p)
    (x : GSTNativeCodimensionCyclePresentation.CodimensionPoint V.X p) :
    fiberedCycleClassDefect (V := V) (H := H) (p := p)
      (atom V H p i x) =
      H.cycleClass p
          (GSTNativeCodimensionCyclePresentation.codimensionPointCycle V.X p x) -
        (classicalHodgeBasis V H p i).1 := by
  simp [fiberedCycleClassDefect]

/-- Defect zero on one atom is exactly the desired genuine classical equality
for that point cycle and Hodge basis direction. -/
theorem fiberedCycleClassDefect_atom_eq_zero_iff
    (i : ClassicalHodgeBasisIndex V H p)
    (x : GSTNativeCodimensionCyclePresentation.CodimensionPoint V.X p) :
    fiberedCycleClassDefect (V := V) (H := H) (p := p)
        (atom V H p i x) = 0 ↔
      H.cycleClass p
          (GSTNativeCodimensionCyclePresentation.codimensionPointCycle V.X p x) =
        (classicalHodgeBasis V H p i).1 := by
  rw [fiberedCycleClassDefect_atom]
  exact sub_eq_zero

/-- The normalized GST spectral atom has the same Hodge face as the selected
live basis sheet and the same native face as the chosen genuine point.  Its
classical defect is therefore the same atomic difference. -/
theorem normalizedSpectralAtom_defect
    (alpha : ClassicalHodgeFiber V H p)
    (S : GSTWorldShape (liveRank alpha))
    (y : ShapeState S)
    (x : GSTNativeCodimensionCyclePresentation.CodimensionPoint V.X p) :
    fiberedCycleClassDefect (V := V) (H := H) (p := p)
        (normalizedSpectralAtom alpha S y x) =
      H.cycleClass p
          (GSTNativeCodimensionCyclePresentation.codimensionPointCycle V.X p x) -
        (classicalHodgeBasis V H p
          (shapedLiveBasisIndex alpha S y)).1 := by
  unfold fiberedCycleClassDefect fiberedNativeCycleClass fiberedHodgeAmbient
  rw [LinearMap.sub_apply]
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  rw [normalized_nativeFace_exact alpha S y x]
  have hhodge :
      fiberedHodgeClass (V := V) (H := H) (p := p)
        (normalizedSpectralAtom alpha S y x) =
        classicalHodgeBasis V H p (shapedLiveBasisIndex alpha S y) := by
    apply (classicalHodgeBasis V H p).repr.injective
    apply Finsupp.embDomain_injective (weightFiberEmbedding V H p)
    simpa [fiberedHodgeClass] using normalized_hodgeFace_exact alpha S y x
  rw [hhodge]
  rfl

/-- A fibered state is a genuine classical landing state precisely when its
native cycle class equals its reconstructed Hodge face. -/
theorem defect_eq_zero_iff_faces_agree
    (Φ : FiberedNativeAddress V H p) :
    fiberedCycleClassDefect (V := V) (H := H) (p := p) Φ = 0 ↔
      H.cycleClass p (toNativeCycle V H p Φ) =
        (fiberedHodgeClass (V := V) (H := H) (p := p) Φ).1 := by
  change
    fiberedNativeCycleClass (V := V) (H := H) (p := p) Φ -
        fiberedHodgeAmbient (V := V) (H := H) (p := p) Φ = 0 ↔ _
  simp [fiberedNativeCycleClass, fiberedHodgeAmbient, sub_eq_zero]

/-! ## Interaction invisibility

The joint interaction sector cannot change the classical landing defect.
This is stronger than saying the two marginals determine the limitless base
address: the *actual* cycle-class defect itself is constant on every coset of
the joint-kernel interaction space.
-/

/-- Any fibered state with both marginals zero has zero classical defect. -/
theorem fiberedCycleClassDefect_eq_zero_of_zero_marginals
    (Φ : FiberedNativeAddress V H p)
    (hPoint : forgetPoint V H p Φ = 0)
    (hNative : forgetMultiplicity V H p Φ = 0) :
    fiberedCycleClassDefect (V := V) (H := H) (p := p) Φ = 0 := by
  unfold fiberedCycleClassDefect fiberedNativeCycleClass
    fiberedHodgeAmbient fiberedHodgeClass toNativeCycle
  simp [hPoint, hNative]

/-- Every explicit four-corner interaction rectangle is invisible to the
cycle-class defect. -/
@[simp]
theorem fiberedCycleClassDefect_interactionRectangle
    (i₀ i : ClassicalHodgeBasisIndex V H p)
    (x₀ x : GSTNativeCodimensionCyclePresentation.CodimensionPoint V.X p) :
    fiberedCycleClassDefect (V := V) (H := H) (p := p)
      (interactionRectangle i₀ i x₀ x) = 0 := by
  apply fiberedCycleClassDefect_eq_zero_of_zero_marginals
  · exact interactionRectangle_forgetPoint i₀ i x₀ x
  · exact interactionRectangle_forgetMultiplicity i₀ i x₀ x

/-- The whole interaction projection lands in the defect kernel. -/
@[simp]
theorem fiberedCycleClassDefect_interactionProjection
    (i₀ : ClassicalHodgeBasisIndex V H p)
    (x₀ : GSTNativeCodimensionCyclePresentation.CodimensionPoint V.X p)
    (Φ : FiberedNativeAddress V H p) :
    fiberedCycleClassDefect (V := V) (H := H) (p := p)
      (interactionProjection i₀ x₀ Φ) = 0 := by
  apply fiberedCycleClassDefect_eq_zero_of_zero_marginals
  · exact interactionProjection_forgetPoint i₀ x₀ Φ
  · exact interactionProjection_forgetMultiplicity i₀ x₀ Φ

/-- Equal classical and native marginals force equal defects.  Thus no motion
inside the joint interaction fiber can alter the genuine classical
cycle-class obstruction. -/
theorem fiberedCycleClassDefect_eq_of_equal_marginals
    (Φ Ψ : FiberedNativeAddress V H p)
    (hPoint : forgetPoint V H p Φ = forgetPoint V H p Ψ)
    (hNative :
      forgetMultiplicity V H p Φ = forgetMultiplicity V H p Ψ) :
    fiberedCycleClassDefect (V := V) (H := H) (p := p) Φ =
      fiberedCycleClassDefect (V := V) (H := H) (p := p) Ψ := by
  unfold fiberedCycleClassDefect fiberedNativeCycleClass
    fiberedHodgeAmbient fiberedHodgeClass toNativeCycle
  rw [hPoint, hNative]

/-- Reconstructing only the two marginals preserves the defect exactly.  The
discarded interaction component contributes zero. -/
theorem fiberedCycleClassDefect_marginalReconstruction
    (i₀ : ClassicalHodgeBasisIndex V H p)
    (x₀ : GSTNativeCodimensionCyclePresentation.CodimensionPoint V.X p)
    (Φ : FiberedNativeAddress V H p) :
    fiberedCycleClassDefect (V := V) (H := H) (p := p)
        (marginalReconstruction i₀ x₀ Φ) =
      fiberedCycleClassDefect (V := V) (H := H) (p := p) Φ := by
  apply fiberedCycleClassDefect_eq_of_equal_marginals
  · exact marginalReconstruction_forgetPoint i₀ x₀ Φ
  · exact marginalReconstruction_forgetMultiplicity i₀ x₀ Φ

/-- The complete joint kernel sits inside the kernel of the classical defect
map.  This formally rules out interaction-only corrections of a nonzero
landing defect. -/
theorem jointKernel_le_cycleClassDefectKernel
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) :
    (forgetPoint V H p).ker ⊓ (forgetMultiplicity V H p).ker ≤
      (fiberedCycleClassDefect (V := V) (H := H) (p := p)).ker := by
  intro Φ hΦ
  exact fiberedCycleClassDefect_eq_zero_of_zero_marginals Φ hΦ.1 hΦ.2

/-- Equivalently, the explicit four-corner rectangle span is annihilated by
the classical defect. -/
theorem rectangleSpan_le_cycleClassDefectKernel
    (i₀ : ClassicalHodgeBasisIndex V H p)
    (x₀ : GSTNativeCodimensionCyclePresentation.CodimensionPoint V.X p) :
    Submodule.span ℚ
        (Set.range (fun ix : FiberedNativeAtom V H p =>
          interactionRectangle i₀ ix.1 x₀ ix.2)) ≤
      (fiberedCycleClassDefect (V := V) (H := H) (p := p)).ker := by
  rw [← jointKernel_eq_rectangleSpan i₀ x₀]
  exact jointKernel_le_cycleClassDefectKernel V H p

/-- If one defect-zero fibered state realizes every Hodge basis sheet, then the
exact Stage-2G statement follows by unrestricted finite-support reconstruction.
This is a linear-algebra landing theorem; the states themselves are to be
manufactured by the limitless/native operator arsenal. -/
theorem bigradedBettiHodge_of_defectZero_basisStates
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (state : ∀ p : Nat, ClassicalHodgeBasisIndex V H p →
      FiberedNativeAddress V H p)
    (hhodge : ∀ p i,
      fiberedHodgeClass (V := V) (H := H) (p := p) (state p i) =
        classicalHodgeBasis V H p i)
    (hdefect : ∀ p i,
      fiberedCycleClassDefect (V := V) (H := H) (p := p) (state p i) = 0) :
    BigradedBettiHodgeStatement V H := by
  intro p alpha halpha
  let R : ClassicalHodgeBasisIndex V H p →
      codimensionCycles V.X p := fun i => toNativeCycle V H p (state p i)
  have hR : ∀ i,
      H.cycleClass p (R i) = (classicalHodgeBasis V H p i).1 := by
    intro i
    have hz := (defect_eq_zero_iff_faces_agree
      (V := V) (H := H) (p := p) (state p i)).mp (hdefect p i)
    simpa [R, hhodge p i] using hz
  let lift : ClassicalHodgeFiber V H p →ₗ[ℚ] codimensionCycles V.X p :=
    (classicalHodgeBasis V H p).constr ℚ R
  let alphaH : ClassicalHodgeFiber V H p := ⟨alpha, halpha⟩
  refine ⟨lift alphaH, ?_⟩
  have hmaps : (H.cycleClass p).comp lift =
      (rationalHodgeSubspace (H.hodgeBigrading p)).subtype := by
    apply (classicalHodgeBasis V H p).ext
    intro i
    simp [lift, hR]
  change ((H.cycleClass p).comp lift) alphaH = alpha
  rw [hmaps]
  rfl

#check fiberedCycleClassDefect_eq_zero_of_zero_marginals
#check fiberedCycleClassDefect_interactionRectangle
#check fiberedCycleClassDefect_interactionProjection
#check fiberedCycleClassDefect_eq_of_equal_marginals
#check fiberedCycleClassDefect_marginalReconstruction
#check jointKernel_le_cycleClassDefectKernel
#check rectangleSpan_le_cycleClassDefectKernel

#print axioms fiberedCycleClassDefect_interactionRectangle
#print axioms fiberedCycleClassDefect_interactionProjection
#print axioms fiberedCycleClassDefect_eq_of_equal_marginals
#print axioms rectangleSpan_le_cycleClassDefectKernel

#check fiberedHodgeClass
#check fiberedNativeCycleClass
#check fiberedCycleClassDefect
#check fiberedCycleClassDefect_atom
#check normalizedSpectralAtom_defect
#check defect_eq_zero_iff_faces_agree
#check bigradedBettiHodge_of_defectZero_basisStates

#print axioms fiberedCycleClassDefect_atom
#print axioms normalizedSpectralAtom_defect
#print axioms defect_eq_zero_iff_faces_agree
#print axioms bigradedBettiHodge_of_defectZero_basisStates

end GSTClassicalHodgeFiberedCycleClassDefect
