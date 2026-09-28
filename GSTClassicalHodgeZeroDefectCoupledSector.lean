import GSTClassicalHodgeFiberedDefectEquivariance
import GSTClassicalHodgeFiberedSeparatorDefect

/-!
# GST CLASSICAL HODGE — ZERO-DEFECT COUPLED SECTOR

The fibered/native universe contains two independent faces at one Hodge
weight: a genuine native codimension-p cycle and a genuine classical Hodge
multiplicity state.  Their difference is the already-defined
`fiberedCycleClassDefect`.

This module turns exact native/Hodge agreement into an intrinsic submodule:
the kernel of that defect map.  This is the precise coupled sector on which a
future GST/native transitivity theorem has to act.  It is deliberately not a
surjectivity assumption and carries no basis-cycle witnesses.

Three facts are recorded here.

* membership is exactly equality of the native cycle class and the Hodge face;
* every Hodge face occurring in this sector is automatically an actual cycle
  class;
* the existing cycle-natural tensor equivariance theorem becomes a genuine
  closure theorem for zero-defect source atoms.

Conversely an atomic separator excludes every normalized spectral atom in its
obstructed sheet from this sector.  Thus a Hodge counterexample is now a
literal missing point of one linear GST/native kernel, while every valid
coupled geometric transport preserves that kernel whenever its native mass and
Hodge transfer agree.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeZeroDefectCoupledSector

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeFiberedNativePullback
open GSTClassicalHodgeNormalizedFiberedSpectralAtom
open GSTClassicalHodgeFiberedCycleClassDefect
open GSTClassicalHodgeFiberedDefectEquivariance
open GSTClassicalHodgeFiberedSeparatorDefect
open GSTClassicalHodgeSingleSheetCrown

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- The genuine coupled native/Hodge sector: exactly those fibered states for
which the actual native cycle class equals the reconstructed Hodge face. -/
noncomputable def zeroDefectSector :
    Submodule ℚ (FiberedNativeAddress V H p) :=
  LinearMap.ker
    (fiberedCycleClassDefect (V := V) (H := H) (p := p))

@[simp]
theorem mem_zeroDefectSector_iff
    (Φ : FiberedNativeAddress V H p) :
    Φ ∈ zeroDefectSector (V := V) (H := H) (p := p) ↔
      H.cycleClass p (toNativeCycle V H p Φ) =
        (fiberedHodgeClass (V := V) (H := H) (p := p) Φ).1 := by
  rw [zeroDefectSector, LinearMap.mem_ker]
  exact defect_eq_zero_iff_faces_agree Φ

/-- Every Hodge face carried by the zero-defect sector is already in the
actual native cycle-class range, witnessed by that state's native face. -/
theorem hodgeFace_mem_cycleClass_range
    (Φ : FiberedNativeAddress V H p)
    (hΦ : Φ ∈ zeroDefectSector (V := V) (H := H) (p := p)) :
    (fiberedHodgeClass (V := V) (H := H) (p := p) Φ).1 ∈
      LinearMap.range (H.cycleClass p) := by
  refine ⟨toNativeCycle V H p Φ, ?_⟩
  exact (mem_zeroDefectSector_iff Φ).mp hΦ

/-- A zero-defect state whose Hodge face is one genuine basis sheet therefore
materializes that sheet by its native face. -/
theorem basis_mem_cycleClass_range_of_zeroDefect_state
    (i : ClassicalHodgeBasisIndex V H p)
    (Φ : FiberedNativeAddress V H p)
    (hΦ : Φ ∈ zeroDefectSector (V := V) (H := H) (p := p))
    (hface :
      fiberedHodgeClass (V := V) (H := H) (p := p) Φ =
        classicalHodgeBasis V H p i) :
    (classicalHodgeBasis V H p i).1 ∈
      LinearMap.range (H.cycleClass p) := by
  simpa [hface] using hodgeFace_mem_cycleClass_range Φ hΦ

/-- For a normalized coupled spectral atom, membership in the zero-defect
sector is exactly the missing classical equality between its genuine point
cycle and its selected live Hodge basis sheet. -/
theorem normalizedSpectralAtom_mem_zeroDefectSector_iff
    (alpha : ClassicalHodgeFiber V H p)
    (S : GSTWorldShape (liveRank alpha))
    (y : ShapeState S)
    (x : CodimensionPoint V.X p) :
    normalizedSpectralAtom alpha S y x ∈
        zeroDefectSector (V := V) (H := H) (p := p) ↔
      H.cycleClass p (codimensionPointCycle V.X p x) =
        (classicalHodgeBasis V H p
          (shapedLiveBasisIndex alpha S y)).1 := by
  rw [zeroDefectSector, LinearMap.mem_ker]
  rw [normalizedSpectralAtom_defect]
  exact sub_eq_zero

/-- An atomic separator proves that every normalized spectral atom carrying its
obstructed sheet lies outside the genuine zero-defect sector. -/
theorem separator_excludes_normalizedSpectralAtom
    {i : ClassicalHodgeBasisIndex V H p}
    (Sep : BasisAtomicSeparator V H p i)
    (alpha : ClassicalHodgeFiber V H p)
    (S : GSTWorldShape (liveRank alpha))
    (y : ShapeState S)
    (x : CodimensionPoint V.X p)
    (hy : shapedLiveBasisIndex alpha S y = i) :
    normalizedSpectralAtom alpha S y x ∉
      zeroDefectSector (V := V) (H := H) (p := p) := by
  intro hmem
  have hz :
      fiberedCycleClassDefect (V := V) (H := H) (p := p)
        (normalizedSpectralAtom alpha S y x) = 0 := by
    exact hmem
  exact
    (separator_detects_normalizedSpectralAtom_defect
      Sep alpha S y x hy) hz

/-- Existing tensor equivariance, recast as closure of the coupled sector on a
source atom.  This is the exact positive geometric mechanism that may move a
classically landed source through the GST multiplicity universe without
leaving native geometry. -/
theorem tensorWord_atom_mem_zeroDefectSector
    (T : GSTClassicalHodgeCycleOperatorNaturality.CycleClassOperatorPair V H p)
    (i j : ClassicalHodgeBasisIndex V H p)
    (x : CodimensionPoint V.X p)
    (hT : TensorIntertwinesAt T i j x)
    (hsource :
      atom V H p i x ∈ zeroDefectSector (V := V) (H := H) (p := p)) :
    GSTClassicalHodgeFiberedNativeTensorArsenal.tensorWord
        i j T.cycleOperator (atom V H p i x) ∈
      zeroDefectSector (V := V) (H := H) (p := p) := by
  change
    fiberedCycleClassDefect (V := V) (H := H) (p := p)
      (GSTClassicalHodgeFiberedNativeTensorArsenal.tensorWord
        i j T.cycleOperator (atom V H p i x)) = 0
  apply defectZero_tensorWord_atom T i j x hT
  exact hsource

/-- Uniform genuine tensor transport closes the zero-defect sector on every
source atom in its source sheet. -/
theorem uniformTensorIntertwiner_atom_mem_zeroDefectSector
    (T : GSTClassicalHodgeCycleOperatorNaturality.CycleClassOperatorPair V H p)
    (i j : ClassicalHodgeBasisIndex V H p)
    (hT : UniformTensorIntertwiner T i j)
    (x : CodimensionPoint V.X p)
    (hsource :
      atom V H p i x ∈ zeroDefectSector (V := V) (H := H) (p := p)) :
    GSTClassicalHodgeFiberedNativeTensorArsenal.tensorWord
        i j T.cycleOperator (atom V H p i x) ∈
      zeroDefectSector (V := V) (H := H) (p := p) := by
  exact tensorWord_atom_mem_zeroDefectSector
    T i j x (hT.at x) hsource

/-- Separator-level collision: no genuine zero-defect state can carry the
obstructed Hodge basis sheet.  Unlike an exact matrix-unit realization, this
statement only refers to the intrinsic coupled sector. -/
theorem separator_forbids_zeroDefect_basis_state
    {i : ClassicalHodgeBasisIndex V H p}
    (Sep : BasisAtomicSeparator V H p i) :
    ¬ ∃ Φ : FiberedNativeAddress V H p,
        Φ ∈ zeroDefectSector (V := V) (H := H) (p := p) ∧
        fiberedHodgeClass (V := V) (H := H) (p := p) Φ =
          classicalHodgeBasis V H p i := by
  rintro ⟨Φ, hΦ, hface⟩
  have hrange :=
    basis_mem_cycleClass_range_of_zeroDefect_state i Φ hΦ hface
  rcases hrange with ⟨Z, hZ⟩
  have hzero : Sep.detector (H.cycleClass p Z) = 0 := by
    have hker :
        GSTClassicalHodgeAtomicSpan.pointCycleClassSpan p (H.cycleClass p) ≤
          LinearMap.ker Sep.detector :=
      (GSTClassicalHodgeAtomicAnnihilator.annihilatesPointCycles_iff_atomicSpan_le_ker
        p (H.cycleClass p) Sep.detector).mp Sep.annihilates_atoms
    apply hker
    rw [← GSTClassicalHodgeAtomicSpan.smoothProjective_cycleClass_range_eq_atomic_span
      V H p]
    exact ⟨Z, rfl⟩
  rw [hZ] at hzero
  exact Sep.detects_basis hzero

#check zeroDefectSector
#check mem_zeroDefectSector_iff
#check hodgeFace_mem_cycleClass_range
#check basis_mem_cycleClass_range_of_zeroDefect_state
#check normalizedSpectralAtom_mem_zeroDefectSector_iff
#check separator_excludes_normalizedSpectralAtom
#check tensorWord_atom_mem_zeroDefectSector
#check uniformTensorIntertwiner_atom_mem_zeroDefectSector
#check separator_forbids_zeroDefect_basis_state

#print axioms mem_zeroDefectSector_iff
#print axioms hodgeFace_mem_cycleClass_range
#print axioms separator_excludes_normalizedSpectralAtom
#print axioms tensorWord_atom_mem_zeroDefectSector
#print axioms separator_forbids_zeroDefect_basis_state

end GSTClassicalHodgeZeroDefectCoupledSector
