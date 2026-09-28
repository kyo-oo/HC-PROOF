import GSTClassicalHodgeFiberedCycleClassDefect
import GSTClassicalHodgeSeparatorProbe
import GSTClassicalHodgeThreeUniverseSeedIdentification

/-!
# GST CLASSICAL HODGE — PERSISTENT VERTICAL DEFECT

A failure separator does much more than merely witness that one Hodge class is
outside the algebraic range.  Once its completed Hodge probe is expanded in the
genuine unrestricted basis, some basis sheet is detected nontrivially.  On
that sheet the separator reads the classical fibered defect with the SAME
nonzero value for every genuine native codimension-p point.

Indeed the native point-class term is annihilated by the separator, so the
only surviving read is the negative value on the detected Hodge basis vector.
Changing the native point cannot change this number.

This isolates the true vertical obstruction left after the limitless
three-universe identification: all unit native points and all genuine Hodge
basis sheets share the same base transfer address, but a hypothetical Hodge
failure would force one multiplicity sheet to carry a nonzero classical defect
against every native point above that address.

The result is an exact contradiction target for any later geometric
recoordination / correspondence / observation theorem: it is enough to force
ONE point over the detected sheet to have zero defect.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgePersistentVerticalDefect

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicAnnihilator
open GSTClassicalHodgeSeparatorProbe
open GSTClassicalHodgeFiberedNativePullback
open GSTClassicalHodgeFiberedCycleClassDefect
open GSTClassicalHodgeThreeUniverseSeedIdentification
open GSTClassicalHodgeNativeCycleCosmicShadow
open GSTClassicalHodgeNativeTransferAddressIdentification
open GSTTransferBridgeV2

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- A nonzero separator probe must detect at least one genuine unrestricted
Hodge basis sheet. -/
theorem AtomicSeparatorProbe.exists_detected_basis
    (S : AtomicSeparatorProbe V H p) :
    ∃ i : ClassicalHodgeBasisIndex V H p,
      S.detector (classicalHodgeBasis V H p i).1 ≠ 0 := by
  by_contra hnone
  push_neg at hnone
  have hprobeZero :
      functionalHodgeProbe V H p S.detector = 0 := by
    funext i
    exact hnone i
  apply S.pairing_nonzero
  rw [hprobeZero]
  simp [hodgeFiberPairing]

/-- On a detected basis sheet, the separator read of the atomic classical
defect is the negative basis read and is independent of the native point. -/
theorem AtomicSeparatorProbe.detector_atom_defect
    (S : AtomicSeparatorProbe V H p)
    (i : ClassicalHodgeBasisIndex V H p)
    (x : CodimensionPoint V.X p) :
    S.detector
        (fiberedCycleClassDefect (V := V) (H := H) (p := p)
          (atom V H p i x)) =
      - S.detector (classicalHodgeBasis V H p i).1 := by
  rw [fiberedCycleClassDefect_atom]
  rw [map_sub]
  rw [S.annihilates_atoms x]
  simp

/-- Hence every native point over a detected multiplicity sheet has nonzero
classical defect.  There is no exceptional point that can repair the failure. -/
theorem AtomicSeparatorProbe.atom_defect_ne_zero_of_detected
    (S : AtomicSeparatorProbe V H p)
    (i : ClassicalHodgeBasisIndex V H p)
    (hi : S.detector (classicalHodgeBasis V H p i).1 ≠ 0)
    (x : CodimensionPoint V.X p) :
    fiberedCycleClassDefect (V := V) (H := H) (p := p)
        (atom V H p i x) ≠ 0 := by
  intro hz
  have hread := congrArg S.detector hz
  rw [LinearMap.map_zero] at hread
  rw [S.detector_atom_defect i x] at hread
  exact hi (neg_eq_zero.mp hread)

/-- The separator read of the defect is literally constant across any two
native points over the same Hodge sheet. -/
theorem AtomicSeparatorProbe.detector_atom_defect_point_independent
    (S : AtomicSeparatorProbe V H p)
    (i : ClassicalHodgeBasisIndex V H p)
    (x y : CodimensionPoint V.X p) :
    S.detector
        (fiberedCycleClassDefect (V := V) (H := H) (p := p)
          (atom V H p i x)) =
      S.detector
        (fiberedCycleClassDefect (V := V) (H := H) (p := p)
          (atom V H p i y)) := by
  rw [S.detector_atom_defect i x, S.detector_atom_defect i y]

/-- Package the persistent vertical obstruction carried by one detected sheet. -/
structure PersistentVerticalDefect
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) where
  sheet : ClassicalHodgeBasisIndex V H p
  detector :
    RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ] ℚ
  annihilates_atoms :
    AnnihilatesPointCycleClasses p (H.cycleClass p) detector
  sheet_read_ne_zero :
    detector (classicalHodgeBasis V H p sheet).1 ≠ 0

namespace PersistentVerticalDefect

/-- Defect readout over any native point is the same fixed nonzero charge. -/
theorem read_defect
    (D : PersistentVerticalDefect V H p)
    (x : CodimensionPoint V.X p) :
    D.detector
        (fiberedCycleClassDefect (V := V) (H := H) (p := p)
          (atom V H p D.sheet x)) =
      - D.detector (classicalHodgeBasis V H p D.sheet).1 := by
  rw [fiberedCycleClassDefect_atom, map_sub, D.annihilates_atoms x]
  simp

/-- The vertical defect itself is nonzero above every native point. -/
theorem defect_ne_zero
    (D : PersistentVerticalDefect V H p)
    (x : CodimensionPoint V.X p) :
    fiberedCycleClassDefect (V := V) (H := H) (p := p)
        (atom V H p D.sheet x) ≠ 0 := by
  intro hz
  have hread := congrArg D.detector hz
  rw [LinearMap.map_zero, D.read_defect x] at hread
  exact D.sheet_read_ne_zero (neg_eq_zero.mp hread)

/-- Despite the persistent nonzero vertical defect, the classical sheet and
any unit native point have exactly the same multiplicity-forgotten limitless
transfer address. -/
theorem base_limitless_address_agrees
    (D : PersistentVerticalDefect V H p)
    (x : CodimensionPoint V.X p) :
    forgetMultiplicityToGST (fiberedSheetGenerator V H ⟨p, D.sheet⟩) =
      pureWeightToUniversalAddress
        (nativeCycleCosmicShadow V p (codimensionPointCycle V.X p x)) := by
  exact classicalBasis_baseAddress_eq_nativePoint V H p D.sheet x

/-- The common base address is the established limitless transfer generator. -/
theorem base_limitless_address_is_transfer
    (D : PersistentVerticalDefect V H p)
    (x : CodimensionPoint V.X p) :
    forgetMultiplicityToGST (fiberedSheetGenerator V H ⟨p, D.sheet⟩) =
      rationalizeCompactAddress (compactClMono p) := by
  exact classicalSheet_eq_rationalized_transfer V H p D.sheet

end PersistentVerticalDefect

/-- Every atomic separator canonically yields a persistent vertical defect
sheet. -/
noncomputable def AtomicSeparatorProbe.toPersistentVerticalDefect
    (S : AtomicSeparatorProbe V H p) :
    PersistentVerticalDefect V H p := by
  let i := Classical.choose S.exists_detected_basis
  exact {
    sheet := i
    detector := S.detector
    annihilates_atoms := S.annihilates_atoms
    sheet_read_ne_zero := Classical.choose_spec S.exists_detected_basis
  }

/-- **FAILURE FORCES A PERSISTENT VERTICAL DEFECT.** -/
theorem not_hodge_yields_persistentVerticalDefect
    (hnot : ¬ BigradedBettiHodgeStatement V H) :
    ∃ p : Nat, Nonempty (PersistentVerticalDefect V H p) := by
  obtain ⟨p, hS⟩ :=
    (not_bigradedBettiHodgeStatement_iff_exists_separatorProbe V H).mp hnot
  rcases hS with ⟨S⟩
  exact ⟨p, ⟨S.toPersistentVerticalDefect⟩⟩

/-- Conversely, the existence of a persistent vertical defect already contains
an atomic separator and therefore refutes the Hodge target. -/
theorem persistentVerticalDefect_implies_not_hodge
    (p : Nat)
    (D : PersistentVerticalDefect V H p) :
    ¬ BigradedBettiHodgeStatement V H := by
  intro hHodge
  have hrange :
      (classicalHodgeBasis V H p D.sheet).1 ∈
        LinearMap.range (H.cycleClass p) :=
    hHodge p (classicalHodgeBasis V H p D.sheet).2
  have hatomic :
      (classicalHodgeBasis V H p D.sheet).1 ∈
        GSTClassicalHodgeAtomicSpan.pointCycleClassSpan p (H.cycleClass p) := by
    rwa [GSTClassicalHodgeAtomicSpan.smoothProjective_cycleClass_range_eq_atomic_span
      V H p] at hrange
  have hker :
      GSTClassicalHodgeAtomicSpan.pointCycleClassSpan p (H.cycleClass p) ≤
        LinearMap.ker D.detector :=
    (annihilatesPointCycles_iff_atomicSpan_le_ker
      p (H.cycleClass p) D.detector).mp D.annihilates_atoms
  exact D.sheet_read_ne_zero (hker hatomic)

/-- Exact obstruction equivalence. -/
theorem hodge_failure_iff_exists_persistentVerticalDefect :
    (¬ BigradedBettiHodgeStatement V H) ↔
      ∃ p : Nat, Nonempty (PersistentVerticalDefect V H p) := by
  constructor
  · exact not_hodge_yields_persistentVerticalDefect
  · rintro ⟨p, ⟨D⟩⟩
    exact persistentVerticalDefect_implies_not_hodge p D

#check AtomicSeparatorProbe.exists_detected_basis
#check AtomicSeparatorProbe.detector_atom_defect
#check AtomicSeparatorProbe.atom_defect_ne_zero_of_detected
#check PersistentVerticalDefect
#check PersistentVerticalDefect.read_defect
#check PersistentVerticalDefect.defect_ne_zero
#check PersistentVerticalDefect.base_limitless_address_agrees
#check AtomicSeparatorProbe.toPersistentVerticalDefect
#check not_hodge_yields_persistentVerticalDefect
#check hodge_failure_iff_exists_persistentVerticalDefect

#print axioms AtomicSeparatorProbe.exists_detected_basis
#print axioms AtomicSeparatorProbe.detector_atom_defect
#print axioms AtomicSeparatorProbe.atom_defect_ne_zero_of_detected
#print axioms not_hodge_yields_persistentVerticalDefect
#print axioms hodge_failure_iff_exists_persistentVerticalDefect

end GSTClassicalHodgePersistentVerticalDefect
