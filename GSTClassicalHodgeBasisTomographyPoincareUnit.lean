import GSTClassicalHodgeAtomicDefectTomographyGhost
import GSTLefschetzPoincareReciprocity

/-!
# GST CLASSICAL HODGE — BASIS TOMOGRAPHY / POINCARE UNIT

A genuine chosen Hodge basis vector is not merely finite support: its fibered
address is exactly one Finsupp atom.  Therefore its local multiplicity chart has
one live coordinate.  On that one-sheet chart the triangular Lefschetz
transform has no lower terms and the unique coefficient is exactly one.

This identifies the nonzero tomography signal of a ghost basis sheet with the
unit transition amplitude of the one-cell GST world.  Poincare reversal fixes
the unique cell, so the reverse amplitude is the same unit.

The result removes every arbitrary scalar from the INTERNAL GST side of the
first-ghost return problem.  Any external transpose/cycle-class return only has
to couple to this one canonical unit reverse amplitude.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeBasisTomographyPoincareUnit

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeFiniteSupportChart
open GSTClassicalHodgeLefschetzTomography
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeOmniversalSeparatorGhostCrown
open GSTClassicalHodgeAtomicDefectTomographyGhost
open GSTWorldCosmology
open GSTWorldPoincareDuality
open GSTTruncatedWorldCohomologyRing
open GSTLefschetzPoincareReciprocity

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- One chosen Hodge basis vector has exactly one live fibered coordinate. -/
theorem basis_fiberedSupportSize_eq_one
    (i : ClassicalHodgeBasisIndex V H p) :
    fiberedSupportSize
      (fiberedWeightCoordinates V H p (classicalHodgeBasis V H p i)) = 1 := by
  rw [fiberedWeightCoordinates_basis]
  unfold fiberedSupportSize LiveFiberedAddress
  classical
  simp

/-- Every coordinate of the singleton support vector is the unit coefficient.
The target is `Fin 1` after rewriting the support cardinality. -/
theorem basis_supportCoordinateVector_eq_one
    (i : ClassicalHodgeBasisIndex V H p) :
    let f := fiberedWeightCoordinates V H p (classicalHodgeBasis V H p i)
    ∀ q : Fin (fiberedSupportSize f), supportCoordinateVector f q = 1 := by
  intro f q
  have hsize : fiberedSupportSize f = 1 := by
    simpa [f] using basis_fiberedSupportSize_eq_one (V := V) (H := H) i
  have hsingle :
      f = Finsupp.single (⟨p,i⟩ : FiberedHodgeIndex V H) 1 := by
    simpa [f] using fiberedWeightCoordinates_basis V H p i
  unfold supportCoordinateVector
  have hlive :
      (((fiberedSupportEquivFin f).symm q).1) ∈ f.support :=
    ((fiberedSupportEquivFin f).symm q).2
  rw [hsingle] at hlive ⊢
  classical
  have haddr :
      ((fiberedSupportEquivFin f).symm q).1 =
        (⟨p,i⟩ : FiberedHodgeIndex V H) := by
    simpa using hlive
  simp [haddr]

/-- The exact finite Lefschetz tomography of a chosen basis sheet is the
constant unit vector. -/
theorem basis_lefschetzTomography_eq_one
    (i : ClassicalHodgeBasisIndex V H p) :
    let f := fiberedWeightCoordinates V H p (classicalHodgeBasis V H p i)
    ∀ q : Fin (fiberedSupportSize f),
      lefschetzTomography (supportCoordinateVector f) q = 1 := by
  intro f q
  rw [lefschetzTomography_triangular]
  rw [basis_supportCoordinateVector_eq_one (V := V) (H := H) i q]
  have hq0 : q.1 = 0 := by
    have hsize : fiberedSupportSize f = 1 := by
      simpa [f] using basis_fiberedSupportSize_eq_one (V := V) (H := H) i
    omega
  have hsum :
      (∑ j : Fin (fiberedSupportSize f) with j.1 < q.1,
        multiplicityLefschetzKernel j q * supportCoordinateVector f j) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hlt := (Finset.mem_filter.mp hj).2
    omega
  rw [hsum, add_zero]

/-- Hence the ghost-selected tomography scalar from the older existence-based
construction is actually exactly one. -/
theorem ghostTomographyScalar_eq_one
    {G : GeometricCycleClassSpine V H}
    (E : OmniversalSeparatorGhost G) :
    GSTClassicalHodgeAtomicDefectTomographySynchronization.ghostTomographyScalar E = 1 := by
  unfold GSTClassicalHodgeAtomicDefectTomographySynchronization.ghostTomographyScalar
  let q := Classical.choose (ghost_basis_has_nonzero_lefschetzMoment E)
  exact basis_lefschetzTomography_eq_one
    (V := V) (H := H) E.sheet q

/-- The unique one-cell GST state is fixed by Poincare duality. -/
theorem oneCell_worldDual
    (s : WorldCell 1 1) : worldDual s = s := by
  apply Prod.ext <;> apply Fin.ext <;> omega

/-- The unique zero-time one-cell transition has unit amplitude. -/
theorem oneCell_unit_transition
    (s : WorldCell 1 1) :
    worldAct 1 1 ((L 1 1)^0) (worldBasis s) s = 1 := by
  simp

/-- **POINCARE UNIT RECIPROCITY.**  The canonical unit transition and its
Poincare-reversed transition are literally the same unit amplitude. -/
theorem oneCell_poincare_reverse_unit
    (s : WorldCell 1 1) :
    worldAct 1 1 ((L 1 1)^0) (worldBasis (worldDual s)) (worldDual s) = 1 := by
  rw [oneCell_worldDual]
  exact oneCell_unit_transition s

/-- Crown: every obstructed Hodge basis sheet carries the canonical internal
GST unit tomography signal, and the signal survives Poincare reversal exactly. -/
theorem ghost_basis_poincare_unit_crown
    {G : GeometricCycleClassSpine V H}
    (E : OmniversalSeparatorGhost G) :
    GSTClassicalHodgeAtomicDefectTomographySynchronization.ghostTomographyScalar E = 1
      ∧ ∀ s : WorldCell 1 1,
        worldAct 1 1 ((L 1 1)^0)
          (worldBasis (worldDual s)) (worldDual s) = 1 := by
  exact ⟨ghostTomographyScalar_eq_one E,
    oneCell_poincare_reverse_unit⟩

#check basis_fiberedSupportSize_eq_one
#check basis_supportCoordinateVector_eq_one
#check basis_lefschetzTomography_eq_one
#check ghostTomographyScalar_eq_one
#check oneCell_worldDual
#check oneCell_unit_transition
#check oneCell_poincare_reverse_unit
#check ghost_basis_poincare_unit_crown

#print axioms basis_fiberedSupportSize_eq_one
#print axioms basis_lefschetzTomography_eq_one
#print axioms ghostTomographyScalar_eq_one
#print axioms oneCell_poincare_reverse_unit
#print axioms ghost_basis_poincare_unit_crown

end GSTClassicalHodgeBasisTomographyPoincareUnit
