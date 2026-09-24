import Mathlib
import GSTWorldCosmology

/-!
# GST LIMITLESS WORLD — unbounded algebraic cosmos and finite windows

This file removes the terminal rectangle from the strongest world carrier.
Finite `A × B` worlds remain exact observation windows, while the limitless
algebraic carrier is the finitely-supported integer field on `Nat × Nat`.

No finite boundary is erased.  Instead, boundary extinction belongs to the
window in which it is observed.  The limitless carrier itself has no final
row or column.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

namespace GSTLimitlessWorld

open GSTWorldCosmology

/-- A cell in the limitless GST cosmos.  There is no terminal row or column. -/
abbrev CosmicCell : Type := Nat × Nat

/-- The compact algebraic face of the limitless cosmos: integer amplitudes
with finite support on the unbounded grid. -/
abbrev CosmicCoef : Type := CosmicCell →₀ ℤ

/-- Forget the finite bounds of a window cell and read its cosmic address. -/
def windowCell {carryDepth digitDepth : Nat}
    (c : WorldCell carryDepth digitDepth) : CosmicCell :=
  (c.1.1, c.2.1)

/-- Window-cell coordinates lose no information. -/
theorem windowCell_injective {carryDepth digitDepth : Nat} :
    Function.Injective (@windowCell carryDepth digitDepth) := by
  intro a b h
  rcases a with ⟨aC, ad⟩
  rcases b with ⟨bC, bd⟩
  apply Prod.ext
  · apply Fin.ext
    exact congrArg Prod.fst h
  · apply Fin.ext
    exact congrArg Prod.snd h

/-- Zero-extend a finite world into the limitless finitely-supported cosmos. -/
noncomputable def includeWindow {carryDepth digitDepth : Nat}
    (g : WorldCoef carryDepth digitDepth) : CosmicCoef :=
  ∑ c : WorldCell carryDepth digitDepth,
    Finsupp.single (windowCell c) (g c)

/-- Observe a limitless compact field through a finite rectangular window. -/
def restrictWindow {carryDepth digitDepth : Nat}
    (f : CosmicCoef) : WorldCoef carryDepth digitDepth :=
  fun c => f (windowCell c)

/-- A cosmic field is supported inside an `A × B` observation window. -/
def SupportedInWindow (carryDepth digitDepth : Nat) (f : CosmicCoef) : Prop :=
  ∀ p, f p ≠ 0 → p.1 < carryDepth ∧ p.2 < digitDepth

/-- Exact evaluation of zero-extension at a cell that lies inside the window. -/
theorem includeWindow_apply_inside {carryDepth digitDepth : Nat}
    (g : WorldCoef carryDepth digitDepth)
    (C d : Nat) (hC : C < carryDepth) (hd : d < digitDepth) :
    includeWindow g (C, d) = g (⟨C, hC⟩, ⟨d, hd⟩) := by
  classical
  let target : WorldCell carryDepth digitDepth := (⟨C, hC⟩, ⟨d, hd⟩)
  rw [includeWindow]
  simp only [Finset.sum_apply, Finsupp.single_apply]
  rw [Finset.sum_eq_single target]
  · simp [target, windowCell]
  · intro c _ hc
    have hneq : windowCell c ≠ (C, d) := by
      intro h
      apply hc
      apply windowCell_injective
      simpa [target, windowCell] using h
    simp [hneq]
  · simp

/-- Exact evaluation of zero-extension outside the observation window. -/
theorem includeWindow_apply_outside {carryDepth digitDepth : Nat}
    (g : WorldCoef carryDepth digitDepth) (p : CosmicCell)
    (h : carryDepth ≤ p.1 ∨ digitDepth ≤ p.2) :
    includeWindow g p = 0 := by
  classical
  rw [includeWindow]
  simp only [Finset.sum_apply, Finsupp.single_apply]
  apply Finset.sum_eq_zero
  intro c _
  have hneq : windowCell c ≠ p := by
    intro heq
    rcases h with hC | hd
    · have hv := congrArg Prod.fst heq
      dsimp [windowCell] at hv
      omega
    · have hv := congrArg Prod.snd heq
      dsimp [windowCell] at hv
      omega
  simp [hneq]

/-- Restricting an included finite world returns exactly the original world. -/
theorem restrictWindow_includeWindow {carryDepth digitDepth : Nat}
    (g : WorldCoef carryDepth digitDepth) :
    restrictWindow (includeWindow g) = g := by
  funext c
  exact includeWindow_apply_inside g c.1.1 c.2.1 c.1.2 c.2.2

/-- Zero-extension is supported in exactly the finite observation rectangle. -/
theorem includeWindow_supported {carryDepth digitDepth : Nat}
    (g : WorldCoef carryDepth digitDepth) :
    SupportedInWindow carryDepth digitDepth (includeWindow g) := by
  intro p hp
  constructor
  · by_contra hC
    have hz := includeWindow_apply_outside g p (Or.inl (Nat.le_of_not_gt hC))
    exact hp hz
  · by_contra hd
    have hz := includeWindow_apply_outside g p (Or.inr (Nat.le_of_not_gt hd))
    exact hp hz

/-- If a compact cosmic field really lives inside a window, observing it and
zero-extending that observation reconstructs the cosmic field exactly. -/
theorem includeWindow_restrictWindow_of_supported
    {carryDepth digitDepth : Nat} (f : CosmicCoef)
    (hf : SupportedInWindow carryDepth digitDepth f) :
    includeWindow (restrictWindow f : WorldCoef carryDepth digitDepth) = f := by
  ext p
  by_cases hC : p.1 < carryDepth
  · by_cases hd : p.2 < digitDepth
    · simpa [restrictWindow, windowCell] using
        (includeWindow_apply_inside
          (restrictWindow f : WorldCoef carryDepth digitDepth)
          p.1 p.2 hC hd)
    · have hz : f p = 0 := by
        by_contra hp
        exact hd (hf p hp).2
      rw [includeWindow_apply_outside
        (restrictWindow f : WorldCoef carryDepth digitDepth) p
        (Or.inr (Nat.le_of_not_gt hd))]
      exact hz.symm
  · have hz : f p = 0 := by
      by_contra hp
      exact hC (hf p hp).1
    rw [includeWindow_apply_outside
      (restrictWindow f : WorldCoef carryDepth digitDepth) p
      (Or.inl (Nat.le_of_not_gt hC))]
    exact hz.symm

/-- Restrict a larger finite window to a smaller one. -/
def restrictFiniteWindow
    {smallCarry smallDigit bigCarry bigDigit : Nat}
    (hCarry : smallCarry ≤ bigCarry) (hDigit : smallDigit ≤ bigDigit)
    (g : WorldCoef bigCarry bigDigit) : WorldCoef smallCarry smallDigit :=
  fun c =>
    g (⟨c.1.1, lt_of_lt_of_le c.1.2 hCarry⟩,
      ⟨c.2.1, lt_of_lt_of_le c.2.2 hDigit⟩)

/-- Cosmic observation is coherent under shrinking a finite window. -/
theorem restrictWindow_shrink
    {smallCarry smallDigit bigCarry bigDigit : Nat}
    (hCarry : smallCarry ≤ bigCarry) (hDigit : smallDigit ≤ bigDigit)
    (f : CosmicCoef) :
    restrictFiniteWindow hCarry hDigit
      (restrictWindow f : WorldCoef bigCarry bigDigit) =
      (restrictWindow f : WorldCoef smallCarry smallDigit) := by
  rfl

/-- The historical twelve-cell coefficient chart is recovered exactly from
its limitless zero-extension. -/
theorem twelve_cell_window_recovery (f : GSTWaveCohomology.WaveCoef) :
    restrictWindow (includeWindow (liftWave f)) = liftWave f := by
  exact restrictWindow_includeWindow (liftWave f)

/-- Reading the recovered `4 × 3` observation back through the historical
wave chart loses no information. -/
theorem twelve_cell_wave_recovery (f : GSTWaveCohomology.WaveCoef) :
    lowerWave (restrictWindow (includeWindow (liftWave f))) = f := by
  rw [restrictWindow_includeWindow]
  exact lowerWave_liftWave f

#check CosmicCell
#check CosmicCoef
#check windowCell_injective
#check includeWindow
#check restrictWindow
#check SupportedInWindow
#check includeWindow_apply_inside
#check includeWindow_apply_outside
#check restrictWindow_includeWindow
#check includeWindow_restrictWindow_of_supported
#check restrictFiniteWindow
#check restrictWindow_shrink
#check twelve_cell_window_recovery
#check twelve_cell_wave_recovery

#print axioms windowCell_injective
#print axioms includeWindow_apply_inside
#print axioms includeWindow_apply_outside
#print axioms restrictWindow_includeWindow
#print axioms includeWindow_restrictWindow_of_supported
#print axioms restrictWindow_shrink
#print axioms twelve_cell_wave_recovery

end GSTLimitlessWorld
