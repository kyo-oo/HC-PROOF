import Mathlib
import GSTWorldCosmology

/-!
# GST LIMITLESS COSMOLOGY — unbounded algebraic and observational carriers

This file is the first unbounded layer above the finite rectangular world
family. Finite `A × B` worlds remain exact observations, but the global
carrier itself has no terminal row, column, degree, or address.

Two infinite faces are kept deliberately distinct:

* `CosmicCoef` is the finite-support algebraic cosmos;
* `GlobalCoef` is the unrestricted observational field.

No equivalence between them is asserted. `compactToGlobal` is the canonical
embedding of the algebraic sector into the observational one.
-/

set_option maxHeartbeats 20000000
set_option maxRecDepth 1000000

namespace GSTLimitlessCosmology

noncomputable section

open GSTWorldCosmology
open scoped BigOperators

/-- A cell in the limitless GST universe. Neither axis has a terminal wall. -/
abbrev CosmicCell : Type := Nat × Nat

/-- The algebraic limitless cosmos: integer amplitudes with finite support. -/
abbrev CosmicCoef : Type := CosmicCell →₀ ℤ

/-- The completed observational carrier: an unrestricted integer field. -/
abbrev GlobalCoef : Type := CosmicCell → ℤ

/-- The canonical embedding of a finite world cell into the limitless grid. -/
def worldCellEmbedding (A B : Nat) : WorldCell A B ↪ CosmicCell where
  toFun c := (c.1.1, c.2.1)
  inj' := by
    intro x y h
    apply Prod.ext
    · apply Fin.ext
      exact congrArg Prod.fst h
    · apply Fin.ext
      exact congrArg Prod.snd h

/-- The injective limitless digit translation by `n` layers. -/
def digitEmbedding (n : Nat) : CosmicCell ↪ CosmicCell where
  toFun c := (c.1, c.2 + n)
  inj' := by
    intro x y h
    injection h with hfst hsnd
    exact Prod.ext hfst (Nat.add_right_cancel hsnd)

/-- The injective limitless carry translation by `n` layers. -/
def carryEmbedding (n : Nat) : CosmicCell ↪ CosmicCell where
  toFun c := (c.1 + n, c.2)
  inj' := by
    intro x y h
    injection h with hfst hsnd
    exact Prod.ext (Nat.add_right_cancel hfst) hsnd

/-- Forget finite support and observe a compact algebraic field globally. -/
def compactToGlobal (f : CosmicCoef) : GlobalCoef :=
  fun c => f c

/-- Unrestricted digit-axis transport. Unlike a finite window shift, this
operator never dies merely because the transport depth is large. -/
def digitShift (n : Nat) (f : CosmicCoef) : CosmicCoef :=
  Finsupp.embDomain (digitEmbedding n) f

/-- Unrestricted carry-axis transport. -/
def carryShift (n : Nat) (f : CosmicCoef) : CosmicCoef :=
  Finsupp.embDomain (carryEmbedding n) f

/-- The limitless Lefschetz evolution: one digit step plus one carry step. -/
def lefschetz (f : CosmicCoef) : CosmicCoef :=
  digitShift 1 f + carryShift 1 f

/-- Observe a compact cosmic field through one finite rectangular window. -/
def windowRestrict (A B : Nat) (f : CosmicCoef) : WorldCoef A B :=
  fun c => f (worldCellEmbedding A B c)

/-- Extend a finite rectangular world into the limitless algebraic cosmos.
The finite function is first viewed as a finitely supported function on its
finite domain, then transported along the injective chart embedding. -/
def windowExtend (A B : Nat) (g : WorldCoef A B) : CosmicCoef :=
  Finsupp.embDomain (worldCellEmbedding A B)
    (Finsupp.equivFunOnFinite.symm g)

/-- Compact algebraic data embeds faithfully in the unrestricted observational
cosmos. Completion adds observations; it does not identify compact states. -/
theorem compactToGlobal_injective : Function.Injective compactToGlobal := by
  intro f g h
  ext c
  exact congrFun h c

/-- A basis state translated along the digit axis remains a basis state at
arbitrary depth. There is no global digit wall. -/
@[simp] theorem digitShift_single (n : Nat) (c : CosmicCell) (z : ℤ) :
    digitShift n (Finsupp.single c z) =
      Finsupp.single (c.1, c.2 + n) z := by
  rw [digitShift, Finsupp.embDomain_single]
  rfl

/-- A basis state translated along the carry axis remains a basis state at
arbitrary depth. There is no global carry wall. -/
@[simp] theorem carryShift_single (n : Nat) (c : CosmicCell) (z : ℤ) :
    carryShift n (Finsupp.single c z) =
      Finsupp.single (c.1 + n, c.2) z := by
  rw [carryShift, Finsupp.embDomain_single]
  rfl

/-- Extending a finite world into the limitless cosmos and observing the same
window recovers the finite world exactly. This holds uniformly, including
empty rectangular worlds. -/
theorem windowRestrict_windowExtend (A B : Nat) (g : WorldCoef A B) :
    windowRestrict A B (windowExtend A B g) = g := by
  funext c
  simp only [windowRestrict, windowExtend, Finsupp.embDomain_apply_self]
  exact congrFun (Finsupp.equivFunOnFinite.apply_symm_apply g) c

/-- Finite digit transport is exactly limitless digit transport observed back
through the same finite window. Finite extinction is therefore observational
truncation, not death of the global operator. -/
theorem windowRestrict_digitShift_windowExtend
    (A B n : Nat) (g : WorldCoef A B) :
    windowRestrict A B (digitShift n (windowExtend A B g)) =
      digitShiftN n g := by
  funext c
  change
    (digitShift n (windowExtend A B g)) (worldCellEmbedding A B c) =
      digitShiftN n g c
  unfold GSTWorldCosmology.digitShiftN
  by_cases h : n ≤ c.2.1
  · rw [dif_pos h]
    let p : WorldCell A B :=
      (c.1, ⟨c.2.1 - n, by omega⟩)
    have hcoord :
        worldCellEmbedding A B c =
          digitEmbedding n (worldCellEmbedding A B p) := by
      apply Prod.ext
      · rfl
      · dsimp [worldCellEmbedding, digitEmbedding, p]
        omega
    change
      (Finsupp.embDomain (digitEmbedding n) (windowExtend A B g))
          (worldCellEmbedding A B c) = g p
    rw [hcoord, Finsupp.embDomain_apply_self]
    simpa [windowRestrict] using
      congrFun (windowRestrict_windowExtend A B g) p
  · rw [dif_neg h]
    change
      (Finsupp.embDomain (digitEmbedding n) (windowExtend A B g))
          (worldCellEmbedding A B c) = 0
    apply Finsupp.embDomain_of_notMem_range
    intro hrange
    rcases hrange with ⟨x, hx⟩
    have hsnd := congrArg Prod.snd hx
    dsimp [digitEmbedding, worldCellEmbedding] at hsnd
    omega

/-- Finite carry transport is exactly limitless carry transport observed back
through the same finite window. The finite carry boundary is likewise an
observer boundary rather than a global wall. -/
theorem windowRestrict_carryShift_windowExtend
    (A B n : Nat) (g : WorldCoef A B) :
    windowRestrict A B (carryShift n (windowExtend A B g)) =
      carryShiftN n g := by
  funext c
  change
    (carryShift n (windowExtend A B g)) (worldCellEmbedding A B c) =
      carryShiftN n g c
  unfold GSTWorldCosmology.carryShiftN
  by_cases h : n ≤ c.1.1
  · rw [dif_pos h]
    let p : WorldCell A B :=
      (⟨c.1.1 - n, by omega⟩, c.2)
    have hcoord :
        worldCellEmbedding A B c =
          carryEmbedding n (worldCellEmbedding A B p) := by
      apply Prod.ext
      · dsimp [worldCellEmbedding, carryEmbedding, p]
        omega
      · rfl
    change
      (Finsupp.embDomain (carryEmbedding n) (windowExtend A B g))
          (worldCellEmbedding A B c) = g p
    rw [hcoord, Finsupp.embDomain_apply_self]
    simpa [windowRestrict] using
      congrFun (windowRestrict_windowExtend A B g) p
  · rw [dif_neg h]
    change
      (Finsupp.embDomain (carryEmbedding n) (windowExtend A B g))
          (worldCellEmbedding A B c) = 0
    apply Finsupp.embDomain_of_notMem_range
    intro hrange
    rcases hrange with ⟨x, hx⟩
    have hfst := congrArg Prod.fst hx
    dsimp [carryEmbedding, worldCellEmbedding] at hfst
    omega

#check CosmicCell
#check CosmicCoef
#check GlobalCoef
#check digitEmbedding
#check carryEmbedding
#check digitShift
#check carryShift
#check lefschetz
#check windowRestrict
#check windowExtend
#check compactToGlobal
#check compactToGlobal_injective
#check digitShift_single
#check carryShift_single
#check windowRestrict_windowExtend
#check windowRestrict_digitShift_windowExtend
#check windowRestrict_carryShift_windowExtend

end

end GSTLimitlessCosmology
