import Mathlib
import GSTWorldCosmology

/-!
# GST LIMITLESS COSMOLOGY — unbounded algebraic and observational carriers

This file is the first unbounded layer above the finite rectangular world
family.  Finite `A × B` worlds remain exact observations, but the global
carrier itself has no terminal row, column, degree, or address.

Two infinite faces are kept deliberately distinct:

* `CosmicCoef` is the finite-support algebraic cosmos;
* `GlobalCoef` is the unrestricted observational field.

No equivalence between them is asserted.  `compactToGlobal` is the canonical
embedding of the algebraic sector into the observational one.
-/

set_option maxHeartbeats 20000000
set_option maxRecDepth 1000000

namespace GSTLimitlessCosmology

open GSTWorldCosmology
open scoped BigOperators

/-- A cell in the limitless GST universe.  Neither axis has a terminal wall. -/
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

/-- Forget finite support and observe a compact algebraic field globally. -/
def compactToGlobal (f : CosmicCoef) : GlobalCoef :=
  fun c => f c

/-- Unrestricted digit-axis transport.  Unlike a finite window shift, this
operator never dies merely because the transport depth is large. -/
def digitShift (n : Nat) (f : CosmicCoef) : CosmicCoef :=
  f.sum fun c z => Finsupp.single (c.1, c.2 + n) z

/-- Unrestricted carry-axis transport. -/
def carryShift (n : Nat) (f : CosmicCoef) : CosmicCoef :=
  f.sum fun c z => Finsupp.single (c.1 + n, c.2) z

/-- The limitless Lefschetz evolution: one digit step plus one carry step. -/
def lefschetz (f : CosmicCoef) : CosmicCoef :=
  digitShift 1 f + carryShift 1 f

/-- Observe a compact cosmic field through one finite rectangular window. -/
def windowRestrict (A B : Nat) (f : CosmicCoef) : WorldCoef A B :=
  fun c => f (worldCellEmbedding A B c)

/-- Extend a finite rectangular world into the limitless algebraic cosmos.
Outside the selected finite chart the extension is zero. -/
noncomputable def windowExtend (A B : Nat) (g : WorldCoef A B) : CosmicCoef :=
  ∑ c : WorldCell A B,
    Finsupp.single (worldCellEmbedding A B c) (g c)

#check CosmicCell
#check CosmicCoef
#check GlobalCoef
#check digitShift
#check carryShift
#check lefschetz
#check windowRestrict
#check windowExtend
#check compactToGlobal

end GSTLimitlessCosmology
