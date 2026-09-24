import GSTWorldCosmology

/-!
# GST LIMITLESS WORLD — compact algebraic cosmos and finite observations

The finite rectangle `WorldCell A B = Fin A × Fin B` remains an exact GST
observation, but it is no longer the largest carrier.  The unbounded algebraic
cosmos is indexed by `Nat × Nat`; amplitudes are finitely supported so every
individual algebraic state is finite while the ambient universe has no final
row or column.

This file deliberately separates two notions which were previously fused:

* a **cosmic state**, living on the unbounded grid;
* a **finite window**, obtained by observing a bounded rectangle.

Extension from a finite window is exact zero-extension.  Restriction followed
by extension reconstructs a cosmic state exactly when its support lies in the
chosen window.  Hence finite boundary extinction is a property of an
observation, not a terminal law of the unbounded carrier.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

namespace GSTLimitlessWorld

open GSTWorldCosmology

/-- A cell in the unbounded GST cosmos.  Neither axis has a terminal value. -/
abbrev CosmicCell : Type := Nat × Nat

/-- Finitely supported fields on the unbounded GST cosmos over an arbitrary
coefficient type with zero.  This is the compact algebraic face of the
limitless universe. -/
abbrev CosmicField (R : Type) [Zero R] : Type := CosmicCell →₀ R

/-- The integral cosmic coefficient field used by the existing GST world
algebra. -/
abbrev CosmicCoef : Type := CosmicField ℤ

/-- The canonical embedding of an `A × B` GST window into the unbounded grid. -/
def windowCellEmbedding (carryDepth digitDepth : Nat) :
    WorldCell carryDepth digitDepth ↪ CosmicCell where
  toFun c := (c.1.1, c.2.1)
  inj' := by
    intro x y h
    apply Prod.ext
    · apply Fin.ext
      exact congrArg Prod.fst h
    · apply Fin.ext
      exact congrArg Prod.snd h

@[simp]
theorem windowCellEmbedding_apply {carryDepth digitDepth : Nat}
    (c : WorldCell carryDepth digitDepth) :
    windowCellEmbedding carryDepth digitDepth c = (c.1.1, c.2.1) :=
  rfl

/-- Convert a finite-world coefficient function to its canonical finitely
supported representation.  Finiteness comes from the finite window itself. -/
noncomputable def windowFinsupp {carryDepth digitDepth : Nat}
    (f : WorldCoef carryDepth digitDepth) :
    WorldCell carryDepth digitDepth →₀ ℤ :=
  Finsupp.equivFunOnFinite.symm f

@[simp]
theorem windowFinsupp_apply {carryDepth digitDepth : Nat}
    (f : WorldCoef carryDepth digitDepth)
    (c : WorldCell carryDepth digitDepth) :
    windowFinsupp f c = f c :=
  rfl

/-- Exact zero-extension of a finite GST window into the unbounded cosmos. -/
noncomputable def windowExtend {carryDepth digitDepth : Nat}
    (f : WorldCoef carryDepth digitDepth) : CosmicCoef :=
  Finsupp.embDomain (windowCellEmbedding carryDepth digitDepth) (windowFinsupp f)

/-- Evaluation of zero-extension at an embedded finite cell.  This explicit
law prevents the concrete `(Nat × Nat)` coordinates of a cell from obscuring
the exact `Finsupp.embDomain` image used by later reconstruction proofs. -/
@[simp]
theorem windowExtend_apply {carryDepth digitDepth : Nat}
    (f : WorldCoef carryDepth digitDepth)
    (c : WorldCell carryDepth digitDepth) :
    windowExtend f (windowCellEmbedding carryDepth digitDepth c) = f c := by
  change
    (Finsupp.embDomain (windowCellEmbedding carryDepth digitDepth) (windowFinsupp f))
        (windowCellEmbedding carryDepth digitDepth c) = f c
  rw [Finsupp.embDomain_apply_self]
  exact windowFinsupp_apply f c

/-- Observe an unbounded compact cosmic state through the finite `A × B`
window.  No information outside the window is asserted to vanish globally. -/
def windowRestrict (carryDepth digitDepth : Nat) (g : CosmicCoef) :
    WorldCoef carryDepth digitDepth :=
  fun c => g (windowCellEmbedding carryDepth digitDepth c)

/-- A compact cosmic state is contained in a finite window exactly when every
nonzero cell lies in the image of that window. -/
def SupportInWindow (carryDepth digitDepth : Nat) (g : CosmicCoef) : Prop :=
  (↑g.support : Set CosmicCell) ⊆
    Set.range (windowCellEmbedding carryDepth digitDepth)

/-- Zero-extension never changes a coefficient already visible in its source
window. -/
@[simp]
theorem windowRestrict_windowExtend {carryDepth digitDepth : Nat}
    (f : WorldCoef carryDepth digitDepth) :
    windowRestrict carryDepth digitDepth (windowExtend f) = f := by
  funext c
  exact windowExtend_apply f c

/-- Every zero-extended finite state is genuinely supported inside the window
from which it came. -/
theorem windowExtend_support {carryDepth digitDepth : Nat}
    (f : WorldCoef carryDepth digitDepth) :
    SupportInWindow carryDepth digitDepth (windowExtend f) := by
  intro x hx
  classical
  by_contra hRange
  have hz : windowExtend f x = 0 :=
    Finsupp.embDomain_of_notMem_range
      (windowCellEmbedding carryDepth digitDepth) (windowFinsupp f) x hRange
  exact (Finsupp.mem_support_iff.mp hx) hz

/-- Restricting a compact state to a window and extending it back is exact
when that window contains the complete support. -/
theorem windowExtend_windowRestrict_of_support
    (carryDepth digitDepth : Nat) (g : CosmicCoef)
    (h : SupportInWindow carryDepth digitDepth g) :
    windowExtend (windowRestrict carryDepth digitDepth g) = g := by
  ext x
  classical
  by_cases hRange : x ∈ Set.range (windowCellEmbedding carryDepth digitDepth)
  · rcases hRange with ⟨c, rfl⟩
    exact windowExtend_apply (windowRestrict carryDepth digitDepth g) c
  · have hx : x ∉ g.support := by
      intro hx
      exact hRange (h hx)
    have hg0 : g x = 0 := Finsupp.notMem_support_iff.mp hx
    rw [windowExtend]
    rw [Finsupp.embDomain_of_notMem_range
      (windowCellEmbedding carryDepth digitDepth)
      (windowFinsupp (windowRestrict carryDepth digitDepth g)) x hRange]
    exact hg0.symm

/-- Inclusion of one finite observation window into a larger one. -/
def windowInclusion {carryDepth₁ digitDepth₁ carryDepth₂ digitDepth₂ : Nat}
    (hCarry : carryDepth₁ ≤ carryDepth₂)
    (hDigit : digitDepth₁ ≤ digitDepth₂) :
    WorldCell carryDepth₁ digitDepth₁ ↪ WorldCell carryDepth₂ digitDepth₂ where
  toFun c :=
    (⟨c.1.1, lt_of_lt_of_le c.1.2 hCarry⟩,
      ⟨c.2.1, lt_of_lt_of_le c.2.2 hDigit⟩)
  inj' := by
    intro x y h
    apply Prod.ext
    · apply Fin.ext
      exact congrArg (fun c => c.1.1) h
    · apply Fin.ext
      exact congrArg (fun c => c.2.1) h

/-- Restrict a larger finite observation to a smaller nested window. -/
def windowRestrictFromWindow
    {carryDepth₁ digitDepth₁ carryDepth₂ digitDepth₂ : Nat}
    (hCarry : carryDepth₁ ≤ carryDepth₂)
    (hDigit : digitDepth₁ ≤ digitDepth₂)
    (f : WorldCoef carryDepth₂ digitDepth₂) :
    WorldCoef carryDepth₁ digitDepth₁ :=
  fun c => f (windowInclusion hCarry hDigit c)

/-- Direct observation from the cosmos agrees exactly with observing a larger
window first and then restricting to a smaller nested window. -/
theorem windowRestrict_nested
    {carryDepth₁ digitDepth₁ carryDepth₂ digitDepth₂ : Nat}
    (hCarry : carryDepth₁ ≤ carryDepth₂)
    (hDigit : digitDepth₁ ≤ digitDepth₂)
    (g : CosmicCoef) :
    windowRestrict carryDepth₁ digitDepth₁ g =
      windowRestrictFromWindow hCarry hDigit
        (windowRestrict carryDepth₂ digitDepth₂ g) := by
  rfl

/-- A window with no carry rows observes the unique zero coefficient field. -/
theorem windowRestrict_zero_carry (digitDepth : Nat) (g : CosmicCoef) :
    windowRestrict 0 digitDepth g = 0 := by
  funext c
  exact Fin.elim0 c.1

/-- A window with no digit columns observes the unique zero coefficient field. -/
theorem windowRestrict_zero_digit (carryDepth : Nat) (g : CosmicCoef) :
    windowRestrict carryDepth 0 g = 0 := by
  funext c
  exact Fin.elim0 c.2

/-- The exact finite-window reconstruction law packaged as a two-way
certificate.  This is the first universal replacement for treating a finite
rectangle as the whole cosmos. -/
theorem finite_window_reconstruction_crown
    (carryDepth digitDepth : Nat) :
    (∀ f : WorldCoef carryDepth digitDepth,
      windowRestrict carryDepth digitDepth (windowExtend f) = f) ∧
    (∀ g : CosmicCoef,
      SupportInWindow carryDepth digitDepth g →
        windowExtend (windowRestrict carryDepth digitDepth g) = g) := by
  constructor
  · exact windowRestrict_windowExtend
  · intro g hg
    exact windowExtend_windowRestrict_of_support carryDepth digitDepth g hg

#print axioms finite_window_reconstruction_crown

end GSTLimitlessWorld
