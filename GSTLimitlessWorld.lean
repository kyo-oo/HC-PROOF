import Mathlib

/-!
# GST LIMITLESS WORLD — unbounded algebraic cosmos

The finite rectangular GST worlds remain exact observation windows, but they
are no longer the ambient universe. The algebraic limitless cosmos is an
integer monoid algebra on the multiplicative image of `Nat × Nat`: an integer
field with finite support and no terminal carry row or digit column.

The `Multiplicative` wrapper makes monomial multiplication perform addition of
ordinary cosmic coordinates. The two global axes therefore act by genuine
unbounded translation, while finite extinction remains a property of finite
observation windows rather than of the cosmos itself.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

namespace GSTWorldCosmology

/-- A finite GST observation window with carry-depth and digit-depth. -/
abbrev WorldCell (carryDepth digitDepth : Nat) : Type :=
  Fin carryDepth × Fin digitDepth

/-- Integer amplitudes visible in one finite GST observation window. -/
def WorldCoef (carryDepth digitDepth : Nat) : Type :=
  WorldCell carryDepth digitDepth → ℤ

instance worldCoefAddCommGroup (carryDepth digitDepth : Nat) :
    AddCommGroup (WorldCoef carryDepth digitDepth) :=
  inferInstanceAs (AddCommGroup (WorldCell carryDepth digitDepth → ℤ))

instance worldCoefIntModule (carryDepth digitDepth : Nat) :
    Module ℤ (WorldCoef carryDepth digitDepth) :=
  inferInstanceAs (Module ℤ (WorldCell carryDepth digitDepth → ℤ))

end GSTWorldCosmology

namespace GSTLimitlessWorld

open GSTWorldCosmology

noncomputable section

/-- A coordinate in the limitless GST algebraic cosmos. -/
abbrev CosmicCell : Type := Nat × Nat

/-- Finite-support integer amplitudes on the limitless GST cosmos.

Mathlib's `MonoidAlgebra` stores coefficients as a finitely-supported function.
The multiplicative wrapper converts addition of ordinary cosmic coordinates
into monomial multiplication. -/
abbrev CosmicCoef : Type := MonoidAlgebra ℤ (Multiplicative CosmicCell)

/-- Basis state concentrated at one ordinary cosmic coordinate. -/
def cosmicBasis (c : CosmicCell) (z : ℤ := 1) : CosmicCoef :=
  MonoidAlgebra.single (Multiplicative.ofAdd c) z

/-- Read a compact cosmic field at an ordinary additive coordinate. -/
def cosmicEval (f : CosmicCoef) (c : CosmicCell) : ℤ :=
  f.coeff (Multiplicative.ofAdd c)

/-- The cosmic origin basis state is exactly the multiplicative unit. -/
@[simp]
theorem cosmicBasis_zero : cosmicBasis (0, 0) = (1 : CosmicCoef) := by
  change MonoidAlgebra.single (1 : Multiplicative CosmicCell) 1 = (1 : CosmicCoef)
  exact MonoidAlgebra.one_def.symm

/-- Monomial multiplication is literal addition of cosmic coordinates. -/
@[simp]
theorem cosmicBasis_add (a b : CosmicCell) :
    cosmicBasis a * cosmicBasis b = cosmicBasis (a + b) := by
  rw [cosmicBasis, cosmicBasis, cosmicBasis, MonoidAlgebra.single_mul_single]
  congr

/-- Global digit-axis transport. There is no digit ceiling. -/
def cosmicDigitShiftN (n : Nat) (f : CosmicCoef) : CosmicCoef :=
  cosmicBasis (0, n) * f

/-- Global carry-axis transport. There is no carry ceiling. -/
def cosmicCarryShiftN (n : Nat) (f : CosmicCoef) : CosmicCoef :=
  cosmicBasis (n, 0) * f

@[simp]
theorem cosmic_digitShiftN_zero (f : CosmicCoef) :
    cosmicDigitShiftN 0 f = f := by
  simp [cosmicDigitShiftN]

@[simp]
theorem cosmic_carryShiftN_zero (f : CosmicCoef) :
    cosmicCarryShiftN 0 f = f := by
  simp [cosmicCarryShiftN]

/-- Digit transport composes at arbitrary depth with no terminal wall. -/
theorem cosmic_digitShiftN_add (m n : Nat) (f : CosmicCoef) :
    cosmicDigitShiftN m (cosmicDigitShiftN n f) =
      cosmicDigitShiftN (m + n) f := by
  rw [cosmicDigitShiftN, cosmicDigitShiftN, cosmicDigitShiftN, ← mul_assoc,
    cosmicBasis_add]
  rfl

/-- Carry transport composes at arbitrary depth with no terminal wall. -/
theorem cosmic_carryShiftN_add (m n : Nat) (f : CosmicCoef) :
    cosmicCarryShiftN m (cosmicCarryShiftN n f) =
      cosmicCarryShiftN (m + n) f := by
  rw [cosmicCarryShiftN, cosmicCarryShiftN, cosmicCarryShiftN, ← mul_assoc,
    cosmicBasis_add]
  rfl

/-- **LIMITLESS AXIS LAW.** The two cosmic axes commute at every pair of
natural depths. -/
theorem cosmic_axes_commute (m n : Nat) (f : CosmicCoef) :
    cosmicDigitShiftN n (cosmicCarryShiftN m f) =
      cosmicCarryShiftN m (cosmicDigitShiftN n f) := by
  simp [cosmicDigitShiftN, cosmicCarryShiftN, cosmicBasis,
    mul_assoc, mul_comm, mul_left_comm]

/-- Embed one finite observation window into the limitless algebraic cosmos.
Every visible cell is sent to the cell with the same natural coordinates. -/
def extendWorld {A B : Nat} (g : WorldCoef A B) : CosmicCoef :=
  ∑ c : WorldCell A B,
    cosmicBasis (c.1.1, c.2.1) (g c)

/-- Observe a limitless algebraic field through one finite rectangle. -/
def restrictWorld (A B : Nat) (f : CosmicCoef) : WorldCoef A B :=
  fun c => cosmicEval f (c.1.1, c.2.1)

private theorem finiteCell_nat_injective {A B : Nat}
    {c d : WorldCell A B}
    (h : (c.1.1, c.2.1) = (d.1.1, d.2.1)) : c = d := by
  apply Prod.ext
  · apply Fin.ext
    exact congrArg Prod.fst h
  · apply Fin.ext
    exact congrArg Prod.snd h

/-- Exact scalar evaluation of a finite-world extension. -/
theorem cosmicEval_extendWorld {A B : Nat} (g : WorldCoef A B) (c : CosmicCell) :
    cosmicEval (extendWorld g) c =
      ∑ d : WorldCell A B,
        if (d.1.1, d.2.1) = c then g d else 0 := by
  classical
  unfold cosmicEval extendWorld cosmicBasis
  rw [MonoidAlgebra.coeff_sum]
  change
    ((∑ d ∈ (Finset.univ : Finset (WorldCell A B)),
      Finsupp.single (Multiplicative.ofAdd (d.1.1, d.2.1)) (g d))
        (Multiplicative.ofAdd c)) =
      ∑ d ∈ (Finset.univ : Finset (WorldCell A B)),
        if (d.1.1, d.2.1) = c then g d else 0
  rw [Finsupp.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro d _
  by_cases h : (d.1.1, d.2.1) = c
  · subst c
    simp
  · simp [h]

/-- Finite observation after extension is exactly the original world. -/
@[simp]
theorem restrictWorld_extendWorld {A B : Nat} (g : WorldCoef A B) :
    restrictWorld A B (extendWorld g) = g := by
  classical
  funext c
  rw [restrictWorld, cosmicEval_extendWorld]
  rw [Finset.sum_eq_single c]
  · simp
  · intro d _ hdc
    have hne : (d.1.1, d.2.1) ≠ (c.1.1, c.2.1) := by
      intro h
      exact hdc (finiteCell_nat_injective h)
    simp [hne]
  · simp

/-- A compact cosmic field lies inside an `A × B` window when every nonzero
coordinate lies below both observation depths. -/
def SupportInside (A B : Nat) (f : CosmicCoef) : Prop :=
  ∀ c, cosmicEval f c ≠ 0 → c.1 < A ∧ c.2 < B

/-- Every finite-world extension is supported inside its source window. -/
theorem supportInside_extendWorld {A B : Nat} (g : WorldCoef A B) :
    SupportInside A B (extendWorld g) := by
  classical
  intro c hc
  by_contra hinside
  have hout : A ≤ c.1 ∨ B ≤ c.2 := by omega
  have hzero : cosmicEval (extendWorld g) c = 0 := by
    rw [cosmicEval_extendWorld]
    apply Finset.sum_eq_zero
    intro d _
    have hne : (d.1.1, d.2.1) ≠ c := by
      intro h
      have hA : c.1 < A := by
        rw [← congrArg Prod.fst h]
        exact d.1.2
      have hB : c.2 < B := by
        rw [← congrArg Prod.snd h]
        exact d.2.2
      omega
    simp [hne]
  exact hc hzero

#check CosmicCell
#check CosmicCoef
#check cosmicBasis
#check cosmicEval
#check cosmicBasis_zero
#check cosmicBasis_add
#check cosmicDigitShiftN
#check cosmicCarryShiftN
#check cosmic_digitShiftN_add
#check cosmic_carryShiftN_add
#check cosmic_axes_commute
#check extendWorld
#check restrictWorld
#check cosmicEval_extendWorld
#check restrictWorld_extendWorld
#check supportInside_extendWorld

#print axioms cosmicBasis_add
#print axioms cosmic_digitShiftN_add
#print axioms cosmic_carryShiftN_add
#print axioms cosmic_axes_commute
#print axioms cosmicEval_extendWorld
#print axioms restrictWorld_extendWorld
#print axioms supportInside_extendWorld

end

end GSTLimitlessWorld
