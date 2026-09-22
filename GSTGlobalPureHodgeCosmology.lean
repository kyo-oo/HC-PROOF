import Mathlib
import GSTDimensionFreeHodgeDiagonal

/-!
# GST GLOBAL PURE HODGE COSMOLOGY

The dimension-free Hodge diagonal file classifies one live weight at a time.
This file promotes the entire diagonal to one canonical object.

For an A x B rectangular world, the pure diagonal sector is exactly a free
integer module of rank min A B.  Its canonical coordinates are the values at

    (0,0), (1,1), ..., (min(A,B)-1,min(A,B)-1).

This gives a dimension-free parent theorem for the historical three-generator
pure sector of the 4 x 3 HC world.

No fixed Fin 12 address and no p < 3 case split appears.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

namespace GSTGlobalPureHodgeCosmology

open GSTWorldRecoordinationGroupoid
open GSTUniversalAddressBridge
open GSTDimensionFreeHodgeDiagonal

/-- Pure Hodge support means support is contained in the complete diagonal. -/
def isWorldPureHodge
    {A B : Nat}
    (f : ShapeCoef (outputShape A B)) : Prop :=
  ∀ x : ShapeState (outputShape A B),
    x.1.1 ≠ x.2.1 -> f x = 0

/-- The canonical coordinate module of the full diagonal. -/
abbrev PureHodgeCoordinates (A B : Nat) : Type :=
  Fin (min A B) -> ℤ

/-- The p-th diagonal state, now indexed canonically by Fin(min A B). -/
def pureDiagonalState
    {A B : Nat} (p : Fin (min A B)) :
    ShapeState (outputShape A B) :=
  diagonalState
    (p:=p.1)
    (by
      have hp := p.2
      omega)
    (by
      have hp := p.2
      omega)

/-- Read all pure-Hodge coordinates at once. -/
def pureCoordinates
    {A B : Nat}
    (f : ShapeCoef (outputShape A B)) :
    PureHodgeCoordinates A B :=
  fun p => f (pureDiagonalState p)

/-- Reassemble a diagonal cochain from arbitrary diagonal coordinates. -/
def pureReassemble
    {A B : Nat}
    (a : PureHodgeCoordinates A B) :
    ShapeCoef (outputShape A B) :=
  fun x =>
    if h : x.1.1 = x.2.1 then
      a ⟨x.1.1, by
        have hA : x.1.1 < A := by
          simpa [outputShape] using x.1.2
        have hB : x.2.1 < B := by
          simpa [outputShape] using x.2.2
        omega⟩
    else 0

/-- Every reassembled diagonal coordinate family is pure. -/
theorem pureReassemble_isPure
    {A B : Nat}
    (a : PureHodgeCoordinates A B) :
    isWorldPureHodge (pureReassemble a) := by
  intro x hx
  simp [pureReassemble, hx]

/-- Reading after reassembly is exactly identity on all diagonal coordinates. -/
theorem pureCoordinates_pureReassemble
    {A B : Nat}
    (a : PureHodgeCoordinates A B) :
    pureCoordinates (pureReassemble a) = a := by
  funext p
  unfold pureCoordinates pureReassemble pureDiagonalState
  simp [diagonalState]

/-- Every pure class is reconstructed exactly from all of its diagonal
coordinates. -/
theorem pureReassemble_pureCoordinates
    {A B : Nat}
    (f : ShapeCoef (outputShape A B))
    (hf : isWorldPureHodge f) :
    pureReassemble (pureCoordinates f) = f := by
  funext x
  by_cases hdiag : x.1.1 = x.2.1
  · simp only [pureReassemble, dif_pos hdiag, pureCoordinates,
      pureDiagonalState]
    have hx :
        diagonalState
          (p:=x.1.1)
          (by exact x.1.2)
          (by
            rw [hdiag]
            exact x.2.2) = x := by
      apply Prod.ext
      · apply Fin.ext
        rfl
      · apply Fin.ext
        exact hdiag
    rw [hx]
  · simp [pureReassemble, hdiag, hf x hdiag]

/-- The pure diagonal sector as a genuine Z-submodule of the full world. -/
def PureWorldHodge (A B : Nat) :
    Submodule ℤ (ShapeCoef (outputShape A B)) where
  carrier := {f | isWorldPureHodge f}
  zero_mem' := by
    intro x hx
    rfl
  add_mem' := by
    intro f g hf hg x hx
    simp [hf x hx, hg x hx]
  smul_mem' := by
    intro z f hf x hx
    simp [hf x hx]

/-- **GLOBAL PURE-HODGE COORDINATE EQUIVALENCE.**
The complete pure sector of every A x B world is canonically the free
integer module Z^(min A B). -/
def pureHodgeLinearEquiv
    (A B : Nat) :
    PureWorldHodge A B ≃ₗ[ℤ] PureHodgeCoordinates A B where
  toFun := fun f => pureCoordinates f.1
  invFun := fun a =>
    ⟨pureReassemble a, pureReassemble_isPure a⟩
  left_inv := by
    intro f
    apply Subtype.ext
    exact pureReassemble_pureCoordinates f.1 f.2
  right_inv := pureCoordinates_pureReassemble
  map_add' := by
    intro f g
    funext p
    rfl
  map_smul' := by
    intro z f
    funext p
    rfl

/-- Pure Hodge classes are uniquely determined by their complete diagonal
coordinate vector. -/
theorem pure_hodge_ext
    {A B : Nat}
    {f g : ShapeCoef (outputShape A B)}
    (hf : isWorldPureHodge f)
    (hg : isWorldPureHodge g)
    (hcoord : pureCoordinates f = pureCoordinates g) :
    f = g := by
  rw [← pureReassemble_pureCoordinates f hf,
      ← pureReassemble_pureCoordinates g hg,
      hcoord]

/-- Every pure class is exactly the reassembly of a unique coordinate family. -/
theorem pure_hodge_classification
    {A B : Nat}
    (f : ShapeCoef (outputShape A B)) :
    isWorldPureHodge f ↔
      ∃! a : PureHodgeCoordinates A B,
        f = pureReassemble a := by
  constructor
  · intro hf
    refine ⟨pureCoordinates f, ?_, ?_⟩
    · exact (pureReassemble_pureCoordinates f hf).symm
    · intro a ha
      have h := congrArg pureCoordinates ha
      rw [pureCoordinates_pureReassemble] at h
      exact h.symm
  · rintro ⟨a, rfl, huniq⟩
    exact pureReassemble_isPure a

/-- The historical HC pure sector has exactly three canonical coordinates. -/
theorem hc_pure_coordinate_depth :
    min 4 3 = 3 := by decide

/-- The historical three-generator theorem is therefore the 4 x 3 shadow of
the universal min(A,B)-coordinate classification. -/
noncomputable def hc_pure_hodge_equiv :
    PureWorldHodge 4 3 ≃ₗ[ℤ] (Fin 3 -> ℤ) :=
  (pureHodgeLinearEquiv 4 3).trans
    (LinearEquiv.piCongrLeft ℤ (fun _ : Fin 3 => ℤ)
      (finCongr hc_pure_coordinate_depth))

/-- Canonical pure basis vector at one diagonal weight. -/
def pureBasis
    {A B : Nat} (p : Fin (min A B)) :
    PureWorldHodge A B :=
  (pureHodgeLinearEquiv A B).symm
    (fun q => if q = p then 1 else 0)

/-- The p-th pure basis vector reads as Kronecker delta in pure coordinates. -/
theorem pureCoordinates_pureBasis
    {A B : Nat} (p : Fin (min A B)) :
    pureCoordinates (pureBasis p).1 =
      fun q => if q = p then 1 else 0 := by
  change pureHodgeLinearEquiv A B (pureBasis p) =
    fun q => if q = p then 1 else 0
  simp [pureBasis]

/-- Universal-address image of a pure class is supported exactly on the
finite set of diagonal codes (B+1)p. -/
theorem worldAddress_pure_support
    {A B : Nat}
    (f : ShapeCoef (outputShape A B))
    (hf : isWorldPureHodge f)
    (i : Fin (A*B))
    (hi :
      ∀ p : Fin (min A B),
        i ≠ shapeCodeEquiv (outputShape A B) (pureDiagonalState p)) :
    worldAddress (outputShape A B) f i = 0 := by
  unfold worldAddress
  let x := (shapeCodeEquiv (outputShape A B)).symm i
  apply hf x
  intro hdiag
  have hxA : x.1.1 < A := x.1.2
  have hxB : x.2.1 < B := x.2.2
  let p : Fin (min A B) :=
    ⟨x.1.1, by omega⟩
  apply hi p
  calc
    i = shapeCodeEquiv (outputShape A B) x := by
      simp [x]
    _ = shapeCodeEquiv (outputShape A B) (pureDiagonalState p) := by
      congr 1
      unfold pureDiagonalState diagonalState
      apply Prod.ext
      · apply Fin.ext
        rfl
      · apply Fin.ext
        exact hdiag.symm

/-- One capstone collecting the global pure-Hodge upgrade. -/
theorem global_pure_hodge_crown :
    (∀ A B : Nat,
      Function.Bijective (pureHodgeLinearEquiv A B))
    ∧ (∀ A B (f : ShapeCoef (outputShape A B)),
      isWorldPureHodge f ↔
        ∃! a : PureHodgeCoordinates A B,
          f = pureReassemble a)
    ∧ min 4 3 = 3 := by
  exact ⟨
    fun A B => (pureHodgeLinearEquiv A B).bijective,
    fun A B f => pure_hodge_classification f,
    hc_pure_coordinate_depth⟩

#check isWorldPureHodge
#check PureHodgeCoordinates
#check pureCoordinates
#check pureReassemble
#check PureWorldHodge
#check pureHodgeLinearEquiv
#check pure_hodge_ext
#check pure_hodge_classification
#check hc_pure_hodge_equiv
#check pureBasis
#check worldAddress_pure_support
#check global_pure_hodge_crown

#print axioms pureHodgeLinearEquiv
#print axioms pure_hodge_classification
#print axioms hc_pure_hodge_equiv
#print axioms worldAddress_pure_support
#print axioms global_pure_hodge_crown

end GSTGlobalPureHodgeCosmology
