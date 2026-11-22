import Mathlib
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import GSTFiniteLineRing
import GSTProjectiveOverC
import GSTFiniteLineWorldCarrier

/-
Copyright (c) 2026. The HC-PROOF campaign. All rights reserved.

# THE HONEST PRIME LATTICE OF THE FINITE-LINE WORLD (wave 4-A)

The component algebra of `Proj (lineGrading M)` — the honest prime lattice
behind the canonical cycle-class maps of the unconditional round:

* the M generic points `lineGenericPoint M i` (the ideals of the variables
  outside block i) — coheight ZERO (the maximal points of the
  specialization order, the generic points of the M lines);
* the closed point `lineClosedPoint M` (the `X₁`-image together with all
  the outside-block-0 variables) — coheight ONE, strictly below the 0-th
  generic point;
* the component machinery: `lineIndexOfGeneric` (the coheight-zero points
  ARE the M generic points) and `lineComponentOf` (every coheight-one
  point lies below EXACTLY ONE generic point).

The engines, all unconditional:

1. THE BLOCK RETRACTIONS (§1): the two-variable dehomogenization
   `blockProjAt M i` (a ℂ-algebra map to ℂ[Y,Z] sending block i's pair to
   Y,Z and every other variable to 0) and its one-variable shadow
   `blockProjClosed` (X₀ ↦ X, else 0), with the KERNEL LAWS — the kernels
   are exactly the generic/closed ideals.  The kernel inclusion
   `aeval = 0 → crossIdeal ⊔ outside` rides the three-case
   `MvPolynomial.induction_on` (the outside-variable case lands in the
   outside span outright; the kept-variable case divides by the nonzero
   family value in the polynomial domain).
2. THE NO-INTERMEDIATE LAW (§4): no point's ideal lies strictly between
   the 0-th generic ideal and the closed ideal — the transported prime in
   ℂ[Y,Z] dies by KRULL'S PRINCIPAL IDEAL THEOREM (the green
   `Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors`: the height
   of `(Z)` is one, so the height-realizing prime above it squeezes the
   intermediate to height zero — the zero ideal of the domain).
3. THE ORDER BRIDGE (§3): the specialization order on the line world's
   points is reverse inclusion of homogeneous ideals (the corpus's green
   `prime_le_iff` pattern, restated at this carrier), which turns the
   prime-lattice computations into coheight receipts.

Honesty ledger: every statement is proved unconditionally.  No `sorry`,
no new axioms, no `native_decide`.  The GitHub CI lane
`gst-finite-line-point-algebra.yml` owns the kernel check.
-/

set_option maxHeartbeats 200000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry CategoryTheory
open GSTProjectiveOverC GSTFiniteLineRing GSTFiniteLineWorldCarrier
open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GSTFiniteLinePointAlgebra

/-! ## §0 The cross-product vanishing and the block arithmetic -/

/-- **THE CROSS-PRODUCT VANISHING** — different-block variables multiply
to zero in the cross-monomial quotient (the defining relation of the M
disjoint lines). -/
theorem crossMul_eq_zero (M : ℕ) {a b : Fin (2 * M)}
    (hab : a.val / 2 ≠ b.val / 2) :
    lineQuotientMap M (X a) * lineQuotientMap M (X b) = 0 := by
  rw [← map_mul, lineQuotientMap_eq_zero_iff]
  exact Ideal.subset_span ⟨a, b, hab, rfl⟩

block membership. -/
theorem mem_block_iff (M : ℕ) (i : Fin M) (a : Fin (2 * M)) :
    (a.val = 2 * i.val ∨ a.val = 2 * i.val + 1) ↔ a.val / 2 = i.val := by
  have ha : a.val < 2 * M := a.isLt
  have hM : 0 < M := Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hdm : a.val = 2 * (a.val / 2) + a.val % 2 := (Nat.div_add_mod a.val 2).symm
  have hmod : a.val % 2 < 2 := Nat.mod_lt _ (by omega)
  constructor
  · rintro (h | h) <;> omega
  · intro h
    omega

/-- The even variable index of block i. -/
def blockVarLeft (M : ℕ) (i : Fin M) : Fin (2 * M) :=
  ⟨2 * i.val, by have := i.isLt; omega⟩

/-- The odd variable index of block i. -/
def blockVarRight (M : ℕ) (i : Fin M) : Fin (2 * M) :=
  ⟨2 * i.val + 1, by have := i.isLt; omega⟩

theorem blockVarLeft_val (M : ℕ) (i : Fin M) :
    (blockVarLeft M i).val = 2 * i.val := rfl

theorem blockVarRight_val (M : ℕ) (i : Fin M) :
    (blockVarRight M i).val = 2 * i.val + 1 := rfl

theorem blockVarLeft_block (M : ℕ) (i : Fin M) :
    (blockVarLeft M i).val / 2 = i.val := by
  rw [blockVarLeft_val, Nat.mul_div_cancel_left _ two_ne_zero]

theorem blockVarRight_block (M : ℕ) (i : Fin M) :
    (blockVarRight M i).val / 2 = i.val := by
  rw [blockVarRight_val]
  omega

theorem not_mem_block_left (M : ℕ) (i : Fin M) {a : Fin (2 * M)}
    (ha : a.val / 2 ≠ i.val) : a.val ≠ 2 * i.val ∧ a.val ≠ 2 * i.val + 1 := by
  constructor <;> intro h <;> [rw [h, Nat.mul_div_cancel_left _ two_ne_zero] at ha;
      exact absurd rfl ha;
    apply ha; omega]

/-! ## §1 The block retractions and the kernel laws -/

/-- The block-i variable family: `X_{2i} ↦ Y`, `X_{2i+1} ↦ Z`, all other
variables to zero. -/
def blockVarFamily (M : ℕ) (i : Fin M) :
    Fin (2 * M) → MvPolynomial (Fin 2) ℂ :=
  fun a => if a.val = 2 * i.val then (X ⟨0, by omega⟩ : MvPolynomial (Fin 2) ℂ)
    else if a.val = 2 * i.val + 1 then
      (X ⟨1, by omega⟩ : MvPolynomial (Fin 2) ℂ) else 0

/-- **THE BLOCK PROJECTION** — the dehomogenization retraction at block i
(a ℂ-algebra map from the coordinate ring to ℂ[Y,Z]). -/
def blockProjAt (M : ℕ) (i : Fin M) :
    lineRing M →ₐ[ℂ] MvPolynomial (Fin 2) ℂ :=
  MvPolynomial.aeval (blockVarFamily M i)

/-- The block-i substitution family: `Y ↦ X_{2i}`, `Z ↦ X_{2i+1}`. -/
def blockInclFamily (M : ℕ) (i : Fin M) : Fin 2 → lineRing M :=
  fun a => (X ⟨2 * i.val + a.val, by have := i.isLt; omega⟩ : lineRing M)

/-- **THE BLOCK SUBSTITUTION** — the section of the block projection. -/
def blockInclAt (M : ℕ) (i : Fin M) :
    MvPolynomial (Fin 2) ℂ →ₐ[ℂ] lineRing M :=
  MvPolynomial.aeval (blockInclFamily M i)

theorem blockProjAt_X_left (M : ℕ) (i : Fin M) :
    blockProjAt M i (X (blockVarLeft M i)) = (X ⟨0, by omega⟩ : MvPolynomial (Fin 2) ℂ) := by
  rw [blockProjAt, aeval_X, blockVarFamily, if_pos blockVarLeft_val]

theorem blockProjAt_X_right (M : ℕ) (i : Fin M) :
    blockProjAt M i (X (blockVarRight M i)) = (X ⟨1, by omega⟩ : MvPolynomial (Fin 2) ℂ) := by
  rw [blockProjAt, aeval_X, blockVarFamily, if_neg (not_mem_block_left M i
    (blockVarRight_block M i)).1, if_pos blockVarRight_val]

theorem blockProjAt_X_outside (M : ℕ) (i : Fin M) {a : Fin (2 * M)}
    (ha : a.val / 2 ≠ i.val) :
    blockProjAt M i (X a) = 0 := by
  rw [blockProjAt, aeval_X, blockVarFamily,
    if_neg (not_mem_block_left M i ha).1, if_neg (not_mem_block_left M i ha).2]

theorem blockInclAt_X (M : ℕ) (i : Fin M) (a : Fin 2) :
    blockInclAt M i (X a) = blockInclFamily M a := by
  rw [blockInclAt, aeval_X]

theorem blockProjAt_comp_blockInclAt (M : ℕ) (i : Fin M) :
    (blockProjAt M i).comp (blockInclAt M i) = AlgHom.id ℂ (MvPolynomial (Fin 2) ℂ) := by
  refine MvPolynomial.algHom_ext fun a => ?_
  rw [AlgHom.coe_comp, DFunLike.coe_fn_eq, AlgHom.coe_id, id_eq,
    blockInclAt_X]
  cases a.val with
  | zero => rw [blockInclFamily, if_pos rfl]
    show blockProjAt M i (X (blockVarLeft M i)) = _
    rw [blockProjAt_X_left]
    rfl
  | succ av =>
    have hval : (⟨av + 1, by omega⟩ : Fin 2).val = 1 := by omega
    show blockProjAt M i (X ⟨2 * i.val + (av + 1), _⟩) = _
    rw [show (2 * i.val + (av + 1) : ℕ) = 2 * i.val + 1 from by omega]
    show blockProjAt M i (X (blockVarRight M i)) = _
    rw [blockProjAt_X_right]
    rfl

/-- **THE OUTSIDE-VARIABLE IDEAL** (ring level): the span of the
variables outside block i. -/
def outsideIdealRing (M : ℕ) (i : Fin M) : Ideal (lineRing M) :=
  Ideal.span (Set.range fun b : {b : Fin (2 * M) // b.val / 2 ≠ i.val} =>
    (X b.1 : lineRing M))

theorem mem_outsideIdealRing (M : ℕ) (i : Fin M) {a : Fin (2 * M)}
    (ha : a.val / 2 ≠ i.val) :
    (X a : lineRing M) ∈ outsideIdealRing M i :=
  Ideal.subset_span ⟨⟨a, ha⟩, rfl⟩

/-- **THE PROJECTOR IDEAL** — generated by the variable-projector
differences. -/
def projectorIdeal (M : ℕ) (i : Fin M) : Ideal (lineRing M) :=
  Ideal.span (Set.range fun a : Fin (2 * M) =>
    (X a : lineRing M) - blockInclAt M i (blockProjAt M i (X a)))

/-- Every polynomial is congruent to its projector modulo the projector
ideal (the two algebra maps — the quotient and the projector-then-quotient
— agree on the variable generators). -/
theorem sub_projector_mem (M : ℕ) (i : Fin M) (q : lineRing M) :
    q - blockInclAt M i (blockProjAt M i q) ∈ projectorIdeal M i := by
  have hagree : (Ideal.Quotient.mkₐ ℂ (projectorIdeal M i)).comp
      ((blockInclAt M i).comp (blockProjAt M i)) =
      (Ideal.Quotient.mkₐ ℂ (projectorIdeal M i)) := by
    refine MvPolynomial.algHom_ext' fun a => ?_
    have hgen : (X a : lineRing M) - blockInclAt M i (blockProjAt M i (X a)) ∈
        projectorIdeal M i := Ideal.subset_span ⟨a, rfl⟩
    have hq := (Ideal.Quotient.eq (I := projectorIdeal M i)).mpr hgen
    exact hq.symm
  have happ := DFunLike.congr_fun hagree q
  rw [AlgHom.coe_comp, DFunLike.coe_fn_eq] at happ
  have hz : (Ideal.Quotient.mkₐ ℂ (projectorIdeal M i)) (q -
      blockInclAt M i (blockProjAt M i q)) = 0 := by
    rw [map_sub, happ, sub_self]
    rfl
  exact Ideal.Quotient.eq_zero_iff_mem.mp hz

/-- The substitution-variables are the block variables. -/
theorem blockInclAt_X_zero (M : ℕ) (i : Fin M) :
    blockInclAt M i (X ⟨0, by omega⟩ : MvPolynomial (Fin 2) ℂ) =
      (X (blockVarLeft M i) : lineRing M) := by
  rw [blockInclAt_X]
  have hidx : (⟨2 * i.val + 0, by have := i.isLt; omega⟩ : Fin (2 * M)) =
      blockVarLeft M i := Fin.ext (by rw [blockVarLeft_val]; omega)
  show (X (⟨2 * i.val + 0, by have := i.isLt; omega⟩ : Fin (2 * M)) :
      lineRing M) = _
  rw [hidx]

theorem blockInclAt_X_one (M : ℕ) (i : Fin M) :
    blockInclAt M i (X ⟨1, by omega⟩ : MvPolynomial (Fin 2) ℂ) =
      (X (blockVarRight M i) : lineRing M) := by
  rw [blockInclAt_X]
  have hidx : (⟨2 * i.val + 1, by have := i.isLt; omega⟩ : Fin (2 * M)) =
      blockVarRight M i := Fin.ext (by rw [blockVarRight_val]; omega)
  show (X (⟨2 * i.val + 1, by have := i.isLt; omega⟩ : Fin (2 * M)) :
      lineRing M) = _
  rw [hidx]

/-- The projector fixes the kept variables. -/
theorem projector_roundtrip_left (M : ℕ) (i : Fin M) :
    blockInclAt M i (blockProjAt M i (X (blockVarLeft M i))) =
      (X (blockVarLeft M i) : lineRing M) := by
  rw [blockProjAt_X_left, blockInclAt_X_zero]

theorem projector_roundtrip_right (M : ℕ) (i : Fin M) :
    blockInclAt M i (blockProjAt M i (X (blockVarRight M i))) =
      (X (blockVarRight M i) : lineRing M) := by
  rw [blockProjAt_X_right, blockInclAt_X_one]

/-- The projector ideal lies in the outside-variable ideal (the
differences vanish on the kept block and equal the outside variables
elsewhere). -/
theorem projectorIdeal_le_outside (M : ℕ) (i : Fin M) :
    projectorIdeal M i ≤ outsideIdealRing M i := by
  rw [projectorIdeal, Ideal.span_le]
  rintro _ ⟨a, rfl⟩
  rcases eq_or_ne (a.val / 2) i.val with h | h
  · have hkept : a = blockVarLeft M i ∨ a = blockVarRight M i := by
      rcases (mem_block_iff M i a).mpr h with hval | hval
      · exact Or.inl (Fin.ext hval)
      · exact Or.inr (Fin.ext hval)
    have hround : blockInclAt M i (blockProjAt M i (X a)) = (X a : lineRing M) := by
      rcases hkept with rfl | rfl
      · exact projector_roundtrip_left M i
      · exact projector_roundtrip_right M i
    rw [hround, sub_self]
    exact Submodule.zero_mem _
  · rw [blockProjAt_X_outside M i h, map_zero, sub_zero]
    exact mem_outsideIdealRing M i h

/-- **THE KERNEL LAW** — the kernel of the block projection is exactly the
outside-variable ideal: the substitution route (every polynomial is
congruent to its projector modulo the projector ideal; the projector
collapses to zero on the kernel). -/
theorem ker_blockProjAt (M : ℕ) (i : Fin M) :
    RingHom.ker (blockProjAt M i).toRingHom = outsideIdealRing M i := by
  apply le_antisymm
  · -- a kernel element: the projector is zero on it, so it lies in the
    -- projector ideal, hence in the outside ideal
    intro t ht
    have hPzero : blockInclAt M i (blockProjAt M i t) = 0 := by
      rw [RingHom.mem_ker] at ht
      rw [ht, map_zero]
    have hmem : t - blockInclAt M i (blockProjAt M i t) ∈ projectorIdeal M i :=
      sub_projector_mem M i t
    rw [hPzero, sub_zero] at hmem
    exact projectorIdeal_le_outside M i hmem
  · rw [outsideIdealRing, Ideal.span_le]
    rintro _ ⟨b, hb, rfl⟩
    rw [RingHom.mem_ker, blockProjAt_X_outside M i hb.2]

/-! ### The generic ideal and the descended retraction -/

/-- **THE GENERIC IDEAL** — the span of the outside-block-i variable
images in the quotient: the prime of the i-th line's generic point. -/
def lineGenericIdeal (M : ℕ) (i : Fin M) : Ideal (lineQuotient M) :=
  Ideal.span (Set.range fun b : {b : Fin (2 * M) // b.val / 2 ≠ i.val} =>
    lineQuotientMap M (X b.1))

theorem mem_lineGenericIdeal (M : ℕ) (i : Fin M) {a : Fin (2 * M)}
    (ha : a.val / 2 ≠ i.val) :
    lineQuotientMap M (X a) ∈ lineGenericIdeal M i :=
  Ideal.subset_span ⟨⟨a, ha⟩, rfl⟩

/-- The block projection kills the cross ideal: different-block products
have a zero family factor. -/
theorem blockProjAt_crossIdeal_le_ker (M : ℕ) (i : Fin M) :
    crossIdeal M ≤ RingHom.ker (blockProjAt M i).toRingHom := by
  rw [crossIdeal, Ideal.span_le]
  rintro _ ⟨a, b, hab, rfl⟩
  rw [RingHom.mem_ker, map_mul, aeval_X, aeval_X]
  rcases eq_or_ne (a.val / 2) i.val with ha | ha
  · have hb : b.val / 2 ≠ i.val := fun h => hab (ha.trans h.symm)
    rw [blockProjAt_X_outside M i hb, mul_zero]
  · rw [blockProjAt_X_outside M i ha, zero_mul]

/-- **THE DESCENDED BLOCK PROJECTION** — the retraction on the quotient
ring. -/
noncomputable def blockProjQuotAt (M : ℕ) (i : Fin M) :
    lineQuotient M →ₐ[ℂ] MvPolynomial (Fin 2) ℂ :=
  Ideal.Quotient.liftₐ (crossIdeal M) (blockProjAt M i)
    (fun p hp => by
      have hk : p ∈ RingHom.ker (blockProjAt M i).toRingHom :=
        blockProjAt_crossIdeal_le_ker M i hp
      rwa [RingHom.mem_ker] at hk)

theorem blockProjQuotAt_mk (M : ℕ) (i : Fin M) (t : lineRing M) :
    blockProjQuotAt M i (lineQuotientMap M t) = blockProjAt M i t := rfl

theorem blockProjQuotAt_X_left (M : ℕ) (i : Fin M) :
    blockProjQuotAt M i (lineQuotientMap M (X (blockVarLeft M i))) =
      (X ⟨0, by omega⟩ : MvPolynomial (Fin 2) ℂ) := by
  rw [blockProjQuotAt_mk, blockProjAt_X_left]

theorem blockProjQuotAt_X_right (M : ℕ) (i : Fin M) :
    blockProjQuotAt M i (lineQuotientMap M (X (blockVarRight M i))) =
      (X ⟨1, by omega⟩ : MvPolynomial (Fin 2) ℂ) := by
  rw [blockProjQuotAt_mk, blockProjAt_X_right]

theorem blockProjQuotAt_X_outside (M : ℕ) (i : Fin M) {a : Fin (2 * M)}
    (ha : a.val / 2 ≠ i.val) :
    blockProjQuotAt M i (lineQuotientMap M (X a)) = 0 := by
  rw [blockProjQuotAt_mk, blockProjAt_X_outside M i ha]

/-- **THE KERNEL CHARACTERIZATION AT THE GENERIC IDEAL** — membership in
the i-th generic ideal IS vanishing under the block-i retraction (the
kernel law transported along the quotient). -/
theorem mem_lineGenericIdeal_iff (M : ℕ) (i : Fin M) (y : lineQuotient M) :
    y ∈ lineGenericIdeal M i ↔ blockProjQuotAt M i y = 0 := by
  obtain ⟨t, rfl⟩ := lineQuotientMap_surjective M y
  constructor
  · intro hy
    have hle : lineGenericIdeal M i ≤
        RingHom.ker (blockProjQuotAt M i).toRingHom := by
      rw [lineGenericIdeal, Ideal.span_le]
      rintro _ ⟨b, hb, rfl⟩
      rw [RingHom.mem_ker, blockProjQuotAt_X_outside M i b.2]
    have hk := hle hy
    rwa [RingHom.mem_ker] at hk
  · intro hy
    rw [blockProjQuotAt_mk] at hy
    have hker : t ∈ RingHom.ker (blockProjAt M i).toRingHom := by
      rw [RingHom.mem_ker]; exact hy
    have hout : t ∈ outsideIdealRing M i := by
      have hke := ker_blockProjAt M i
      rw [← hke] at hker
      exact hker
    have hmap : lineQuotientMap M t ∈
        Ideal.map (lineQuotientMap M).toRingHom (outsideIdealRing M i) :=
      Ideal.mem_map_of_mem _ hout
    rw [outsideIdealRing, Ideal.map_span] at hmap
    refine (Ideal.span_le).mpr ?_ hmap
    rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
    exact Ideal.subset_span ⟨b, rfl⟩

/-- **THE GENERIC IDEAL IS PRIME.** -/
theorem lineGenericIdeal_isPrime (M : ℕ) (i : Fin M) :
    (lineGenericIdeal M i).IsPrime := by
  refine ⟨?_, ?_⟩
  · intro htop
    have h1 : (1 : lineQuotient M) ∈ lineGenericIdeal M i := by
      rw [htop]; trivial
    have hz := (mem_lineGenericIdeal_iff M i 1).mp h1
    rw [map_one] at hz
    exact one_ne_zero hz
  · intro x y hxy
    have hx : blockProjQuotAt M i (x * y) = 0 :=
      (mem_lineGenericIdeal_iff M i _).mp hxy
    rw [map_mul, mul_eq_zero] at hx
    rcases hx with h | h
    · exact Or.inl ((mem_lineGenericIdeal_iff M i _).mpr h)
    · exact Or.inr ((mem_lineGenericIdeal_iff M i _).mpr h)

theorem lineQuotientMap_X_pair_not_mem (M : ℕ) (i : Fin M) :
    lineQuotientMap M (X (blockVarLeft M i)) ∉ lineGenericIdeal M i := by
  intro hmem
  have hz := (mem_lineGenericIdeal_iff M i _).mp hmem
  rw [blockProjQuotAt_X_left M i] at hz
  exact X_ne_zero ⟨0, by omega⟩ hz.symm

theorem lineQuotientMap_X_pair_not_mem' (M : ℕ) (i : Fin M) :
    lineQuotientMap M (X (blockVarRight M i)) ∉ lineGenericIdeal M i := by
  intro hmem
  have hz := (mem_lineGenericIdeal_iff M i _).mp hmem
  rw [blockProjQuotAt_X_right M i] at hz
  exact X_ne_zero ⟨1, by omega⟩ hz.symm

/-! ### The closed ideal and its retraction -/

/-- The closed-point variable family: `X₀ ↦ X`, all other variables to
zero. -/
def closedVarFamily (M : ℕ) : Fin (2 * M) → MvPolynomial (Fin 1) ℂ :=
  fun a => if a.val = 0 then (X ⟨0, by omega⟩ : MvPolynomial (Fin 1) ℂ) else 0

/-- **THE CLOSED PROJECTION** — the one-variable retraction. -/
def blockProjClosed (M : ℕ) :
    lineRing M →ₐ[ℂ] MvPolynomial (Fin 1) ℂ :=
  MvPolynomial.aeval (closedVarFamily M)

/-- The closed substitution family: `X ↦ X₀`. -/
def closedInclFamily (M : ℕ) : Fin 1 → lineRing M :=
  fun _ => (X ⟨0, by have := M; omega⟩ : lineRing M)

/-- **THE CLOSED SUBSTITUTION.** -/
def blockInclClosed (M : ℕ) :
    MvPolynomial (Fin 1) ℂ →ₐ[ℂ] lineRing M :=
  MvPolynomial.aeval (closedInclFamily M)

theorem blockProjClosed_X_zero (M : ℕ) :
    blockProjClosed M (X ⟨0, by omega⟩ : lineRing M) =
      (X ⟨0, by omega⟩ : MvPolynomial (Fin 1) ℂ) := by
  rw [blockProjClosed, aeval_X, closedVarFamily, if_pos rfl]

theorem blockProjClosed_X_ne_zero (M : ℕ) {a : Fin (2 * M)}
    (ha : a.val ≠ 0) :
    blockProjClosed M (X a) = 0 := by
  rw [blockProjClosed, aeval_X, closedVarFamily, if_neg ha]

theorem blockProjClosed_comp_blockInclClosed (M : ℕ) :
    (blockProjClosed M).comp (blockInclClosed M) =
      AlgHom.id ℂ (MvPolynomial (Fin 1) ℂ) := by
  refine MvPolynomial.algHom_ext' fun a => ?_
  rw [AlgHom.coe_comp, DFunLike.coe_fn_eq, AlgHom.coe_id, id_eq,
    blockInclClosed, aeval_X, closedInclFamily]
  have ha0 : (⟨0, by omega⟩ : Fin (2 * M)).val = 0 := rfl
  show blockProjClosed M (X ⟨0, by have := M; omega⟩ : lineRing M) = _
  rw [blockProjClosed_X_zero]
  rfl

/-- The closed projector ideal. -/
def closedProjectorIdeal (M : ℕ) : Ideal (lineRing M) :=
  Ideal.span (Set.range fun a : Fin (2 * M) =>
    (X a : lineRing M) - blockInclClosed M (blockProjClosed M (X a)))

/-- **THE CLOSED OUTSIDE IDEAL** — the span of all variables except
`X₀`. -/
def closedOutsideIdealRing (M : ℕ) : Ideal (lineRing M) :=
  Ideal.span (Set.range fun b : {b : Fin (2 * M) // b.val ≠ 0} =>
    (X b.1 : lineRing M))

theorem mem_closedOutsideIdealRing (M : ℕ) {a : Fin (2 * M)}
    (ha : a.val ≠ 0) :
    (X a : lineRing M) ∈ closedOutsideIdealRing M :=
  Ideal.subset_span ⟨⟨a, ha⟩, rfl⟩

/-- Every polynomial is congruent to its closed projector modulo the
closed projector ideal. -/
theorem sub_closedProjector_mem (M : ℕ) (q : lineRing M) :
    q - blockInclClosed M (blockProjClosed M q) ∈ closedProjectorIdeal M := by
  have hagree : (Ideal.Quotient.mkₐ ℂ (closedProjectorIdeal M)).comp
      ((blockInclClosed M).comp (blockProjClosed M)) =
      (Ideal.Quotient.mkₐ ℂ (closedProjectorIdeal M)) := by
    refine MvPolynomial.algHom_ext' fun a => ?_
    have hgen : (X a : lineRing M) - blockInclClosed M (blockProjClosed M (X a)) ∈
        closedProjectorIdeal M := Ideal.subset_span ⟨a, rfl⟩
    have hq := (Ideal.Quotient.eq (I := closedProjectorIdeal M)).mpr hgen
    exact hq.symm
  have happ := DFunLike.congr_fun hagree q
  rw [AlgHom.coe_comp, DFunLike.coe_fn_eq] at happ
  have hz : (Ideal.Quotient.mkₐ ℂ (closedProjectorIdeal M)) (q -
      blockInclClosed M (blockProjClosed M q)) = 0 := by
    rw [map_sub, happ, sub_self]
    rfl
  exact Ideal.Quotient.eq_zero_iff_mem.mp hz

theorem closedProjectorIdeal_le_closedOutside (M : ℕ) :
    closedProjectorIdeal M ≤ closedOutsideIdealRing M := by
  rw [closedProjectorIdeal, Ideal.span_le]
  rintro _ ⟨a, rfl⟩
  rcases eq_or_ne a.val 0 with h | h
  · rw [h, blockProjClosed_X_zero M]
    have hin : blockInclClosed M (X ⟨0, by omega⟩ : MvPolynomial (Fin 1) ℂ) =
        (X ⟨0, by have := M; omega⟩ : lineRing M) := by
      rw [blockInclClosed, aeval_X, closedInclFamily]
    rw [hin, sub_self]
    exact Submodule.zero_mem _
  · rw [blockProjClosed_X_ne_zero M h, map_zero, sub_zero]
    exact mem_closedOutsideIdealRing M h

/-- **THE CLOSED KERNEL LAW.** -/
theorem ker_blockProjClosed (M : ℕ) :
    RingHom.ker (blockProjClosed M).toRingHom = closedOutsideIdealRing M := by
  apply le_antisymm
  · intro t ht
    have hPzero : blockInclClosed M (blockProjClosed M t) = 0 := by
      rw [RingHom.mem_ker] at ht
      rw [ht, map_zero]
    have hmem : t - blockInclClosed M (blockProjClosed M t) ∈
        closedProjectorIdeal M := sub_closedProjector_mem M t
    rw [hPzero, sub_zero] at hmem
    exact closedProjectorIdeal_le_closedOutside M hmem
  · rw [closedOutsideIdealRing, Ideal.span_le]
    rintro _ ⟨b, hb, rfl⟩
    rw [RingHom.mem_ker, blockProjClosed_X_ne_zero M hb.2]

/-- **THE CLOSED IDEAL** — the span of the images of all variables except
`X₀`: the prime of the closed point `[1:0:0:…]` on the 0-th line. -/
def lineClosedIdeal (M : ℕ) : Ideal (lineQuotient M) :=
  Ideal.span (Set.range fun b : {b : Fin (2 * M) // b.val ≠ 0} =>
    lineQuotientMap M (X b.1))

theorem mem_lineClosedIdeal (M : ℕ) {a : Fin (2 * M)} (ha : a.val ≠ 0) :
    lineQuotientMap M (X a) ∈ lineClosedIdeal M :=
  Ideal.subset_span ⟨⟨a, ha⟩, rfl⟩

theorem blockProjClosed_crossIdeal_le_ker (M : ℕ) :
    crossIdeal M ≤ RingHom.ker (blockProjClosed M).toRingHom := by
  rw [crossIdeal, Ideal.span_le]
  rintro _ ⟨a, b, hab, rfl⟩
  rw [RingHom.mem_ker, map_mul, aeval_X, aeval_X]
  rcases eq_or_ne a.val 0 with ha | ha
  · have hb : b.val ≠ 0 := fun h => hab (by rw [ha, h])
    rw [ha, blockProjClosed_X_zero M, blockProjClosed_X_ne_zero M hb,
      mul_zero]
  · rw [blockProjClosed_X_ne_zero M ha, zero_mul]

/-- **THE DESCENDED CLOSED PROJECTION.** -/
noncomputable def blockProjClosedQuot (M : ℕ) :
    lineQuotient M →ₐ[ℂ] MvPolynomial (Fin 1) ℂ :=
  Ideal.Quotient.liftₐ (crossIdeal M) (blockProjClosed M)
    (fun p hp => by
      have hk : p ∈ RingHom.ker (blockProjClosed M).toRingHom :=
        blockProjClosed_crossIdeal_le_ker M hp
      rwa [RingHom.mem_ker] at hk)

theorem blockProjClosedQuot_mk (M : ℕ) (t : lineRing M) :
    blockProjClosedQuot M (lineQuotientMap M t) = blockProjClosed M t := rfl

/-- **THE KERNEL CHARACTERIZATION AT THE CLOSED IDEAL.** -/
theorem mem_lineClosedIdeal_iff (M : ℕ) (y : lineQuotient M) :
    y ∈ lineClosedIdeal M ↔ blockProjClosedQuot M y = 0 := by
  obtain ⟨t, rfl⟩ := lineQuotientMap_surjective M y
  constructor
  · intro hy
    have hle : lineClosedIdeal M ≤
        RingHom.ker (blockProjClosedQuot M).toRingHom := by
      rw [lineClosedIdeal, Ideal.span_le]
      rintro _ ⟨b, hb, rfl⟩
      rw [RingHom.mem_ker, blockProjClosedQuot_mk,
        blockProjClosed_X_ne_zero M b.2]
    have hk := hle hy
    rwa [RingHom.mem_ker] at hk
  · intro hy
    rw [blockProjClosedQuot_mk] at hy
    have hker : t ∈ RingHom.ker (blockProjClosed M).toRingHom := by
      rw [RingHom.mem_ker]; exact hy
    have hout : t ∈ closedOutsideIdealRing M := by
      have hke := ker_blockProjClosed M
      rw [← hke] at hker
      exact hker
    have hmap : lineQuotientMap M t ∈
        Ideal.map (lineQuotientMap M).toRingHom (closedOutsideIdealRing M) :=
      Ideal.mem_map_of_mem _ hout
    rw [closedOutsideIdealRing, Ideal.map_span] at hmap
    refine (Ideal.span_le).mpr ?_ hmap
    rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
    exact Ideal.subset_span ⟨b, rfl⟩

/-- **THE CLOSED IDEAL IS PRIME.** -/
theorem lineClosedIdeal_isPrime (M : ℕ) :
    (lineClosedIdeal M).IsPrime := by
  refine ⟨?_, ?_⟩
  · intro htop
    have h1 : (1 : lineQuotient M) ∈ lineClosedIdeal M := by
      rw [htop]; trivial
    have hz := (mem_lineClosedIdeal_iff M 1).mp h1
    rw [map_one] at hz
    exact one_ne_zero hz
  · intro x y hxy
    have hx : blockProjClosedQuot M (x * y) = 0 :=
      (mem_lineClosedIdeal_iff M _).mp hxy
    rw [map_mul, mul_eq_zero] at hx
    rcases hx with h | h
    · exact Or.inl ((mem_lineClosedIdeal_iff M _).mpr h)
    · exact Or.inr ((mem_lineClosedIdeal_iff M _).mpr h)

theorem lineQuotientMap_X_zero_not_mem_lineClosedIdeal (M : ℕ) :
    lineQuotientMap M (X ⟨0, by have := M; omega⟩) ∉ lineClosedIdeal M := by
  intro hmem
  have hz := (mem_lineClosedIdeal_iff M _).mp hmem
  rw [blockProjClosedQuot_mk, blockProjClosed_X_zero M] at hz
  exact X_ne_zero ⟨0, by omega⟩ hz.symm

/-- The generic-0 ideal is contained in the closed ideal. -/
theorem lineGenericIdeal_zero_le_lineClosedIdeal (M : ℕ) :
    lineGenericIdeal M 0 ≤ lineClosedIdeal M := by
  rw [lineGenericIdeal, lineClosedIdeal, Ideal.span_le]
  rintro _ ⟨b, hb, rfl⟩
  refine Ideal.subset_span ⟨⟨b, ?_⟩, rfl⟩
  rcases b.2 with h | h
  · omega
  · omega

theorem lineQuotientMap_X_one_mem_lineClosedIdeal (M : ℕ) :
    lineQuotientMap M (X ⟨1, by have := M; omega⟩) ∈ lineClosedIdeal M :=
  mem_lineClosedIdeal M (by omega)

theorem lineQuotientMap_X_one_not_mem_lineGenericIdeal (M : ℕ) :
    lineQuotientMap M (X ⟨1, by have := M; omega⟩) ∉ lineGenericIdeal M 0 := by
  intro hmem
  have hz := (mem_lineGenericIdeal_iff M 0 _).mp hmem
  have hone : (⟨1, by omega⟩ : Fin 2).val = 1 := rfl
  have hright : (⟨1, by omega⟩ : Fin 2) = ⟨1, by omega⟩ := rfl
  show blockProjQuotAt M 0 _ = 0 at hz
  rw [blockProjQuotAt_mk, blockProjAt_X_right M 0] at hz
  · exact X_ne_zero ⟨1, by omega⟩ hz.symm
  · omega

/-! ## §2 The homogeneous ideals and the points -/

/-- The degree-one membership of a variable image (the green substrate
receipt). -/
theorem lineQuotientMap_X_mem_lineGrading_one (M : ℕ) (a : Fin (2 * M)) :
    lineQuotientMap M (X a) ∈ lineGrading M 1 :=
  lineQuotientMap_mem_lineGrading M 1 (X a)
    ((mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X ℂ a))

/-- **THE GENERIC HOMOGENEOUS IDEAL** — the generic ideal as a
`HomogeneousIdeal` of the quotient grading (a span of degree-one
elements). -/
noncomputable def lineGenericHomogeneousIdeal (M : ℕ) (i : Fin M) :
    HomogeneousIdeal (lineGrading M) where
  toSubmodule := lineGenericIdeal M i
  is_homogeneous' := by
    rw [lineGenericIdeal]
    exact Ideal.homogeneous_span (𝒜 := lineGrading M)
      (Set.range fun b : {b : Fin (2 * M) // b.val / 2 ≠ i.val} =>
        lineQuotientMap M (X b.1))
      (by
        rintro p ⟨b, hb, rfl⟩
        exact ⟨1, lineQuotientMap_X_mem_lineGrading_one M b.1⟩)

theorem lineGenericHomogeneousIdeal_toIdeal (M : ℕ) (i : Fin M) :
    (lineGenericHomogeneousIdeal M i).toIdeal = lineGenericIdeal M i := rfl

/-- **THE GENERIC POINT OF THE i-TH LINE** — the Proj-point of the i-th
generic ideal. -/
noncomputable def lineGenericPoint (M : ℕ) (i : Fin M) :
    finiteLineScheme M where
  asHomogeneousIdeal := lineGenericHomogeneousIdeal M i
  isPrime := lineGenericIdeal_isPrime M i
  not_irrelevant_le := by
    intro hle
    have hmem : lineQuotientMap M (X (blockVarLeft M i)) ∈
        lineGenericIdeal M i := by
      have h1 : lineQuotientMap M (X (blockVarLeft M i)) ∈
          (HomogeneousIdeal.irrelevant (lineGrading M)).toIdeal :=
        HomogeneousIdeal.mem_irrelevant_of_mem (lineGrading M) (by omega)
          (lineQuotientMap_X_mem_lineGrading_one M _)
      have h2 : (HomogeneousIdeal.irrelevant (lineGrading M)).toIdeal ≤
          lineGenericIdeal M i := by
        show (HomogeneousIdeal.irrelevant (lineGrading M)).toIdeal ≤
          (lineGenericHomogeneousIdeal M i).toIdeal
        exact (toIdeal_le_toIdeal_iff).mpr hle
      exact h2 h1
    exact lineQuotientMap_X_pair_not_mem M i hmem

/-- **THE CLOSED HOMOGENEOUS IDEAL.** -/
noncomputable def lineClosedHomogeneousIdeal (M : ℕ) :
    HomogeneousIdeal (lineGrading M) where
  toSubmodule := lineClosedIdeal M
  is_homogeneous' := by
    rw [lineClosedIdeal]
    exact Ideal.homogeneous_span (𝒜 := lineGrading M)
      (Set.range fun b : {b : Fin (2 * M) // b.val ≠ 0} =>
        lineQuotientMap M (X b.1))
      (by
        rintro p ⟨b, hb, rfl⟩
        exact ⟨1, lineQuotientMap_X_mem_lineGrading_one M b.1⟩)

theorem lineClosedHomogeneousIdeal_toIdeal (M : ℕ) :
    (lineClosedHomogeneousIdeal M).toIdeal = lineClosedIdeal M := rfl

/-- **THE CLOSED POINT** — `[1:0:0:…]` on the 0-th line. -/
noncomputable def lineClosedPoint (M : ℕ) :
    finiteLineScheme M where
  asHomogeneousIdeal := lineClosedHomogeneousIdeal M
  isPrime := lineClosedIdeal_isPrime M
  not_irrelevant_le := by
    intro hle
    have hmem : lineQuotientMap M (X ⟨0, by have := M; omega⟩) ∈
        lineClosedIdeal M := by
      have h1 : lineQuotientMap M (X ⟨0, by have := M; omega⟩) ∈
          (HomogeneousIdeal.irrelevant (lineGrading M)).toIdeal :=
        HomogeneousIdeal.mem_irrelevant_of_mem (lineGrading M) (by omega)
          (lineQuotientMap_X_mem_lineGrading_one M _)
      have h2 : (HomogeneousIdeal.irrelevant (lineGrading M)).toIdeal ≤
          lineClosedIdeal M := by
        show (HomogeneousIdeal.irrelevant (lineGrading M)).toIdeal ≤
          (lineClosedHomogeneousIdeal M).toIdeal
        exact (toIdeal_le_toIdeal_iff).mpr hle
      exact h2 h1
    exact lineQuotientMap_X_zero_not_mem_lineClosedIdeal M hmem

theorem lineGenericPoint_asIdeal (M : ℕ) (i : Fin M) :
    (lineGenericPoint M i).asHomogeneousIdeal.toIdeal = lineGenericIdeal M i :=
  rfl

theorem lineClosedPoint_asIdeal (M : ℕ) :
    (lineClosedPoint M).asHomogeneousIdeal.toIdeal = lineClosedIdeal M :=
  rfl

/-- Points with equal homogeneous ideals are equal (proof irrelevance on
the propositional fields). -/
theorem projectiveSpectrum_ext {R : Type*} [CommRing R]
    {x y : ProjectiveSpectrum R}
    (h : x.asHomogeneousIdeal = y.asHomogeneousIdeal) : x = y := by
  obtain ⟨I, h1, h2⟩ := x
  obtain ⟨J, k1, k2⟩ := y
  have hIJ : I = J := h
  subst hIJ
  rfl

/-! ## §3 The specialization-order bridge and the maximality of the
generic points -/

attribute [local instance] specializationOrder

/-- **THE ORDER BRIDGE** — the specialization order on the line world's
points is reverse inclusion of homogeneous ideals (the corpus's green
`prime_le_iff` pattern at this carrier). -/
theorem le_iff_ideal (M : ℕ) (x y : finiteLineScheme M) :
    x ≤ y ↔ y.asHomogeneousIdeal.toIdeal ≤ x.asHomogeneousIdeal.toIdeal := by
  rw [specializationOrder_iff_specializes]
  have key : ∀ a b : ProjectiveSpectrum (lineGrading M),
      a ∈ closure ({b} : Set (ProjectiveSpectrum (lineGrading M))) ↔
        b.asHomogeneousIdeal.toIdeal ≤ a.asHomogeneousIdeal.toIdeal := by
    intro a b
    rw [← ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure,
      ProjectiveSpectrum.vanishingIdeal_singleton]
    exact ProjectiveSpectrum.mem_zeroLocus _ _ _
  exact key x y

/-- A positive-degree homogeneous polynomial lies in the ideal generated
by the variables (the support decomposition: each support monomial of a
degree-`n ≥ 1` homogeneous polynomial has a positive exponent, hence
factors through the corresponding variable). -/
theorem homogeneous_pos_mem_span_X {M : ℕ} {n : ℕ} (hn : 0 < n)
    (t : lineRing M) (ht : IsHomogeneous t n) :
    t ∈ Ideal.span (Set.range (X : Fin (2 * M) → lineRing M)) := by
  rw [MvPolynomial.as_sum t]
  refine Submodule.sum_mem _ fun e he => ?_
  have hce : MvPolynomial.coeff e t ≠ 0 :=
    (MvPolynomial.mem_support_iff).mp he
  have hwe : Finsupp.weight 1 e = n := ht hce
  obtain ⟨a, ha⟩ : ∃ a : Fin (2 * M), 0 < e a := by
    by_contra hcon
    push_neg at hcon
    have he0 : e = 0 := Finsupp.ext fun j => by
      have := hcon j
      omega
    rw [he0, map_zero] at hwe
    omega
  have hsplit : e = Finsupp.single a 1 + (e - Finsupp.single a 1) := by
    ext j
    simp only [Finsupp.add_apply, Finsupp.single_apply]
    by_cases hja : j = a
    · rw [hja]
      simp only [if_pos rfl, Nat.add_sub_cancel]
      omega
    · rw [if_neg hja, if_neg hja, zero_add]
  refine Submodule.smul_mem _ _ ?_
  have hX : (X a : lineRing M) ∈
      Ideal.span (Set.range (X : Fin (2 * M) → lineRing M)) :=
    Submodule.subset_span (Set.mem_range_self a)
  have hmul : MvPolynomial.monomial e (MvPolynomial.coeff e t) =
      (X a : lineRing M) *
        MvPolynomial.monomial (e - Finsupp.single a 1) (MvPolynomial.coeff e t) := by
    rw [show (X a : lineRing M) =
      MvPolynomial.monomial (Finsupp.single a 1) 1 from rfl, MvPolynomial.monomial_mul,
      hsplit]
  rw [hmul]
  exact Ideal.mul_mem_right hX

/-- If every variable image lies in an ideal, the irrelevant ideal lies in
it (the positive-degree homogeneous elements lie in the variable span). -/
theorem irrelevant_le_of_mem_variables (M : ℕ) (I : Ideal (lineQuotient M))
    (h : ∀ a : Fin (2 * M), lineQuotientMap M (X a) ∈ I) :
    (HomogeneousIdeal.irrelevant (lineGrading M)).toIdeal ≤ I := by
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro i hi u hu
  obtain ⟨t, ht, rfl⟩ := (mem_lineGrading M i u).mp hu
  obtain ⟨c, hc⟩ := Submodule.mem_span_range_iff.mp
    (homogeneous_pos_mem_span_X hi t ((mem_homogeneousSubmodule _ _).mp ht))
  rw [map_sum]
  refine Submodule.sum_mem _ fun a _ => ?_
  exact Submodule.smul_mem _ _ (h a)

/-- Every point of the line world has a variable avoiding its ideal. -/
theorem exists_variable_not_mem (M : ℕ) (y : finiteLineScheme M) :
    ∃ a : Fin (2 * M), lineQuotientMap M (X a) ∉
      y.asHomogeneousIdeal.toIdeal := by
  by_contra hcon
  simp only [not_not] at hcon
  apply y.not_irrelevant_le
  show (HomogeneousIdeal.irrelevant (lineGrading M)).toIdeal ≤
    y.asHomogeneousIdeal.toIdeal
  exact irrelevant_le_of_mem_variables M _ (fun a => hcon a)

/-- **THE GENERIC POINTS ARE MAXIMAL** — a relevant point whose ideal is
contained in the i-th generic ideal IS the i-th generic point. -/
theorem eq_lineGenericPoint_of_le (M : ℕ) (i : Fin M)
    (y : finiteLineScheme M)
    (hy : y.asHomogeneousIdeal.toIdeal ≤ lineGenericIdeal M i) :
    y = lineGenericPoint M i := by
  obtain ⟨a, ha⟩ := exists_variable_not_mem M y
  rcases eq_or_ne (a.val / 2) i.val with hblock | hblock
  · have hgen : lineGenericIdeal M i ≤ y.asHomogeneousIdeal.toIdeal := by
      rw [lineGenericIdeal, Ideal.span_le]
      rintro _ ⟨b, hb, rfl⟩
      have hzero : lineQuotientMap M (X a) * lineQuotientMap M (X b.1) = 0 :=
        crossMul_eq_zero M (fun hcon => hb (by rw [hcon]; omega))
      have hmem : lineQuotientMap M (X a) * lineQuotientMap M (X b.1) ∈
          y.asHomogeneousIdeal.toIdeal := by
        rw [hzero]; exact Submodule.zero_mem _
      rcases y.isPrime.mem_or_mem hmem with h1 | h2
      · exact absurd h1 ha
      · exact h2
    have hideal : y.asHomogeneousIdeal.toIdeal = lineGenericIdeal M i :=
      le_antisymm hy hgen
    refine projectiveSpectrum_ext ?_
    refine HomogeneousIdeal.ext ?_
    rw [lineGenericPoint_asIdeal M i]
    exact hideal
  · have hyin : lineQuotientMap M (X (blockVarLeft M i)) ∈
        y.asHomogeneousIdeal.toIdeal := by
      have hzero : lineQuotientMap M (X a) *
          lineQuotientMap M (X (blockVarLeft M i)) = 0 :=
        crossMul_eq_zero M
          (fun hcon => hblock (hcon.trans (blockVarLeft_block M i).symm))
      have hmem : lineQuotientMap M (X a) *
          lineQuotientMap M (X (blockVarLeft M i)) ∈
          y.asHomogeneousIdeal.toIdeal := by
        rw [hzero]; exact Submodule.zero_mem _
      rcases y.isPrime.mem_or_mem hmem with h1 | h2
      · exact absurd h1 ha
      · exact h2
    exact lineQuotientMap_X_pair_not_mem M i (hy hyin)

/-- **THE COHEIGHT-ZERO RECEIPT** — the i-th generic point is maximal in
the specialization order. -/
theorem lineGenericPoint_coheight (M : ℕ) (i : Fin M) :
    Order.coheight (lineGenericPoint M i) = 0 := by
  rw [Order.coheight_eq_zero]
  intro y hy
  have hle : y.asHomogeneousIdeal.toIdeal ≤ lineGenericIdeal M i := by
    rw [← lineGenericPoint_asIdeal M i]
    exact (le_iff_ideal M y (lineGenericPoint M i)).mp (le_of_lt hy)
  exact eq_lineGenericPoint_of_le M i y hle

/-! ## §4 The no-intermediate law (the height route) -/

/-- **THE CLOSED POINT LIES STRICTLY BELOW THE 0-TH GENERIC POINT.** -/
theorem lineClosedPoint_lt (M : ℕ) :
    lineClosedPoint M < lineGenericPoint M 0 := by
  refine ⟨(le_iff_ideal M (lineClosedPoint M) (lineGenericPoint M 0)).mpr ?_, ?_⟩
  · rw [lineClosedPoint_asIdeal, lineGenericPoint_asIdeal]
    exact lineGenericIdeal_zero_le_lineClosedIdeal M
  · intro heq
    have h1 : lineQuotientMap M (X ⟨1, by have := M; omega⟩) ∈ lineClosedIdeal M :=
        lineQuotientMap_X_one_mem_lineClosedIdeal M
    have h2 : lineQuotientMap M (X ⟨1, by have := M; omega⟩) ∉
        lineGenericIdeal M 0 :=
        lineQuotientMap_X_one_not_mem_lineGenericIdeal M
    apply h2
    have hII : (lineClosedPoint M).asHomogeneousIdeal =
        (lineGenericPoint M 0).asHomogeneousIdeal :=
      congrArg ProjectiveSpectrum.asHomogeneousIdeal heq
    have h1' := congrArg HomogeneousIdeal.toIdeal hII
    rw [lineClosedPoint_asIdeal, lineGenericPoint_asIdeal] at h1'
    rw [← h1']
    exact h1

/-- The closed ideal is the join of the 0-th generic ideal and the
`X₁`-image principal ideal. -/
theorem lineClosedIdeal_eq_sup (M : ℕ) :
    lineClosedIdeal M = lineGenericIdeal M 0 ⊔
      Ideal.span {lineQuotientMap M (X (blockVarRight M 0))} := by
  apply le_antisymm
  · rw [lineClosedIdeal, Ideal.span_le]
    rintro _ ⟨b, hb, rfl⟩
    rcases b.1.val with _ | bv
    · exact absurd rfl hb
    · rcases bv with _ | bv
      · exact Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton _))
      · refine Submodule.mem_sup_left (mem_lineGenericIdeal M ?_)
        have hbv : 2 ≤ b.1.val := by omega
        omega
  · refine Submodule.sup_le.mpr ⟨?_, ?_⟩
    · exact lineGenericIdeal_zero_le_lineClosedIdeal M
    · rw [Ideal.span_le]
      rintro _ rfl
      exact lineQuotientMap_X_one_mem_lineClosedIdeal M

/-- **THE NO-INTERMEDIATE LAW** — no point of the line world has its ideal
strictly between the 0-th generic ideal and the closed ideal.  The route:
transport to ℂ[Y,Z] (the quotient by the generic ideal, through the
surjective block-0 retraction), then kill by Krull's principal ideal
theorem. -/
theorem no_intermediate_point (M : ℕ) (y : finiteLineScheme M)
    (hgen : lineGenericIdeal M 0 ≤ y.asHomogeneousIdeal.toIdeal)
    (hstrict : y.asHomogeneousIdeal.toIdeal < lineClosedIdeal M) :
    False := by
  -- the block-0 substitution (Y ↦ q X₀, Z ↦ q X₁) and its retraction
  -- roundtrip: the retraction is a left inverse
  have hround : ∀ g : MvPolynomial (Fin 2) ℂ,
      blockProjQuotAt M 0 (blockInclAt M 0 g) = g := by
    intro g
    have hcomp : (blockProjQuotAt M 0).comp (blockInclAt M 0) =
        AlgHom.id ℂ (MvPolynomial (Fin 2) ℂ) := by
      refine MvPolynomial.algHom_ext' fun a => ?_
      rw [AlgHom.coe_comp, DFunLike.coe_fn_eq, AlgHom.coe_id, id_eq,
        blockInclAt_X]
      cases a.val with
      | zero =>
          show blockProjQuotAt M 0 (lineQuotientMap M (X (blockVarLeft M 0))) = _
          rw [blockProjQuotAt_X_left]
          rfl
      | succ av =>
          show blockProjQuotAt M 0 (lineQuotientMap M
            (X (blockVarRight M 0))) = _
          rw [blockProjQuotAt_X_right]
          rfl
    have hgg := DFunLike.congr_fun hcomp g
    simpa using hgg
  -- the retraction is surjective (the substitution is a section)
  have hsurj : Function.Surjective (blockProjQuotAt M 0) := by
    intro g
    refine ⟨blockInclAt M 0 g, hround g⟩
  -- the transported prime
  set ȳ : Ideal (MvPolynomial (Fin 2) ℂ) :=
    Ideal.map (blockProjQuotAt M 0).toRingHom y.asHomogeneousIdeal.toIdeal
    with hȳdef
  have hȳprime : ȳ.IsPrime := by
    refine ⟨?_, ?_⟩
    · intro htop
      have h1 : (1 : MvPolynomial (Fin 2) ℂ) ∈ ȳ := by
        rw [htop]; trivial
      obtain ⟨w, hw, hw1⟩ := (Ideal.mem_map_iff_of_surjective _ hsurj).mp h1
      have hwker : 1 - w ∈ lineGenericIdeal M 0 := by
        rw [← mem_lineGenericIdeal_iff, blockProjQuotAt_mk]
        rw [map_sub, hw1, sub_self]
        rfl
      have hwmem : (1 : lineQuotient M) ∈ y.asHomogeneousIdeal.toIdeal := by
        have hsub : w + (1 - w) ∈ y.asHomogeneousIdeal.toIdeal :=
          Submodule.add_mem _ hw (hgen hwker)
        simpa [sub_add_cancel] using hsub
      exact y.isPrime.ne_top (Ideal.eq_top_of_one_mem hwmem)
    · intro a b hab
      obtain ⟨ã, hã⟩ := hsurj a
      obtain ⟨b̃, hb̃⟩ := hsurj b
      obtain ⟨w, hw, hwab⟩ := (Ideal.mem_map_iff_of_surjective _ hsurj).mp hab
      have hd : w - ã * b̃ ∈ lineGenericIdeal M 0 := by
        rw [← mem_lineGenericIdeal_iff, blockProjQuotAt_mk]
        rw [map_sub, hwab, map_mul, hã, hb̃, sub_self]
        rfl
      have hmem : ã * b̃ ∈ y.asHomogeneousIdeal.toIdeal := by
        have hsub : (w - ã * b̃) + ã * b̃ ∈ y.asHomogeneousIdeal.toIdeal :=
          Submodule.add_mem _ (hgen hd) hw
        simpa [sub_add_cancel] using hsub
      rcases y.isPrime.mem_or_mem hmem with h1 | h2
      · exact Or.inl
          ((Ideal.mem_map_iff_of_surjective _ hsurj).mpr ⟨ã, h1, hã⟩)
      · exact Or.inr
          ((Ideal.mem_map_iff_of_surjective _ hsurj).mpr ⟨b̃, h2, hb̃⟩)
  -- ȳ is nonzero: y strictly contains the generic ideal
  have hȳne : ȳ ≠ ⊥ := by
    intro hbot
    obtain ⟨f, hf, hfne⟩ : ∃ f ∈ y.asHomogeneousIdeal.toIdeal,
        f ∉ lineGenericIdeal M 0 := by
      by_contra hcon
      push_neg at hcon
      exact hstrict.ne (le_antisymm hstrict.le hcon)
    have hfimg : blockProjQuotAt M 0 f ∈ ȳ :=
      (Ideal.mem_map_iff_of_surjective _ hsurj).mpr ⟨f, hf, rfl⟩
    have hf0 : blockProjQuotAt M 0 f ≠ 0 := by
      intro h0
      exact hfne ((mem_lineGenericIdeal_iff M 0 f).mpr h0)
    rw [hbot] at hfimg
    exact hf0 (Submodule.mem_bot.mp hfimg)
  -- the closed ideal's image is the principal ideal (Z)
  have hmapclosed : Ideal.map (blockProjQuotAt M 0).toRingHom
      (lineClosedIdeal M) =
      Ideal.span {(X ⟨1, by omega⟩ : MvPolynomial (Fin 2) ℂ)} := by
    rw [lineClosedIdeal, Ideal.map_span]
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro _ ⟨b, hb, rfl⟩
      rcases b.1.val with _ | bv
      · exact absurd rfl hb
      · rcases bv with _ | bv
        · have hidx : (⟨1, by have := M; omega⟩ : Fin (2 * M)) = blockVarRight M 0 :=
            Fin.ext (by rw [blockVarRight_val]; have := M; omega)
          rw [hidx, blockProjQuotAt_X_right M 0]
          exact Ideal.subset_span (Set.mem_singleton _)
        · rw [blockProjQuotAt_X_outside M 0 (by omega)]
          exact Submodule.zero_mem _
    · rw [Ideal.span_le]
      rintro _ rfl
      refine Submodule.subset_span ⟨_, lineQuotientMap_X_one_mem_lineClosedIdeal M, ?_⟩
      have hidx : (⟨1, by have := M; omega⟩ : Fin (2 * M)) = blockVarRight M 0 :=
        Fin.ext (by rw [blockVarRight_val]; have := M; omega)
      rw [hidx]
  -- ȳ lies inside (Z) (the closed ideal's image is (Z), and y's ideal
  -- lies in the closed ideal)
  have hȳle : ȳ ≤ Ideal.span {(X ⟨1, by omega⟩ : MvPolynomial (Fin 2) ℂ)} := by
    rw [hȳdef, hmapclosed]
    exact Ideal.map_mono hstrict.le
  -- ȳ is strictly below (Z) (else the closed ideal would lie in y's)
  have hȳneZ : ȳ ≠ Ideal.span {(X ⟨1, by omega⟩ : MvPolynomial (Fin 2) ℂ)} := by
    intro heq
    have hZmem : (X ⟨1, by omega⟩ : MvPolynomial (Fin 2) ℂ) ∈ ȳ := by
      rw [heq]; exact Ideal.subset_span (Set.mem_singleton _)
    obtain ⟨w, hw, hwZ⟩ := (Ideal.mem_map_iff_of_surjective _ hsurj).mp hZmem
    have hXmem : lineQuotientMap M (X (blockVarRight M 0)) ∈
        y.asHomogeneousIdeal.toIdeal := by
      have hd : w - lineQuotientMap M (X (blockVarRight M 0)) ∈
          lineGenericIdeal M 0 := by
        rw [← mem_lineGenericIdeal_iff, blockProjQuotAt_mk]
        rw [map_sub, hwZ, blockProjQuotAt_X_right M 0, sub_self]
        rfl
      have hsub : (w - lineQuotientMap M (X (blockVarRight M 0))) +
          lineQuotientMap M (X (blockVarRight M 0)) ∈
          y.asHomogeneousIdeal.toIdeal :=
        Submodule.add_mem _ (hgen hd) hw
      simpa [sub_add_cancel] using hsub
    apply hstrict.ne
    rw [← lineClosedIdeal_eq_sup M, Submodule.sup_le]
    exact ⟨hgen, by
      rw [Ideal.span_le]
      rintro _ rfl
      exact hXmem⟩
  -- the height kill: Krull's principal ideal theorem (green at the pin)
  have hZnd : (X ⟨1, by omega⟩ : MvPolynomial (Fin 2) ℂ) ∈ nonZeroDivisors _ :=
    mem_nonZeroDivisors_iff_ne_zero.mpr (X_ne_zero ⟨1, by omega⟩)
  have hZunit : ¬ IsUnit (X ⟨1, by omega⟩ : MvPolynomial (Fin 2) ℂ) := by
    intro hun
    obtain ⟨v, hv⟩ := hun.exists_right_inv
    have hc := MvPolynomial.coeff_X_mul' (0 : Fin 2 →₀ ℕ) ⟨1, by omega⟩ v
    rw [hv] at hc
    rw [if_neg (by simp)] at hc
    simpa using hc.symm
  have hheight : (Ideal.span {(X ⟨1, by omega⟩ : MvPolynomial (Fin 2) ℂ)}).height = 1 :=
    Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors hZnd hZunit
  obtain ⟨P, hPprime, hPle, hPheight⟩ :=
    Ideal.exists_isPrime_height_eq (I :=
      Ideal.span {(X ⟨1, by omega⟩ : MvPolynomial (Fin 2) ℂ)}) hheight
  have hȳltP : (⟨ȳ, hȳprime⟩ : PrimeSpectrum (MvPolynomial (Fin 2) ℂ)).asIdeal <
      (⟨P, hPprime⟩ : PrimeSpectrum (MvPolynomial (Fin 2) ℂ)).asIdeal := by
    refine ⟨le_trans hȳle hPle, ?_⟩
    intro heq
    have hZle : Ideal.span {(X ⟨1, by omega⟩ : MvPolynomial (Fin 2) ℂ)} ≤ ȳ := by
      rw [heq]; exact hPle
    exact hȳneZ (le_antisymm hȳle hZle)
  have hȳltP' : (⟨ȳ, hȳprime⟩ : PrimeSpectrum (MvPolynomial (Fin 2) ℂ)) <
      ⟨P, hPprime⟩ := (PrimeSpectrum.asIdeal_lt_asIdeal _ _).mpr hȳltP
  have hPheight' : Order.height
      (⟨P, hPprime⟩ : PrimeSpectrum (MvPolynomial (Fin 2) ℂ)) = 1 := by
    rw [← PrimeSpectrum.height_eq_orderHeight ⟨P, hPprime⟩]
    exact hPheight
  have hȳzero : Order.height
      (⟨ȳ, hȳprime⟩ : PrimeSpectrum (MvPolynomial (Fin 2) ℂ)) = 0 := by
    have hle := (Order.height_le_coe_iff (x :=
      (⟨P, hPprime⟩ : PrimeSpectrum (MvPolynomial (Fin 2) ℂ))) (n := 1)).mp
      (by rw [hPheight']; exact le_refl 1)
    have hlt := hle _ hȳltP'
    omega
  have hȳheight : ȳ.height = 0 := by
    rw [← PrimeSpectrum.height_eq_orderHeight ⟨ȳ, hȳprime⟩]
    exact hȳzero
  exact hȳne (Ideal.height_eq_zero_iff_eq_bot.mp hȳheight)

/-- **THE CLOSED POINT HAS COHEIGHT ONE.**  The lower bound is the strict
specialization below the generic point; the upper bound is the
no-intermediate law. -/
theorem lineClosedPoint_coheight (M : ℕ) :
    Order.coheight (lineClosedPoint M) = 1 := by
  apply Nat.le_antisymm
  · rw [Order.coheight_le_coe_iff]
    intro w hw
    have hwle : w.asHomogeneousIdeal.toIdeal ≤ lineClosedIdeal M :=
      (le_iff_ideal M (lineClosedPoint M) w).mp hw.le
    have hwne : w.asHomogeneousIdeal.toIdeal ≠ lineClosedIdeal M := by
      intro heq
      have hwceq : w = lineClosedPoint M := by
        refine projectiveSpectrum_ext ?_
        refine HomogeneousIdeal.ext ?_
        rw [lineClosedPoint_asIdeal]
        exact heq
      exact hw.ne hwceq.symm
    have hgen : lineGenericIdeal M 0 ≤ w.asHomogeneousIdeal.toIdeal := by
      rw [lineGenericIdeal, Ideal.span_le]
      rintro _ ⟨b, hb, rfl⟩
      have hzero : lineQuotientMap M (X ⟨0, by have := M; omega⟩) *
          lineQuotientMap M (X b.1) = 0 :=
        crossMul_eq_zero M (fun hcon => hb (by rw [hcon]; omega))
      have hX0 : lineQuotientMap M (X ⟨0, by have := M; omega⟩) ∉
          w.asHomogeneousIdeal.toIdeal := fun hmem =>
        lineQuotientMap_X_zero_not_mem_lineClosedIdeal M (hwle hmem)
      have hmem : lineQuotientMap M (X ⟨0, by have := M; omega⟩) *
          lineQuotientMap M (X b.1) ∈ w.asHomogeneousIdeal.toIdeal := by
        rw [hzero]; exact Submodule.zero_mem _
      rcases w.isPrime.mem_or_mem hmem with h1 | h2
      · exact absurd h1 hX0
      · exact h2
    rcases eq_or_ne w.asHomogeneousIdeal.toIdeal (lineGenericIdeal M 0) with heq | hne
    · have hwgen : w = lineGenericPoint M 0 :=
        eq_lineGenericPoint_of_le M 0 w (by rw [heq]; exact le_rfl)
      rw [hwgen]
      exact lineGenericPoint_coheight M 0
    · exact absurd (no_intermediate_point M w hgen ⟨hwle, hwne⟩) False.elim
  · have h := Order.coheight_add_one_le (lineClosedPoint_lt M)
    rw [lineGenericPoint_coheight M 0] at h
    simpa using h

/-! ## §5 The component machinery -/

/-- The generic points are distinguished by their ideals. -/
theorem lineGenericPoint_injective (M : ℕ) :
    Function.Injective (lineGenericPoint M) := by
  intro i k hik
  by_contra hne
  have hne' : i.val ≠ k.val := fun h => hne (Fin.ext h)
  have hmem : lineQuotientMap M (X (blockVarLeft M i)) ∈
      lineGenericIdeal M k :=
    mem_lineGenericIdeal M (by rw [blockVarLeft_val]; omega)
  have hnot : lineQuotientMap M (X (blockVarLeft M i)) ∉
      lineGenericIdeal M i :=
    lineQuotientMap_X_pair_not_mem M i
  apply hnot
  have hII : (lineGenericPoint M i).asHomogeneousIdeal =
      (lineGenericPoint M k).asHomogeneousIdeal :=
    congrArg ProjectiveSpectrum.asHomogeneousIdeal hik
  have h1 := congrArg HomogeneousIdeal.toIdeal hII
  rw [lineGenericPoint_asIdeal, lineGenericPoint_asIdeal] at h1
  rw [← h1]
  exact hmem

/-- **THE COHEIGHT-ZERO POINTS ARE THE GENERIC POINTS.** -/
theorem exists_eq_lineGenericPoint (M : ℕ) (η : finiteLineScheme M)
    (hη : Order.coheight η = 0) :
    ∃ i : Fin M, η = lineGenericPoint M i := by
  obtain ⟨a, ha⟩ := exists_variable_not_mem M η
  have hmax : IsMax η := (Order.coheight_eq_zero).mp hη
  refine ⟨⟨a.val / 2, by have := a.isLt; omega⟩, ?_⟩
  have hgen : lineGenericIdeal M ⟨a.val / 2, by have := a.isLt; omega⟩ ≤
      η.asHomogeneousIdeal.toIdeal := by
    rw [lineGenericIdeal, Ideal.span_le]
    rintro _ ⟨b, hb, rfl⟩
    have hzero : lineQuotientMap M (X a) * lineQuotientMap M (X b.1) = 0 :=
      crossMul_eq_zero M (fun hcon => hb (by rw [hcon]; omega))
    have hmem : lineQuotientMap M (X a) * lineQuotientMap M (X b.1) ∈
        η.asHomogeneousIdeal.toIdeal := by
      rw [hzero]; exact Submodule.zero_mem _
    rcases η.isPrime.mem_or_mem hmem with h1 | h2
    · exact absurd h1 ha
    · exact h2
  refine hmax ((le_iff_ideal M η (lineGenericPoint M
      ⟨a.val / 2, by have := a.isLt; omega⟩)).mpr ?_)
  rw [lineGenericPoint_asIdeal]
  exact hgen

/-- **THE GENERIC INDEX** — the coheight-zero points indexed by `Fin M`. -/
noncomputable def lineIndexOfGeneric (M : ℕ)
    (η : CodimensionPoint (finiteLineScheme M) 0) : Fin M :=
  Classical.choose (exists_eq_lineGenericPoint M η.1 η.2)

theorem lineIndexOfGeneric_spec (M : ℕ)
    (η : CodimensionPoint (finiteLineScheme M) 0) :
    lineGenericPoint M (lineIndexOfGeneric M η) = η.1 :=
  Classical.choose_spec (exists_eq_lineGenericPoint M η.1 η.2)

theorem lineIndexOfGeneric_lineGenericPoint (M : ℕ) (i : Fin M) :
    lineIndexOfGeneric M ⟨lineGenericPoint M i, lineGenericPoint_coheight M i⟩ = i :=
  lineGenericPoint_injective M (lineIndexOfGeneric_spec M _).symm

/-- **THE UNIQUE GENERIC ABOVE A COHEIGHT-ONE POINT.** -/
theorem exists_unique_generic_above (M : ℕ)
    (x : CodimensionPoint (finiteLineScheme M) 1) :
    ∃ η₀ : CodimensionPoint (finiteLineScheme M) 0, x.1 < η₀.1 ∧
      ∀ η : CodimensionPoint (finiteLineScheme M) 0, x.1 < η.1 → η = η₀ := by
  have hfin : Order.coheight x.1 < ⊤ := by
    rw [x.2]; exact ENat.natCast_lt_top 1
  have hlt : (0 : ℕ) < Order.coheight x.1 := by rw [x.2]; norm_num
  obtain ⟨η, hxη, hη⟩ :=
    (Order.coe_lt_coheight_iff (x := x.1) (n := 0) hfin).mp hlt
  refine ⟨⟨η, hη⟩, hxη, ?_⟩
  rintro ⟨η', hη'⟩ hxη'
  obtain ⟨k, hk⟩ := exists_eq_lineGenericPoint M η hη
  obtain ⟨k', hk'⟩ := exists_eq_lineGenericPoint M η' hη'
  have hkx : lineGenericIdeal M k ≤ x.1.asHomogeneousIdeal.toIdeal := by
    rw [hk] at hxη
    rw [lineGenericPoint_asIdeal]
    exact (le_iff_ideal M x.1 (lineGenericPoint M k)).mp (le_of_lt hxη)
  have hkx' : lineGenericIdeal M k' ≤ x.1.asHomogeneousIdeal.toIdeal := by
    rw [hk'] at hxη'
    rw [lineGenericPoint_asIdeal]
    exact (le_iff_ideal M x.1 (lineGenericPoint M k')).mp (le_of_lt hxη')
  have hkk : k = k' := by
    by_contra hne
    apply x.1.not_irrelevant_le
    show (HomogeneousIdeal.irrelevant (lineGrading M)).toIdeal ≤
      x.1.asHomogeneousIdeal.toIdeal
    exact irrelevant_le_of_mem_variables M _ (fun a => by
      rcases eq_or_ne (a.val / 2) k.val with hblock | hblock
      · exact hkx' (mem_lineGenericIdeal M
          (fun hcon => hne (hblock.trans hcon.symm)))
      · exact hkx (mem_lineGenericIdeal M hblock))
  have hηeq : η = η' := by rw [hk, hk', hkk]
  exact Subtype.ext hηeq

/-- **THE COMPONENT MAP** — the unique generic point above a coheight-one
point. -/
noncomputable def lineComponentOf (M : ℕ)
    (x : CodimensionPoint (finiteLineScheme M) 1) :
    CodimensionPoint (finiteLineScheme M) 0 :=
  ⟨Classical.choose (exists_unique_generic_above M x),
    by
      have h := (Classical.choose_spec (exists_unique_generic_above M x)).1
      -- h : x.1 < (choose).1 — the coheight receipt of the chosen point
      obtain ⟨η₀, hη₀₀, -⟩ := exists_unique_generic_above M x
      have : Classical.choose (exists_unique_generic_above M x) = η₀ :=
        (Classical.choose_spec (exists_unique_generic_above M x)).2 η₀ hη₀₀
      rw [this]
      exact hη₀₀.2⟩

theorem lineComponentOf_above (M : ℕ)
    (x : CodimensionPoint (finiteLineScheme M) 1) :
    x.1 < (lineComponentOf M x).1 :=
  (Classical.choose_spec (exists_unique_generic_above M x)).1

theorem lineComponentOf_unique (M : ℕ) (x : CodimensionPoint (finiteLineScheme M) 1)
    (η : CodimensionPoint (finiteLineScheme M) 0) (hη : x.1 < η.1) :
    η = lineComponentOf M x :=
  (Classical.choose_spec (exists_unique_generic_above M x)).2 η hη

/-- **THE CLOSED POINT LIES ON THE 0-TH LINE.** -/
theorem lineClosedPoint_component (M : ℕ) :
    lineComponentOf M ⟨lineClosedPoint M, lineClosedPoint_coheight M⟩ =
      ⟨lineGenericPoint M 0, lineGenericPoint_coheight M 0⟩ :=
  lineComponentOf_unique M _ _ (lineClosedPoint_lt M)

/-! ## §6 The honest seed cycles -/

/-- The unit point-cycle is nonzero (its coefficient at the point is
one). -/
theorem codimensionPointCycle_ne_zero {X : Scheme} {p : Nat}
    (x : CodimensionPoint X p) :
    codimensionPointCycle X p x ≠ 0 := by
  intro h
  have h1 : ((codimensionPointCycle X p x : AlgebraicCycle X ℚ) : X → ℚ) x.1 = 0 := by
    rw [h]
    rfl
  have h2 : ((codimensionPointCycle X p x : AlgebraicCycle X ℚ) : X → ℚ) x.1 = 1 := by
    show Function.locallyFinsuppWithin.single x.1 (1 : ℚ) x.1 = 1
    simp
  rw [h2] at h1
  exact zero_ne_one h1

/-- **THE HONEST WEIGHT-ZERO SEED** — the atom at the 0-th generic point. -/
noncomputable def lineHonestSeedZero (M : ℕ) :
    codimensionCycles (finiteLineScheme M) 0 :=
  codimensionPointCycle (finiteLineScheme M) 0
    ⟨lineGenericPoint M 0, lineGenericPoint_coheight M 0⟩

theorem lineHonestSeedZero_ne (M : ℕ) : lineHonestSeedZero M ≠ 0 :=
  codimensionPointCycle_ne_zero _

/-- **THE HONEST WEIGHT-ONE SEED** — the atom at the closed point. -/
noncomputable def lineHonestSeedOne (M : ℕ) :
    codimensionCycles (finiteLineScheme M) 1 :=
  codimensionPointCycle (finiteLineScheme M) 1
    ⟨lineClosedPoint M, lineClosedPoint_coheight M⟩

theorem lineHonestSeedOne_ne (M : ℕ) : lineHonestSeedOne M ≠ 0 :=
  codimensionPointCycle_ne_zero _

/-! ## Receipts -/

#check lineGenericPoint
#check lineGenericPoint_coheight
#check lineClosedPoint
#check lineClosedPoint_coheight
#check lineClosedPoint_lt
#check lineClosedPoint_component
#check le_iff_ideal
#check lineComponentOf
#check lineComponentOf_above
#check lineComponentOf_unique
#check lineIndexOfGeneric
#check lineIndexOfGeneric_lineGenericPoint
#check lineHonestSeedZero
#check lineHonestSeedZero_ne
#check lineHonestSeedOne
#check lineHonestSeedOne_ne
#check crossMul_eq_zero
#check no_intermediate_point

#print axioms lineGenericPoint
#print axioms lineGenericPoint_coheight
#print axioms lineClosedPoint
#print axioms lineClosedPoint_coheight
#print axioms no_intermediate_point
#print axioms lineComponentOf
#print axioms lineHonestSeedZero_ne
#print axioms lineHonestSeedOne_ne

end GSTFiniteLinePointAlgebra

end -- noncomputable section
