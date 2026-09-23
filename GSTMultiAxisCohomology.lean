import Mathlib
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Nilpotent.Basic
import GSTTruncatedWorldCohomologyRing

/-!
# GST arbitrary-axis cohomology: exact relations and universal transport

An axis set need not have two elements, or even be finite. The depth function
is the entire boundary data. The coefficient criterion below is exact: a
polynomial is extinguished precisely when all its surviving coefficients
vanish. Finite axis families additionally carry a uniform polarization bound.
-/

noncomputable section
open MvPolynomial
open scoped BigOperators

namespace GSTMultiAxisCohomology

variable {I : Type*} (d : I → ℕ)

/-- Native boundary ideal for an arbitrary family of GST axes. -/
def boundaryIdeal : Ideal (MvPolynomial I ℤ) :=
  Ideal.span ((fun e : I →₀ ℕ => monomial e (1 : ℤ)) ''
    Set.range (fun i => Finsupp.single i (d i)))

abbrev AxisRing := MvPolynomial I ℤ ⧸ boundaryIdeal d

def axis (i : I) : AxisRing d := Ideal.Quotient.mk (boundaryIdeal d) (X i)

/-- The monomial presentation is exactly the ideal of the axis depth powers. -/
theorem boundaryIdeal_eq_span_powers :
    boundaryIdeal d = Ideal.span (Set.range (fun i => (X i : MvPolynomial I ℤ) ^ d i)) := by
  unfold boundaryIdeal
  congr 1
  ext p
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨e, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, X_pow_eq_monomial⟩
  · rintro ⟨i, rfl⟩
    exact ⟨Finsupp.single i (d i), ⟨i, rfl⟩, X_pow_eq_monomial.symm⟩

/-- Exact extinction: every supported monomial crosses an axis boundary. -/
theorem mem_boundaryIdeal_iff (p : MvPolynomial I ℤ) :
    p ∈ boundaryIdeal d ↔ ∀ e ∈ p.support, ∃ i, d i ≤ e i := by
  classical
  rw [boundaryIdeal, mem_ideal_span_monomial_image]
  constructor
  · intro h e he
    obtain ⟨s, ⟨i, rfl⟩, hi⟩ := h e he
    exact ⟨i, Finsupp.single_le_iff.mp hi⟩
  · intro h e he
    obtain ⟨i, hi⟩ := h e he
    exact ⟨Finsupp.single i (d i), ⟨i, rfl⟩, Finsupp.single_le_iff.mpr hi⟩

/-- Exact surviving-coefficient test, including zero depths and infinite axis sets. -/
theorem mem_boundaryIdeal_iff_coeff (p : MvPolynomial I ℤ) :
    p ∈ boundaryIdeal d ↔ ∀ e, (∀ i, e i < d i) → coeff e p = 0 := by
  classical
  rw [mem_boundaryIdeal_iff]
  constructor
  · intro h e he
    by_contra hn
    obtain ⟨i, hi⟩ := h e (mem_support_iff.mpr hn)
    exact (Nat.not_le_of_lt (he i)) hi
  · intro h e he
    by_contra hn
    have hb : ∀ i, e i < d i := by
      intro i
      exact Nat.lt_of_not_ge (fun hi => hn ⟨i, hi⟩)
    exact (mem_support_iff.mp he) (h e hb)

/-- Two polynomial descriptions define the same world iff all live
coefficients agree. This is a complete equality criterion, not an inclusion. -/
theorem quotient_eq_iff_coeff (p q : MvPolynomial I ℤ) :
    Ideal.Quotient.mk (boundaryIdeal d) p = Ideal.Quotient.mk (boundaryIdeal d) q ↔
      ∀ e, (∀ i, e i < d i) → coeff e p = coeff e q := by
  rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem,
    mem_boundaryIdeal_iff_coeff]
  simp only [coeff_sub, sub_eq_zero]

@[simp] theorem axis_pow_depth (i : I) : axis d i ^ d i = 0 := by
  unfold axis
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, boundaryIdeal_eq_span_powers]
  exact Ideal.subset_span ⟨i, rfl⟩

/-- Every power at or beyond an axis boundary vanishes, not only the first
boundary power itself. -/
theorem axis_pow_eq_zero_of_depth_le (i : I) (n : Nat) (h : d i ≤ n) :
    axis d i ^ n = 0 := by
  have hn : n = d i + (n - d i) := by omega
  rw [hn, pow_add, axis_pow_depth, zero_mul]

/-- Exact survival for every integer amplitude: precisely the nonzero
amplitudes whose displacement stays below every axis boundary survive. -/
theorem monomial_class_ne_zero (e : I →₀ ℕ) (a : ℤ) :
    Ideal.Quotient.mk (boundaryIdeal d) (monomial e a) ≠ 0 ↔
      a ≠ 0 ∧ ∀ i, e i < d i := by
  classical
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro ha
      apply h
      simp [ha]
    · intro i
      by_contra hi
      apply h
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      apply (mem_boundaryIdeal_iff d _).mpr
      intro f hf
      have he : f = e := Finset.mem_singleton.mp (support_monomial_subset hf)
      subst f
      exact ⟨i, Nat.le_of_not_gt hi⟩
  · rintro ⟨ha, he⟩ hz
    have hm := Ideal.Quotient.eq_zero_iff_mem.mp hz
    have h := (mem_boundaryIdeal_iff_coeff d _).mp hm e he
    exact ha (by simpa using h)

/-- Exact extinction classification for a single weighted monomial. -/
theorem monomial_class_eq_zero_iff (e : I →₀ ℕ) (a : ℤ) :
    Ideal.Quotient.mk (boundaryIdeal d) (monomial e a) = 0 ↔
      a = 0 ∨ ∃ i, d i ≤ e i := by
  classical
  constructor
  · intro hz
    by_cases ha : a = 0
    · exact Or.inl ha
    · right
      by_contra hcross
      have hsmall : ∀ i, e i < d i := by
        intro i
        exact Nat.lt_of_not_ge (fun hi => hcross ⟨i, hi⟩)
      exact (monomial_class_ne_zero d e a).2 ⟨ha, hsmall⟩ hz
  · rintro (rfl | ⟨i, hi⟩)
    · simp
    · apply Ideal.Quotient.eq_zero_iff_mem.mpr
      apply (mem_boundaryIdeal_iff d _).mpr
      intro f hf
      have hfe : f = e := Finset.mem_singleton.mp (support_monomial_subset hf)
      subst f
      exact ⟨i, hi⟩

/-- A polynomial supported strictly within the world has no hidden relation. -/
theorem bounded_polynomial_faithful (p : MvPolynomial I ℤ)
    (hp : ∀ e ∈ p.support, ∀ i, e i < d i)
    (hz : Ideal.Quotient.mk (boundaryIdeal d) p = 0) : p = 0 := by
  classical
  apply MvPolynomial.ext
  intro e
  by_cases he : e ∈ p.support
  · simpa using (mem_boundaryIdeal_iff_coeff d p).mp
      (Ideal.Quotient.eq_zero_iff_mem.mp hz) e (hp e he)
  · simpa using (notMem_support_iff.mp he)

/-- **EXACT BOUNDED NORMAL FORM.**  Two representatives whose support stays
strictly inside every axis boundary represent the same cohomology class iff
they are literally the same polynomial. -/
theorem bounded_quotient_injective (p q : MvPolynomial I ℤ)
    (hp : ∀ e ∈ p.support, ∀ i, e i < d i)
    (hq : ∀ e ∈ q.support, ∀ i, e i < d i) :
    Ideal.Quotient.mk (boundaryIdeal d) p =
        Ideal.Quotient.mk (boundaryIdeal d) q ↔ p = q := by
  classical
  constructor
  · intro h
    apply MvPolynomial.ext
    intro e
    by_cases hb : ∀ i, e i < d i
    · exact (quotient_eq_iff_coeff d p q).1 h e hb
    · have hp0 : e ∉ p.support := by
        intro he
        exact hb (hp e he)
      have hq0 : e ∉ q.support := by
        intro he
        exact hb (hq e he)
      rw [notMem_support_iff.mp hp0, notMem_support_iff.mp hq0]
  · intro h
    subst q
    rfl

section Representation
variable {R : Type*} [CommRing R] (x : I → R) (hx : ∀ i, x i ^ d i = 0)

/-- Any commuting native axis family with these depths receives the GST ring. -/
def represent : AxisRing d →+* R :=
  Ideal.Quotient.lift (boundaryIdeal d)
    (eval₂Hom (Int.castRingHom R) x) (by
      change boundaryIdeal d ≤ RingHom.ker (eval₂Hom (Int.castRingHom R) x)
      rw [boundaryIdeal_eq_span_powers, Ideal.span_le]
      rintro p ⟨i, rfl⟩
      change eval₂Hom (Int.castRingHom R) x (X i ^ d i) = 0
      simpa using hx i)

@[simp] theorem represent_axis (i : I) : represent d x hx (axis d i) = x i := by
  simp [represent, axis]

/-- Equality of native ring representations is determined entirely by axes. -/
theorem representation_ext (f g : AxisRing d →+* R)
    (h : ∀ i, f (axis d i) = g (axis d i)) : f = g := by
  have hc : f.comp (Ideal.Quotient.mk (boundaryIdeal d)) =
      g.comp (Ideal.Quotient.mk (boundaryIdeal d)) := by
    apply MvPolynomial.ringHom_ext
    · intro z
      simp
    · intro i
      exact h i
  apply RingHom.ext
  intro z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact DFunLike.congr_fun hc p

include hx in
/-- Universal property with uniqueness, for arbitrary axis sets. -/
theorem existsUnique_representation :
    ∃! f : AxisRing d →+* R, ∀ i, f (axis d i) = x i := by
  refine ⟨represent d x hx, represent_axis d x hx, ?_⟩
  intro f hf
  apply representation_ext d
  intro i
  rw [hf i, represent_axis]
end Representation

/-- Finite polarized sums have a sharp dimension-derived ceiling even when
the axis coefficients are arbitrary ring elements. -/
theorem finite_polarization_bound {R : Type*} [CommRing R]
    (s : Finset I) (x : I → R) (hd : ∀ i ∈ s, 0 < d i)
    (hx : ∀ i ∈ s, x i ^ d i = 0) :
    (∑ i ∈ s, x i) ^ ((∑ i ∈ s, (d i - 1)) + 1) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    have hdi := hd i (Finset.mem_insert_self i s)
    have hxi := hx i (Finset.mem_insert_self i s)
    have hs := ih (fun j hj => hd j (Finset.mem_insert_of_mem hj))
      (fun j hj => hx j (Finset.mem_insert_of_mem hj))
    have h := (Commute.all (x i) (∑ j ∈ s, x j)).add_pow_add_eq_zero_of_pow_eq_zero hxi hs
    have he : d i - 1 + (∑ j ∈ s, (d j - 1)) + 1 =
        d i + ((∑ j ∈ s, (d j - 1)) + 1) - 1 := by omega
    rw [he]
    exact h

/-- Arbitrarily weighted GST polarization, directly inside the quotient. -/
theorem weighted_axis_polarization_bound [Fintype I]
    (hd : ∀ i, 0 < d i) (w : I → AxisRing d) :
    (∑ i, w i * axis d i) ^ ((∑ i, (d i - 1)) + 1) = 0 := by
  apply finite_polarization_bound d Finset.univ
  · intro i hi
    exact hd i
  · intro i hi
    rw [mul_pow, axis_pow_depth, mul_zero]

/-- Exact recovery of the rectangular boundary ideal. -/
theorem rectangular_boundary :
    boundaryIdeal (I:=Fin 2) ![B, A] =
      GSTTruncatedWorldCohomologyRing.truncIdeal A B := by
  classical
  rw [boundaryIdeal_eq_span_powers]
  unfold GSTTruncatedWorldCohomologyRing.truncIdeal
  congr 1
  ext p
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp [GSTTruncatedWorldCohomologyRing.Hpoly,
      GSTTruncatedWorldCohomologyRing.Vpoly]
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

/-- The old rectangular Lefschetz law now holds in the ring itself. -/
theorem rectangular_L_pow_boundary (A B : ℕ) :
    GSTTruncatedWorldCohomologyRing.L A B ^ (A+B-1) = 0 := by
  open GSTTruncatedWorldCohomologyRing in
    simpa [L, Nat.add_comm] using
      (Commute.all (H A B) (V A B)).add_pow_add_eq_zero_of_pow_eq_zero
        (H_pow_depth A B) (V_pow_depth A B)

#check axis_pow_eq_zero_of_depth_le
#check monomial_class_eq_zero_iff
#check bounded_quotient_injective
#print axioms quotient_eq_iff_coeff
#print axioms axis_pow_eq_zero_of_depth_le
#print axioms monomial_class_eq_zero_iff
#print axioms bounded_polynomial_faithful
#print axioms bounded_quotient_injective
#print axioms existsUnique_representation
#print axioms weighted_axis_polarization_bound
#print axioms rectangular_L_pow_boundary
end GSTMultiAxisCohomology
