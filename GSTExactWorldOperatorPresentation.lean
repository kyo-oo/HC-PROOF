import GSTMultiAxisCohomology
import GSTUniversalLefschetzPathFormula

/-!
# Exact GST operator presentation

The native origin experiment extracts every surviving polynomial coefficient.
It proves the reverse kernel inclusion left open by the first quotient
construction. Thus the native operator algebra has exactly the advertised
truncation relations, and no additional relations.
-/
noncomputable section
namespace GSTExactWorldOperatorPresentation
open GSTWorldCosmology GSTUniversalLefschetzCosmology
open GSTTruncatedWorldCohomologyRing GSTMultiAxisCohomology MvPolynomial
open scoped IsMulCommutative

variable (A B : ℕ)

def evalEndo : WorldPoly →+* Module.End ℤ (WorldCoef A B) :=
  (Subring.subtype _).comp (evalWorldPoly A B)

def origin (hA : 0 < A) (hB : 0 < B) : WorldCell A B := (⟨0,hA⟩,⟨0,hB⟩)

def cellExponent (c : WorldCell A B) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 c.2.val + Finsupp.single 1 c.1.val

private theorem exponent_eq_iff (e : Fin 2 →₀ ℕ) (c : WorldCell A B) :
    e = cellExponent A B c ↔ e 1 = c.1.val ∧ e 0 = c.2.val := by
  constructor
  · intro h
    subst e
    simp [cellExponent]
  · rintro ⟨h1,h0⟩
    ext i
    fin_cases i <;> simp [cellExponent, h1, h0]

private theorem monomial_factor (e : Fin 2 →₀ ℕ) (z : ℤ) :
    monomial e z = C z * Hpoly ^ e 0 * Vpoly ^ e 1 := by
  symm
  rw [C_mul_X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul]
  simp only [mul_one]
  have he : Finsupp.single 0 (e 0) + Finsupp.single 1 (e 1) = e := by
    ext i
    fin_cases i <;> simp
  rw [he]

private theorem shifted_origin_at (hA : 0 < A) (hB : 0 < B)
    (m n : ℕ) (c : WorldCell A B) :
    digitShiftN m (carryShiftN n (basis (origin A B hA hB))) c =
      if n = c.1.val ∧ m = c.2.val then 1 else 0 := by
  classical
  by_cases hn : n ≤ c.1.val <;> by_cases hm : m ≤ c.2.val
  · have he :
        ((⟨c.1.val-n, by omega⟩ : Fin A), (⟨c.2.val-m, by omega⟩ : Fin B)) =
          origin A B hA hB ↔ n = c.1.val ∧ m = c.2.val := by
      simp only [origin, Prod.mk.injEq, Fin.mk.injEq]
      omega
    simp [digitShiftN, carryShiftN, basis, GSTWorldPoincareDuality.worldBasis, hn, hm, he]
  · have he : ¬ (n = c.1.val ∧ m = c.2.val) := by omega
    simp [digitShiftN, hm, he]
  · have he : ¬ (n = c.1.val ∧ m = c.2.val) := by omega
    simp [digitShiftN, carryShiftN, hm, hn, he]
  · have he : ¬ (n = c.1.val ∧ m = c.2.val) := by omega
    simp [digitShiftN, hm, he]

/-- Exact origin experiment for every polynomial, not only reduced ones. -/
theorem origin_coefficient (hA : 0 < A) (hB : 0 < B)
    (p : WorldPoly) (c : WorldCell A B) :
    evalEndo A B p (basis (origin A B hA hB)) c = coeff (cellExponent A B c) p := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial e z =>
    rw [monomial_factor]
    have ha : evalEndo A B (C z * Hpoly ^ e 0 * Vpoly ^ e 1)
        (basis (origin A B hA hB)) c =
        z * digitShiftN (e 0) (carryShiftN (e 1) (basis (origin A B hA hB))) c := by
      have hz : evalEndo A B (C z) = (z : Module.End ℤ (WorldCoef A B)) := by
        have hc : (C z : WorldPoly) = (z : WorldPoly) := by simp
        rw [hc, map_intCast]
      have hh : evalEndo A B Hpoly = digitEndo A B := by simp [evalEndo]
      have hv : evalEndo A B Vpoly = carryEndo A B := by simp [evalEndo]
      rw [map_mul, map_mul, map_pow, map_pow, hz, hh, hv]
      simp [Module.End.mul_apply, digitEndo_pow_apply, carryEndo_pow_apply,
        zsmul_eq_mul]
    rw [ha, shifted_origin_at]
    rw [← monomial_factor]
    simp only [coeff_monomial, exponent_eq_iff]
    split_ifs <;> simp
  | add p q hp hq =>
    simp only [map_add, LinearMap.add_apply, Pi.add_apply, coeff_add, hp, hq]

/-- EXACT KERNEL: the native representation has no relations beyond depths. -/
theorem ker_evalWorldPoly_exact :
    RingHom.ker (evalWorldPoly A B) = truncIdeal A B := by
  apply le_antisymm
  · intro p hp
    by_cases hA : 0 < A
    · by_cases hB : 0 < B
      · rw [← rectangular_boundary]
        apply (mem_boundaryIdeal_iff_coeff _ p).mpr
        intro e he
        let c : WorldCell A B := (⟨e 1, he 1⟩,⟨e 0, he 0⟩)
        have hc : cellExponent A B c = e :=
          ((exponent_eq_iff A B e c).mpr ⟨rfl,rfl⟩).symm
        have hz : evalWorldPoly A B p = 0 := hp
        have h := origin_coefficient A B hA hB p c
        rw [hc] at h
        simpa [evalEndo, hz] using h.symm
      · have hB0 : B = 0 := by omega
        have h1 : (1 : WorldPoly) ∈ truncIdeal A B := by
          have h := Ideal.subset_span (s:={Hpoly^B,Vpoly^A}) (Set.mem_insert (Hpoly^B) {Vpoly^A})
          simpa [truncIdeal, hB0] using h
        simpa using (truncIdeal A B).mul_mem_left p h1
    · have hA0 : A = 0 := by omega
      have h1 : (1 : WorldPoly) ∈ truncIdeal A B := by
        have h := Ideal.subset_span (s:={Hpoly^B,Vpoly^A})
          (Set.mem_insert_of_mem (Hpoly^B) (Set.mem_singleton (Vpoly^A)))
        simpa [truncIdeal, hA0] using h
      simpa using (truncIdeal A B).mul_mem_left p h1
  · exact truncIdeal_le_ker_evalWorldPoly A B

/-- The abstract quotient acts faithfully on its native coefficient world. -/
theorem worldOperatorHom_injective : Function.Injective (worldOperatorHom A B) := by
  intro r s h
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective r
  obtain ⟨q,rfl⟩ := Ideal.Quotient.mk_surjective s
  have hh : evalWorldPoly A B p = evalWorldPoly A B q := h
  rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  rw [← ker_evalWorldPoly_exact]
  change evalWorldPoly A B (p-q) = 0
  rw [map_sub, hh, sub_self]

/-- Every operator in the native generated algebra is a polynomial operator. -/
theorem evalWorldPoly_surjective : Function.Surjective (evalWorldPoly A B) := by
  have hr : Subring.closure ({digitEndo A B, carryEndo A B} :
      Set (Module.End ℤ (WorldCoef A B))) ≤ (evalEndo A B).range := by
    apply Subring.closure_le.mpr
    intro x hx
    rcases hx with rfl | hx
    · exact ⟨Hpoly, by simp [evalEndo]⟩
    · have hx' : x = carryEndo A B := hx
      subst x
      exact ⟨Vpoly, by simp [evalEndo]⟩
  intro o
  obtain ⟨p,hp⟩ := hr o.property
  exact ⟨p, Subtype.ext hp⟩

/-- Exact presentation of the native operator algebra, in every rectangle. -/
def worldOperatorEquiv : WorldCohomologyRing A B ≃+* WorldOperatorRing A B :=
  RingEquiv.ofBijective (worldOperatorHom A B)
    ⟨worldOperatorHom_injective A B, by
      intro o
      obtain ⟨p,hp⟩ := evalWorldPoly_surjective A B o
      exact ⟨Ideal.Quotient.mk (truncIdeal A B) p, hp⟩⟩

/-- The last possible polarization power really survives in every nonempty
rectangle: the extinction ceiling is optimal, not merely an upper bound. -/
theorem L_pow_top_ne_zero (hA : 0 < A) (hB : 0 < B) :
    L A B ^ (A+B-2) ≠ 0 := by
  intro hz
  have h := GSTUniversalLefschetzPathFormula.path_formula_exact_boundary
    A B (A-1) (B-1) (by omega) (by omega) (basis (origin A B hA hB))
  have hD : A-1 + (B-1) = A+B-2 := by omega
  rw [hD, hz, worldAct_zero] at h
  have hb : basis (origin A B hA hB)
      ((⟨0, by omega⟩ : Fin A), (⟨0, by omega⟩ : Fin B)) = 1 := by
    simp [basis, GSTWorldPoincareDuality.worldBasis, origin]
  rw [hb, mul_one] at h
  have hc : 0 < (A+B-2).choose (B-1) := Nat.choose_pos (by omega)
  have hci : (0 : ℤ) < ((A+B-2).choose (B-1) : ℤ) := by exact_mod_cast hc
  exact (ne_of_gt hci) h.symm

/-- Exact polarization lifetime: every earlier power survives, and every
power at or beyond the dimension-derived boundary vanishes. -/
theorem L_pow_eq_zero_iff (hA : 0 < A) (hB : 0 < B) (n : ℕ) :
    L A B ^ n = 0 ↔ A+B-1 ≤ n := by
  constructor
  · intro hn
    by_contra hlt
    have hle : n ≤ A+B-2 := by omega
    exact L_pow_top_ne_zero A B hA hB (pow_eq_zero_of_le hle hn)
  · intro hn
    exact pow_eq_zero_of_le hn (rectangular_L_pow_boundary A B)

#print axioms origin_coefficient
#print axioms ker_evalWorldPoly_exact
#print axioms worldOperatorHom_injective
#print axioms worldOperatorEquiv
#print axioms L_pow_top_ne_zero
#print axioms L_pow_eq_zero_iff
end GSTExactWorldOperatorPresentation
