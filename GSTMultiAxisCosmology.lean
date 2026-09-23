import Mathlib
import GSTWorldCosmology

/-!
# GST multi-axis worlds and exact operator reconstruction

The digit/carry rectangle is the two-axis instance of simultaneous native
transport. The basis orbit is cyclic: the origin generates every cell.
Consequently a commuting operator is determined by one origin experiment.
-/
noncomputable section
open scoped BigOperators

namespace GSTMultiAxisCosmology

variable {I : Type*} (d : I → ℕ)
abbrev Cell := (i : I) → Fin (d i)
abbrev Coef := Cell d → ℤ

/-- Transport by an arbitrary simultaneous axis displacement. -/
def shift (m : I → ℕ) (g : Coef d) : Coef d := by
  classical
  exact fun c => if h : ∀ i, m i ≤ (c i).val then
    g (fun i => ⟨(c i).val - m i, lt_of_le_of_lt (Nat.sub_le _ _) (c i).isLt⟩)
  else 0

@[simp] theorem shift_zero (g : Coef d) : shift d (fun _ => 0) g = g := by
  classical
  funext c
  simp [shift]

/-- The full displacement monoid acts: all axes compose simultaneously. -/
theorem shift_add (m n : I → ℕ) (g : Coef d) :
    shift d m (shift d n g) = shift d (fun i => m i + n i) g := by
  classical
  funext c
  by_cases h : ∀ i, m i + n i ≤ (c i).val
  · have hm : ∀ i, m i ≤ (c i).val := fun i => by have := h i; omega
    have hn : ∀ i, n i ≤ (c i).val - m i := fun i => by have := h i; omega
    simp [shift, h, hm, hn, Nat.sub_sub]
  · by_cases hm : ∀ i, m i ≤ (c i).val
    · have hn : ¬ ∀ i, n i ≤ (c i).val - m i := by
        intro hn
        apply h
        intro i
        have := hm i
        have := hn i
        omega
      simp [shift, h, hm, hn]
    · simp [shift, h, hm]

/-- No finite dimensionality is needed for axis commutation. -/
theorem shifts_commute (m n : I → ℕ) (g : Coef d) :
    shift d m (shift d n g) = shift d n (shift d m g) := by
  rw [shift_add, shift_add]
  simp only [Nat.add_comm]

/-- Boundary crossing is the only way a displacement extinguishes every
world, including infinite axis sets and zero-depth worlds. -/
theorem shift_boundary (m : I → ℕ) :
    (∀ g : Coef d, shift d m g = 0) ↔ ∃ i, d i ≤ m i := by
  classical
  constructor
  · intro hz
    by_contra h
    have hm : ∀ i, m i < d i := fun i =>
      Nat.lt_of_not_ge (fun hi => h ⟨i, hi⟩)
    have he := congrFun (hz (fun _ => 1)) (fun i => ⟨m i, hm i⟩)
    simp [shift] at he
  · rintro ⟨i, hi⟩ g
    funext c
    have hn : ¬ ∀ j, m j ≤ (c j).val := by
      intro hh
      have := hh i
      have := (c i).isLt
      omega
    simp [shift, hn]

/-- Native transports as integer-linear operators. -/
def shiftEndo (m : I → ℕ) : Module.End ℤ (Coef d) where
  toFun := shift d m
  map_add' f g := by
    classical
    funext c
    by_cases h : ∀ i, m i ≤ (c i).val <;> simp [shift, h]
  map_smul' z g := by
    classical
    funext c
    by_cases h : ∀ i, m i ≤ (c i).val <;> simp [shift, h]

@[simp] theorem shiftEndo_apply (m : I → ℕ) (g : Coef d) :
    shiftEndo d m g = shift d m g := rfl

theorem shiftEndo_mul (m n : I → ℕ) :
    shiftEndo d m * shiftEndo d n = shiftEndo d (fun i => m i + n i) := by
  apply LinearMap.ext
  intro g
  exact shift_add d m n g

/-- Iteration scales all native displacement coordinates simultaneously. -/
theorem shiftEndo_pow (m : I → ℕ) (n : ℕ) :
    shiftEndo d m ^ n = shiftEndo d (fun i => n * m i) := by
  induction n with
  | zero =>
      apply LinearMap.ext
      intro g
      simpa using (shift_zero d g).symm
  | succ n ih =>
      rw [pow_succ, ih, shiftEndo_mul]
      congr 1
      funext i
      exact (Nat.succ_mul n (m i)).symm

/-- Exact extinction at every exponent, without positive-depth or finite-axis
assumptions. -/
theorem shiftEndo_pow_eq_zero_iff (m : I → ℕ) (n : ℕ) :
    shiftEndo d m ^ n = 0 ↔ ∃ i, d i ≤ n * m i := by
  rw [shiftEndo_pow]
  constructor
  · intro h
    apply (shift_boundary d _).mp
    intro g
    exact congrArg (fun T : Module.End ℤ (Coef d) => T g) h
  · intro h
    apply LinearMap.ext
    intro g
    exact (shift_boundary d _).mpr h g

def origin (hd : ∀ i, 0 < d i) : Cell d := fun i => ⟨0, hd i⟩

def delta (a : Cell d) : Coef d := by
  classical
  exact fun c => if c = a then 1 else 0

/-- Every cell is reached uniquely by applying its displacement to the origin. -/
theorem shift_origin (hd : ∀ i, 0 < d i) (a : Cell d) :
    shift d (fun i => (a i).val) (delta d (origin d hd)) = delta d a := by
  classical
  funext c
  by_cases hca : c = a
  · subst c
    simp only [shift, dif_pos (fun i => Nat.le_refl (a i).val)]
    have hz : (fun i => (⟨(a i).val - (a i).val, by omega⟩ : Fin (d i))) = origin d hd := by
      funext i
      apply Fin.ext
      simp [origin]
    simp only [delta, hz, if_pos rfl]
  · by_cases h : ∀ i, (a i).val ≤ (c i).val
    · have hn : (fun i => (⟨(c i).val - (a i).val,
          lt_of_le_of_lt (Nat.sub_le _ _) (c i).isLt⟩ : Fin (d i))) ≠ origin d hd := by
        intro he
        apply hca
        funext i
        apply Fin.ext
        have hi := congrArg (fun f : Cell d => (f i).val) he
        have := h i
        change (c i).val - (a i).val = 0 at hi
        omega
      simp [shift, delta, h, hn, hca]
    · simp only [shift, dif_neg h, delta, if_neg hca]

section Finite
variable [Fintype I]

instance cellFintype : Fintype (Cell d) := by
  classical
  unfold Cell
  infer_instance

/-- Any world amplitude is the exact finite superposition of native cells. -/
theorem delta_expansion (g : Coef d) :
    (∑ a : Cell d, g a • delta d a) = g := by
  classical
  funext c
  simp [delta, Finset.sum_apply, zsmul_eq_mul]

/-- Synthesize a native mixed-shift operator from its coefficient world. -/
def synthesis (g : Coef d) : Module.End ℤ (Coef d) :=
  ∑ a : Cell d, g a • shiftEndo d (fun i => (a i).val)

/-- One origin experiment recovers every operator coefficient exactly. -/
theorem synthesis_origin (hd : ∀ i, 0 < d i) (g : Coef d) :
    synthesis d g (delta d (origin d hd)) = g := by
  classical
  simp only [synthesis, LinearMap.sum_apply, LinearMap.smul_apply,
    shiftEndo_apply, shift_origin]
  exact delta_expansion d g

/-- Bounded native mixed shifts have no hidden relations, even when a world
has a zero-depth axis. No positivity premise is needed. -/
theorem synthesis_injective :
    Function.Injective (synthesis d) := by
  intro f g h
  funext c
  have hd : ∀ i, 0 < d i := fun i => by have := (c i).isLt; omega
  have hh := congrArg (fun T : Module.End ℤ (Coef d) => T (delta d (origin d hd))) h
  have hfg : f = g := by simpa only [synthesis_origin] using hh
  exact congrFun hfg c

/-- A commuting operator is determined by its origin response on every cell. -/
theorem commuting_operator_delta (hd : ∀ i, 0 < d i)
    (T : Module.End ℤ (Coef d))
    (hT : ∀ m, Commute T (shiftEndo d m)) (a : Cell d) :
    T (delta d a) = shift d (fun i => (a i).val) (T (delta d (origin d hd))) := by
  rw [← shift_origin d hd a]
  exact congrArg (fun U : Module.End ℤ (Coef d) => U (delta d (origin d hd)))
    (hT (fun i => (a i).val)).eq

/-- Exact uniqueness from one origin observation, for the entire commutant. -/
theorem commuting_operator_ext (hd : ∀ i, 0 < d i)
    (T U : Module.End ℤ (Coef d))
    (hT : ∀ m, Commute T (shiftEndo d m))
    (hU : ∀ m, Commute U (shiftEndo d m))
    (h0 : T (delta d (origin d hd)) = U (delta d (origin d hd))) : T = U := by
  apply LinearMap.ext
  intro g
  rw [← delta_expansion d g, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [map_smul, map_smul, commuting_operator_delta d hd T hT,
    commuting_operator_delta d hd U hU, h0]

/-- Every synthesized native operator commutes with every displacement. -/
theorem synthesis_commutes (g : Coef d) (m : I → ℕ) :
    Commute (synthesis d g) (shiftEndo d m) := by
  apply LinearMap.ext
  intro f
  change synthesis d g (shiftEndo d m f) = shiftEndo d m (synthesis d g f)
  simp only [synthesis, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro a ha
  congr 1
  exact shifts_commute d (fun i => (a i).val) m f

/-- Complete classification, beyond uniqueness: every commuting operator is
exactly the mixed-shift synthesis of its origin response. -/
theorem commuting_operator_classification (hd : ∀ i, 0 < d i)
    (T : Module.End ℤ (Coef d))
    (hT : ∀ m, Commute T (shiftEndo d m)) :
    T = synthesis d (T (delta d (origin d hd))) := by
  apply commuting_operator_ext d hd T _ hT
    (synthesis_commutes d (T (delta d (origin d hd))))
  exact (synthesis_origin d hd _).symm

/-- The entire displacement commutant is exactly the native coefficient
world. This classifies arbitrary linear symmetries, not only given shifts. -/
def commutantEquiv (hd : ∀ i, 0 < d i) :
    {T : Module.End ℤ (Coef d) // ∀ m, Commute T (shiftEndo d m)} ≃ Coef d where
  toFun T := T.val (delta d (origin d hd))
  invFun g := ⟨synthesis d g, synthesis_commutes d g⟩
  left_inv T := by
    apply Subtype.ext
    exact (commuting_operator_classification d hd T.val T.property).symm
  right_inv g := synthesis_origin d hd g

/-- Multi-axis complementary cell, with every depth supplied by the world. -/
def dual (c : Cell d) : Cell d :=
  fun i => ⟨d i - 1 - (c i).val, by have := (c i).isLt; omega⟩

@[simp] theorem dual_involutive (c : Cell d) : dual d (dual d c) = c := by
  funext i
  apply Fin.ext
  have := (c i).isLt
  simp only [dual]
  omega

def pairing (f g : Coef d) : ℤ := ∑ c : Cell d, f c * g (dual d c)

/-- Complementary probing extracts an arbitrary coordinate exactly. -/
theorem pairing_extract (f : Coef d) (a : Cell d) :
    pairing d f (delta d (dual d a)) = f a := by
  classical
  unfold pairing
  rw [Finset.sum_eq_single a]
  · simp [delta]
  · intro b hb hba
    have hn : dual d b ≠ dual d a := by
      intro h
      apply hba
      simpa using congrArg (dual d) h
    simp [delta, hn]
  · simp

/-- Integral nondegeneracy in arbitrary finite dimension and arbitrary depths. -/
theorem pairing_nondegenerate (f : Coef d)
    (h : ∀ g, pairing d f g = 0) : f = 0 := by
  funext a
  simpa only [pairing_extract, Pi.zero_apply] using h (delta d (dual d a))

/-- Degree reflection around the dimension-derived top degree. -/
theorem degree_dual (c : Cell d) :
    (∑ i, (dual d c i).val) + (∑ i, (c i).val) = ∑ i, (d i - 1) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have := (c i).isLt
  simp only [dual]
  omega
end Finite

/-! ## Rational transport and generation by duality

These are the same native displacements and complementary cells with rational
amplitudes. Rational coefficients allow a nonzero extracted amplitude to be
normalized, which is essential when applying the native laws to Hodge classes.
-/

abbrev RationalCoef := Cell d → ℚ

def rationalDelta (a : Cell d) : RationalCoef d := fun c => (delta d a c : ℚ)

def rationalShift (m : I → ℕ) (f : RationalCoef d) : RationalCoef d := by
  classical
  exact fun c => if h : ∀ i, m i ≤ (c i).val then
    f (fun i => ⟨(c i).val - m i, lt_of_le_of_lt (Nat.sub_le _ _) (c i).isLt⟩)
  else 0

def rationalMirror (f : RationalCoef d) : RationalCoef d := fun c => f (dual d c)

/-- Rational transport agrees exactly with the existing integral transport. -/
theorem rationalShift_cast (m : I → ℕ) (f : Coef d) :
    rationalShift d m (fun c => (f c : ℚ)) = fun c => (shift d m f c : ℚ) := by
  classical
  funext c
  by_cases h : ∀ i, m i ≤ (c i).val <;> simp [rationalShift, shift, h]

theorem rationalShift_smul (m : I → ℕ) (q : ℚ) (f : RationalCoef d) :
    rationalShift d m (q • f) = q • rationalShift d m f := by
  classical
  funext c
  by_cases h : ∀ i, m i ≤ (c i).val <;> simp [rationalShift, h]

/-- The original GST origin-orbit theorem supplies rational basis generation. -/
theorem rationalShift_origin (hd : ∀ i, 0 < d i) (a : Cell d) :
    rationalShift d (fun i => (a i).val) (rationalDelta d (origin d hd)) =
      rationalDelta d a := by
  unfold rationalDelta
  rw [rationalShift_cast, shift_origin]

theorem rationalMirror_smul (q : ℚ) (f : RationalCoef d) :
    rationalMirror d (q • f) = q • rationalMirror d f := rfl

theorem rationalMirror_delta (a : Cell d) :
    rationalMirror d (rationalDelta d a) = rationalDelta d (dual d a) := by
  classical
  funext c
  have he : dual d c = a ↔ c = dual d a := by
    constructor
    · intro h
      simpa using congrArg (dual d) h
    · rintro rfl
      exact dual_involutive d a
  simp [rationalMirror, rationalDelta, delta, he]

/-- Moving to the top corner extracts exactly the origin amplitude. -/
theorem rationalShift_top (hd : ∀ i, 0 < d i) (f : RationalCoef d) :
    rationalShift d (fun i => d i - 1) f =
      f (origin d hd) • rationalDelta d (dual d (origin d hd)) := by
  classical
  funext c
  by_cases hc : c = dual d (origin d hd)
  · subst c
    have hm : ∀ i, d i - 1 ≤ (dual d (origin d hd) i).val := by
      intro i
      simp [dual, origin]
    have he : (fun i => (⟨(dual d (origin d hd) i).val - (d i - 1),
        lt_of_le_of_lt (Nat.sub_le _ _) (dual d (origin d hd) i).isLt⟩ : Fin (d i))) =
        origin d hd := by
      funext i
      apply Fin.ext
      simp [dual, origin]
    simp [rationalShift, hm, he, rationalDelta, delta]
  · have hm : ¬ ∀ i, d i - 1 ≤ (c i).val := by
      intro h
      apply hc
      funext i
      apply Fin.ext
      have := h i
      have := (c i).isLt
      simp only [dual, origin]
      omega
    simp [rationalShift, hm, rationalDelta, delta, hc]

/-- Complementary displacement reads any chosen amplitude at the top corner. -/
theorem rationalShift_dual_at_top (hd : ∀ i, 0 < d i)
    (a : Cell d) (f : RationalCoef d) :
    rationalShift d (fun i => (dual d a i).val) f (dual d (origin d hd)) = f a := by
  classical
  have hm : ∀ i, (dual d a i).val ≤ (dual d (origin d hd) i).val := by
    intro i
    simp only [dual, origin]
    omega
  simp only [rationalShift, dif_pos hm]
  congr 1
  funext i
  apply Fin.ext
  have := (a i).isLt
  simp only [dual, origin]
  omega

/-- Four native operations extract a selected coordinate into the origin.
This is an explicit word in transport and complementary reflection. -/
theorem rational_origin_extraction (hd : ∀ i, 0 < d i)
    (a : Cell d) (f : RationalCoef d) :
    rationalMirror d (rationalShift d (fun i => d i - 1)
      (rationalMirror d (rationalShift d (fun i => (dual d a i).val) f))) =
      f a • rationalDelta d (origin d hd) := by
  rw [rationalShift_top d hd, rationalMirror_smul, rationalMirror_delta, dual_involutive]
  congr 1
  exact rationalShift_dual_at_top d hd a f

theorem rational_delta_expansion [Fintype I] (f : RationalCoef d) :
    (∑ a : Cell d, f a • rationalDelta d a) = f := by
  classical
  funext c
  simp [rationalDelta, delta, Finset.sum_apply]

/-- Joint native transport and duality are irreducible over rational
amplitudes: a stable subspace containing one nonzero world contains every
world. There is no bound on the number of finite axes or their depths. -/
theorem rational_transport_duality_generation [Fintype I]
    (W : Submodule ℚ (RationalCoef d))
    (hshift : ∀ m f, f ∈ W → rationalShift d m f ∈ W)
    (hmirror : ∀ f, f ∈ W → rationalMirror d f ∈ W)
    (f : RationalCoef d) (hf : f ∈ W) (hne : f ≠ 0) : W = ⊤ := by
  classical
  have ha : ∃ a, f a ≠ 0 := by
    by_contra h
    apply hne
    funext a
    by_contra hfa
    exact h ⟨a, hfa⟩
  obtain ⟨a, hfa⟩ := ha
  have hd : ∀ i, 0 < d i := fun i => by have := (a i).isLt; omega
  have he := hmirror _ (hshift (fun i => d i - 1) _
    (hmirror _ (hshift (fun i => (dual d a i).val) f hf)))
  rw [rational_origin_extraction d hd a f] at he
  have h0 : rationalDelta d (origin d hd) ∈ W := by
    have hscale := W.smul_mem (f a)⁻¹ he
    simpa only [smul_smul, inv_mul_cancel₀ hfa, one_smul] using hscale
  have hb : ∀ b : Cell d, rationalDelta d b ∈ W := by
    intro b
    simpa only [rationalShift_origin] using hshift (fun i => (b i).val) _ h0
  apply top_unique
  intro g hg
  rw [← rational_delta_expansion d g]
  exact W.sum_mem (fun b _ => W.smul_mem (g b) (hb b))

/-- The rectangle is exactly the two-axis world, with carry then digit. -/
def rectangleEquiv (A B : ℕ) :
    GSTWorldCosmology.WorldCell A B ≃ Cell (I:=Fin 2) ![A, B] where
  toFun c := fun i => Fin.cases c.1 (fun j => Fin.cases c.2 (fun k => nomatch k) j) i
  invFun c := (c 0, c 1)
  left_inv c := rfl
  right_inv c := by
    funext i
    fin_cases i <;> rfl

#print axioms shift_add
#print axioms shift_boundary
#print axioms synthesis_injective
#print axioms commuting_operator_ext
#print axioms pairing_nondegenerate
#print axioms degree_dual
end GSTMultiAxisCosmology
