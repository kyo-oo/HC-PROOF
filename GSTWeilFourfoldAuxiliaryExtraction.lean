import Mathlib

/-!
# Exact auxiliary-factor extraction for a Weil fourfold

This file verifies the rational arithmetic in the geometric construction
written in `research/records/20261018-weil-fourfold-auxiliary-extraction.md`.
It does NOT construct abelian varieties, Chow intersections, Betti cycle
classes, or the secant-sheaf cycle on the auxiliary split sixfold.

Those geometric operations and the split-sixfold Weil-plane theorem are
external inputs to the manuscript, not axioms asserted by this file.
In particular, no nonzero geometric cycle is manufactured from coordinates.

The coefficients below represent a tensor in a product of two rational
Weil planes. Its two conjugate determinant summands satisfy the displayed
balance equations. Contraction with Delta - F1 - F2 is injective on this
two-dimensional tensor sector. A second result verifies that the actual
fourth-power character, rather than multiplication by u alone, generates
two independent directions from a nonzero extracted vector.
-/

set_option maxHeartbeats 1000000

namespace GSTWeilFourfoldAuxiliaryExtraction

/-- Coordinates in the ordered divisor list (Gamma_u, F1, F2, Delta). -/
abbrev AuxiliaryDivisor := Fin 4 → ℚ

/-- Intersection numbers for an elliptic curve with u² = -d.
The geometric identification of this formula is external. -/
def auxiliaryIntersection (d : ℚ) (v w : AuxiliaryDivisor) : ℚ :=
  d * (v 0 * w 1 + v 1 * w 0) +
  (v 0 * w 2 + v 2 * w 0) +
  (d + 1) * (v 0 * w 3 + v 3 * w 0) +
  (v 1 * w 2 + v 2 * w 1) +
  (v 1 * w 3 + v 3 * w 1) +
  (v 2 * w 3 + v 3 * w 2)

def graphDifference (i : Fin 4) : ℚ :=
  match i.val with
  | 0 => 0
  | 1 => -1
  | 2 => -1
  | _ => 1

def imaginaryGraphDifference (d : ℚ) (i : Fin 4) : ℚ :=
  match i.val with
  | 0 => 1
  | 1 => -1
  | 2 => -d
  | _ => 0

def firstFiber (i : Fin 4) : ℚ := if i.val = 1 then 1 else 0
def secondFiber (i : Fin 4) : ℚ := if i.val = 2 then 1 else 0

theorem auxiliary_graph_pairings (d : ℚ) :
    auxiliaryIntersection d graphDifference graphDifference = -2 ∧
    auxiliaryIntersection d graphDifference (imaginaryGraphDifference d) = 0 ∧
    auxiliaryIntersection d (imaginaryGraphDifference d)
      (imaginaryGraphDifference d) = -2 * d := by
  refine ⟨?_, ?_, ?_⟩
  <;> norm_num [auxiliaryIntersection, graphDifference, imaginaryGraphDifference]
  <;> ring

theorem graph_difference_kills_product_polarization (d a b : ℚ) :
    auxiliaryIntersection d graphDifference
      (fun i => a * firstFiber i + b * secondFiber i) = 0 := by
  norm_num [auxiliaryIntersection, graphDifference, firstFiber, secondFiber]
  <;> ring

/-- Coefficients in (A0 D0, A0 Du, A1 D0, A1 Du). -/
@[ext] structure TensorCoefficients where
  aa : ℚ
  ab : ℚ
  ba : ℚ
  bb : ℚ

def zeroCoefficients : TensorCoefficients := ⟨0, 0, 0, 0⟩

/-- Equalizer of J_A tensor 1 and 1 tensor J_B, where J² = -d. -/
def balanced (d : ℚ) (v : TensorCoefficients) : Prop :=
  v.ba = v.ab ∧ v.aa = -d * v.bb

def determinantTensor (d x y : ℚ) : TensorCoefficients :=
  ⟨x, y, y, -x / d⟩

def contractGraph (v : TensorCoefficients) : ℚ × ℚ :=
  (-2 * v.aa, -2 * v.ba)

theorem determinant_tensor_balanced (d x y : ℚ) (hd : d ≠ 0) :
    balanced d (determinantTensor d x y) := by
  constructor
  · rfl
  · dsimp [determinantTensor]
    field_simp [hd]

theorem contraction_formula (d x y : ℚ) :
    contractGraph (determinantTensor d x y) = (-2 * x, -2 * y) := rfl

/-- The graph detector loses no nonzero tensor in the Weil sector.
This is a universal rational calculation, not a source-existence theorem. -/
theorem contraction_injective_on_balanced (d : ℚ) (hd : d ≠ 0)
    (v : TensorCoefficients) (hv : balanced d v)
    (hzero : contractGraph v = (0, 0)) : v = zeroCoefficients := by
  have ha := congrArg Prod.fst hzero
  have hb := congrArg Prod.snd hzero
  change -2 * v.aa = 0 at ha
  change -2 * v.ba = 0 at hb
  have haa : v.aa = 0 := by linarith
  have hba : v.ba = 0 := by linarith
  have hab : v.ab = 0 := by rw [← hv.1, hba]
  have hmul : d * v.bb = 0 := by linarith [hv.2]
  have hbb : v.bb = 0 := (mul_eq_zero.mp hmul).resolve_left hd
  exact TensorCoefficients.ext haa hab hba hbb

theorem contraction_nonzero (d : ℚ) (hd : d ≠ 0)
    (v : TensorCoefficients) (hv : balanced d v)
    (hne : v ≠ zeroCoefficients) : contractGraph v ≠ (0, 0) := by
  intro hzero
  exact hne (contraction_injective_on_balanced d hd v hv hzero)

/-- Determinant after padding a (2,2) Hermitian form by (+t,-1/(delta*t)). -/
theorem padded_determinant (delta t : ℚ) (hdelta : delta ≠ 0) (ht : t ≠ 0) :
    delta * t * (-1 / (delta * t)) = -1 := by
  field_simp [hdelta, ht]

def realFourthPower (d m : ℚ) : ℚ := m ^ 4 - 6 * m ^ 2 * d + d ^ 2
def imaginaryFourthPower (d m : ℚ) : ℚ := 4 * m * (m ^ 2 - d)

/-- Matrix of pullback by m+u on the degree-four Weil plane, u²=-d. -/
def fourthPowerAction (d m : ℚ) (v : ℚ × ℚ) : ℚ × ℚ :=
  (realFourthPower d m * v.1 - d * imaginaryFourthPower d m * v.2,
   imaginaryFourthPower d m * v.1 + realFourthPower d m * v.2)

def planeDeterminant (v w : ℚ × ℚ) : ℚ := v.1 * w.2 - v.2 * w.1

theorem fourth_power_orbit_determinant (d m : ℚ) (v : ℚ × ℚ) :
    planeDeterminant v (fourthPowerAction d m v) =
      imaginaryFourthPower d m * (v.1 ^ 2 + d * v.2 ^ 2) := by
  dsimp [planeDeterminant, fourthPowerAction]
  ring

theorem imaginary_fourth_power_positive (d : ℚ) (hd : 0 < d) :
    0 < imaginaryFourthPower d (d + 1) := by
  have hm : 0 < d + 1 := by linarith
  have hq : 0 < (d + 1) ^ 2 - d := by nlinarith [sq_nonneg d]
  dsimp [imaginaryFourthPower]
  positivity

theorem quadratic_norm_positive (d : ℚ) (hd : 0 < d)
    (v : ℚ × ℚ) (hv : v ≠ (0, 0)) : 0 < v.1 ^ 2 + d * v.2 ^ 2 := by
  by_cases hx : v.1 = 0
  · have hy : v.2 ≠ 0 := by
      intro hy
      exact hv (Prod.ext hx hy)
    have hy2 : 0 < v.2 ^ 2 := sq_pos_of_ne_zero hy
    rw [hx]
    nlinarith
  · have hx2 : 0 < v.1 ^ 2 := sq_pos_of_ne_zero hx
    have hy2 : 0 ≤ d * v.2 ^ 2 := mul_nonneg hd.le (sq_nonneg _)
    linarith

/-- A nonzero extracted rational vector and its (d+1+u)-pullback are independent. -/
theorem extracted_fourth_power_orbit_has_rank_two (d : ℚ) (hd : 0 < d)
    (v : ℚ × ℚ) (hv : v ≠ (0, 0)) :
    0 < planeDeterminant v (fourthPowerAction d (d + 1) v) := by
  rw [fourth_power_orbit_determinant]
  exact mul_pos (imaginary_fourth_power_positive d hd)
    (quadratic_norm_positive d hd v hv)

#print axioms auxiliary_graph_pairings
#print axioms graph_difference_kills_product_polarization
#print axioms determinant_tensor_balanced
#print axioms contraction_injective_on_balanced
#print axioms contraction_nonzero
#print axioms padded_determinant
#print axioms fourth_power_orbit_determinant
#print axioms extracted_fourth_power_orbit_has_rank_two

/-! ## Constructive vanishing for the elliptic-star secant seed

This is the first section of the external source construction, rather
than an assumption that a nonzero sixfold cycle has already been supplied.
Four marks with at most two in every projective coordinate fiber force
a trilinear section vanishing on their three axes to be zero.

The proof works over every field. Either two marks differ in all three
coordinates, or the four marks have a tetrahedral arrangement. Basis
extensionality then kills all eight coefficients. No matrix-pencil
classification or assumed evaluation rank is used.
-/

section SecantSeed

variable {K : Type*} [Field K]
variable {V₁ V₂ V₃ : Type*}
variable [AddCommGroup V₁] [Module K V₁] [FiniteDimensional K V₁]
variable [AddCommGroup V₂] [Module K V₂] [FiniteDimensional K V₂]
variable [AddCommGroup V₃] [Module K V₃] [FiniteDimensional K V₃]

abbrev SeedTrilinear := V₁ →ₗ[K] V₂ →ₗ[K] V₃ →ₗ[K] K

/-- Vanishing along all three axes through a projective mark. -/
def seedSingularAt (T : SeedTrilinear (K := K) (V₁ := V₁) (V₂ := V₂) (V₃ := V₃))
    (x : Projectivization K V₁) (y : Projectivization K V₂)
    (z : Projectivization K V₃) : Prop :=
  (∀ a, T a y.rep z.rep = 0) ∧
  (∀ b, T x.rep b z.rep = 0) ∧
  (∀ c, T x.rep y.rep c = 0)

/-- Each coordinate fiber contains at most two indices, counting repeats. -/
def seedFiberAtMostTwo {I P : Type*} (f : I → P) : Prop :=
  ∀ a b c, f a = f b → f a = f c → a = b ∨ a = c ∨ b = c

noncomputable def seedProjectivePairBasis
    {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (hW : Module.finrank K W = 2)
    (a b : Projectivization K W) (hab : a ≠ b) : Module.Basis (Fin 2) K W :=
  basisOfLinearIndependentOfCardEqFinrank
    ((Projectivization.linearIndependent_pair_iff_ne).2 hab)
    (by simpa using hW.symm)

@[simp] theorem seedProjectivePairBasis_zero
    {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (hW : Module.finrank K W = 2)
    (a b : Projectivization K W) (hab : a ≠ b) :
    seedProjectivePairBasis hW a b hab 0 = a.rep := by
  simp [seedProjectivePairBasis]

@[simp] theorem seedProjectivePairBasis_one
    {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (hW : Module.finrank K W = 2)
    (a b : Projectivization K W) (hab : a ≠ b) :
    seedProjectivePairBasis hW a b hab 1 = b.rep := by
  simp [seedProjectivePairBasis]

theorem seedTrilinear_zero_of_basis_corners
    (T : SeedTrilinear (K := K) (V₁ := V₁) (V₂ := V₂) (V₃ := V₃))
    (bx : Module.Basis (Fin 2) K V₁) (byy : Module.Basis (Fin 2) K V₂)
    (bz : Module.Basis (Fin 2) K V₃)
    (h : ∀ i j k, T (bx i) (byy j) (bz k) = 0) : T = 0 := by
  apply bx.ext
  intro i
  apply byy.ext
  intro j
  apply bz.ext
  intro k
  exact h i j k

theorem seedTrilinear_zero_of_separated_pair
    (T : SeedTrilinear (K := K) (V₁ := V₁) (V₂ := V₂) (V₃ := V₃))
    (h₁ : Module.finrank K V₁ = 2) (h₂ : Module.finrank K V₂ = 2)
    (h₃ : Module.finrank K V₃ = 2)
    (x₀ x₁ : Projectivization K V₁) (y₀ y₁ : Projectivization K V₂)
    (z₀ z₁ : Projectivization K V₃)
    (hx : x₀ ≠ x₁) (hy : y₀ ≠ y₁) (hz : z₀ ≠ z₁)
    (hs₀ : seedSingularAt T x₀ y₀ z₀)
    (hs₁ : seedSingularAt T x₁ y₁ z₁) : T = 0 := by
  apply seedTrilinear_zero_of_basis_corners T
    (seedProjectivePairBasis h₁ x₀ x₁ hx)
    (seedProjectivePairBasis h₂ y₀ y₁ hy)
    (seedProjectivePairBasis h₃ z₀ z₁ hz)
  intro i j k
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals simp only [seedProjectivePairBasis_zero, seedProjectivePairBasis_one]
  all_goals first
    | exact hs₀.1 _
    | exact hs₀.2.1 _
    | exact hs₀.2.2 _
    | exact hs₁.1 _
    | exact hs₁.2.1 _
    | exact hs₁.2.2 _

theorem seedTrilinear_zero_of_tetrahedron
    (T : SeedTrilinear (K := K) (V₁ := V₁) (V₂ := V₂) (V₃ := V₃))
    (h₁ : Module.finrank K V₁ = 2) (h₂ : Module.finrank K V₂ = 2)
    (h₃ : Module.finrank K V₃ = 2)
    (x₀ x₁ : Projectivization K V₁) (y₀ y₁ : Projectivization K V₂)
    (z₀ z₁ : Projectivization K V₃)
    (hx : x₀ ≠ x₁) (hy : y₀ ≠ y₁) (hz : z₀ ≠ z₁)
    (hs₀ : seedSingularAt T x₀ y₀ z₀)
    (hs₁ : seedSingularAt T x₀ y₁ z₁)
    (hs₂ : seedSingularAt T x₁ y₀ z₁)
    (hs₃ : seedSingularAt T x₁ y₁ z₀) : T = 0 := by
  apply seedTrilinear_zero_of_basis_corners T
    (seedProjectivePairBasis h₁ x₀ x₁ hx)
    (seedProjectivePairBasis h₂ y₀ y₁ hy)
    (seedProjectivePairBasis h₃ z₀ z₁ hz)
  intro i j k
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals simp only [seedProjectivePairBasis_zero, seedProjectivePairBasis_one]
  all_goals first
    | exact hs₀.1 _
    | exact hs₀.2.1 _
    | exact hs₀.2.2 _
    | exact hs₁.1 _
    | exact hs₁.2.1 _
    | exact hs₁.2.2 _
    | exact hs₂.1 _
    | exact hs₂.2.1 _
    | exact hs₂.2.2 _
    | exact hs₃.1 _
    | exact hs₃.2.1 _
    | exact hs₃.2.2 _

/-- The combinatorial step of the four-mark seed construction.
If no pair is separated, the three neighbors of 0 match it in three
different coordinates. The remaining three edges are then forced. -/
theorem seedFourMarks_match_neighbors
    {P Q R : Type*} (x : Fin 4 → P) (y : Fin 4 → Q) (z : Fin 4 → R)
    (hx : seedFiberAtMostTwo x) (hy : seedFiberAtMostTwo y)
    (hz : seedFiberAtMostTwo z)
    (hAgree : ∀ a b, x a = x b ∨ y a = y b ∨ z a = z b) :
    ∃ a b c : Fin 4, a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      x 0 = x a ∧ y 0 = y b ∧ z 0 = z c := by
  have hx12 : ¬ (x 0 = x 1 ∧ x 0 = x 2) := by
    rintro ⟨h, h'⟩; have := hx 0 1 2 h h'; norm_num at this
  have hx13 : ¬ (x 0 = x 1 ∧ x 0 = x 3) := by
    rintro ⟨h, h'⟩; have := hx 0 1 3 h h'; norm_num at this
  have hx23 : ¬ (x 0 = x 2 ∧ x 0 = x 3) := by
    rintro ⟨h, h'⟩; have := hx 0 2 3 h h'; norm_num at this
  have hy12 : ¬ (y 0 = y 1 ∧ y 0 = y 2) := by
    rintro ⟨h, h'⟩; have := hy 0 1 2 h h'; norm_num at this
  have hy13 : ¬ (y 0 = y 1 ∧ y 0 = y 3) := by
    rintro ⟨h, h'⟩; have := hy 0 1 3 h h'; norm_num at this
  have hy23 : ¬ (y 0 = y 2 ∧ y 0 = y 3) := by
    rintro ⟨h, h'⟩; have := hy 0 2 3 h h'; norm_num at this
  have hz12 : ¬ (z 0 = z 1 ∧ z 0 = z 2) := by
    rintro ⟨h, h'⟩; have := hz 0 1 2 h h'; norm_num at this
  have hz13 : ¬ (z 0 = z 1 ∧ z 0 = z 3) := by
    rintro ⟨h, h'⟩; have := hz 0 1 3 h h'; norm_num at this
  have hz23 : ¬ (z 0 = z 2 ∧ z 0 = z 3) := by
    rintro ⟨h, h'⟩; have := hz 0 2 3 h h'; norm_num at this
  have h01 := hAgree 0 1
  have h02 := hAgree 0 2
  have h03 := hAgree 0 3
  have hmatch :
      (x 0 = x 1 ∧ y 0 = y 2 ∧ z 0 = z 3) ∨
      (x 0 = x 1 ∧ y 0 = y 3 ∧ z 0 = z 2) ∨
      (x 0 = x 2 ∧ y 0 = y 1 ∧ z 0 = z 3) ∨
      (x 0 = x 2 ∧ y 0 = y 3 ∧ z 0 = z 1) ∨
      (x 0 = x 3 ∧ y 0 = y 1 ∧ z 0 = z 2) ∨
      (x 0 = x 3 ∧ y 0 = y 2 ∧ z 0 = z 1) := by tauto
  rcases hmatch with h | h | h | h | h | h
  · exact ⟨1, 2, 3, by decide, by decide, by decide,
      by decide, by decide, by decide, h⟩
  · exact ⟨1, 3, 2, by decide, by decide, by decide,
      by decide, by decide, by decide, h⟩
  · exact ⟨2, 1, 3, by decide, by decide, by decide,
      by decide, by decide, by decide, h⟩
  · exact ⟨2, 3, 1, by decide, by decide, by decide,
      by decide, by decide, by decide, h⟩
  · exact ⟨3, 1, 2, by decide, by decide, by decide,
      by decide, by decide, by decide, h⟩
  · exact ⟨3, 2, 1, by decide, by decide, by decide,
      by decide, by decide, by decide, h⟩

theorem seedFourMarks_opposite_ne
    {I P : Type*} (f : I → P) (hf : seedFiberAtMostTwo f)
    (a b c : I) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (heq : f a = f b) : f a ≠ f c := by
  intro h
  rcases hf a b c heq h with h' | h' | h'
  · exact hab h'
  · exact hac h'
  · exact hbc h'

/-- The universal vanishing needed for the elliptic-star geometric seed.
It proves the four-mark assertion over ANY field, with no rank input,
no pre-existing algebraic cycle, and no tensor classification. -/
theorem secantSeed_four_projective_marks_force_zero
    (T : SeedTrilinear (K := K) (V₁ := V₁) (V₂ := V₂) (V₃ := V₃))
    (h₁ : Module.finrank K V₁ = 2) (h₂ : Module.finrank K V₂ = 2)
    (h₃ : Module.finrank K V₃ = 2)
    (x : Fin 4 → Projectivization K V₁)
    (y : Fin 4 → Projectivization K V₂)
    (z : Fin 4 → Projectivization K V₃)
    (hx : seedFiberAtMostTwo x) (hy : seedFiberAtMostTwo y)
    (hz : seedFiberAtMostTwo z)
    (hs : ∀ i, seedSingularAt T (x i) (y i) (z i)) : T = 0 := by
  classical
  by_cases hsep : ∃ a b, x a ≠ x b ∧ y a ≠ y b ∧ z a ≠ z b
  · rcases hsep with ⟨a, b, hxa, hya, hza⟩
    exact seedTrilinear_zero_of_separated_pair T h₁ h₂ h₃
      (x a) (x b) (y a) (y b) (z a) (z b) hxa hya hza (hs a) (hs b)
  · have hAgree : ∀ a b, x a = x b ∨ y a = y b ∨ z a = z b := by
      intro a b
      by_contra h
      apply hsep
      exact ⟨a, b, by tauto⟩
    rcases seedFourMarks_match_neighbors x y z hx hy hz hAgree with
      ⟨a, b, c, ha, hb, hc, hab, hac, hbc, hxa, hyb, hzc⟩
    have hxb : x 0 ≠ x b :=
      seedFourMarks_opposite_ne x hx 0 a b ha.symm hb.symm hab hxa
    have hxc : x 0 ≠ x c :=
      seedFourMarks_opposite_ne x hx 0 a c ha.symm hc.symm hac hxa
    have hya : y 0 ≠ y a :=
      seedFourMarks_opposite_ne y hy 0 b a hb.symm ha.symm hab.symm hyb
    have hyc : y 0 ≠ y c :=
      seedFourMarks_opposite_ne y hy 0 b c hb.symm hc.symm hbc hyb
    have hza : z 0 ≠ z a :=
      seedFourMarks_opposite_ne z hz 0 c a hc.symm ha.symm hac.symm hzc
    have hzb : z 0 ≠ z b :=
      seedFourMarks_opposite_ne z hz 0 c b hc.symm hb.symm hbc.symm hzc
    have hxbc : x b = x c := by
      rcases hAgree b c with h | h | h
      · exact h
      · exact (hyc (hyb.trans h)).elim
      · exact (hzb (hzc.trans h.symm)).elim
    have hyac : y a = y c := by
      rcases hAgree a c with h | h | h
      · exact (hxc (hxa.trans h)).elim
      · exact h
      · exact (hza (hzc.trans h.symm)).elim
    have hzab : z a = z b := by
      rcases hAgree a b with h | h | h
      · exact (hxb (hxa.trans h)).elim
      · exact (hya (hyb.trans h.symm)).elim
      · exact h
    apply seedTrilinear_zero_of_tetrahedron T h₁ h₂ h₃
      (x 0) (x b) (y 0) (y a) (z 0) (z a) hxb hya hza (hs 0)
    · simpa only [← hxa] using hs a
    · simpa only [← hyb, ← hzab] using hs b
    · simpa only [← hxbc, ← hyac, ← hzc] using hs c

#print axioms seedTrilinear_zero_of_separated_pair
#print axioms seedTrilinear_zero_of_tetrahedron
#print axioms seedFourMarks_match_neighbors
#print axioms secantSeed_four_projective_marks_force_zero

end SecantSeed

end GSTWeilFourfoldAuxiliaryExtraction
