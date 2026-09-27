import GSTClassicalHodgeSingleSheetCrown
import GSTWorldRecoordinationGroupoid

/-!
# GST CLASSICAL HODGE — CYCLIC SPECTRAL GENERATION

The microscopic single-sheet reduction can be compressed further.

Suppose a finite family of Hodge directions is diagonal for one rational
linear observable T with pairwise distinct eigenvalues.  If the algebraic
cycle-class submodule is stable under T, then it is stable under every
polynomial in T.  A single algebraic vector having nonzero coordinate in
every eigendirection is therefore cyclic: Lagrange interpolation extracts
each individual eigendirection by a polynomial in T.

Consequently one algebraic cyclic seed plus one algebraicity-preserving
spectral observable generates the whole finite Hodge family.  This is the
linear-algebraic engine behind the invariant GST code-sector projectors.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators

namespace GSTClassicalHodgeCyclicSpectralGeneration

universe u

variable {M : Type u} [AddCommGroup M] [Module ℚ M]

/-- The canonical scalar ring homomorphism into the endomorphism ring. -/
noncomputable def scalarRingHom : ℚ →+* (Module.End ℚ M) where
  toFun q := q • LinearMap.id
  map_one' := by
    show (1 : ℚ) • (LinearMap.id : Module.End ℚ M) = 1
    exact one_smul ℚ LinearMap.id
  map_mul' q r := by
    apply LinearMap.ext
    intro x
    show (q * r) • x = q • r • x
    exact (smul_smul q r x).symm
  map_zero' := by
    show (0 : ℚ) • (LinearMap.id : Module.End ℚ M) = 0
    exact zero_smul ℚ LinearMap.id
  map_add' q r := by
    apply LinearMap.ext
    intro x
    show (q + r) • x = q • x + r • x
    exact add_smul q r x

/-- Polynomial functional calculus of a rational linear endomorphism,
assembled from Mathlib's `Polynomial.eval₂` over the canonical scalar
ring homomorphism into the endomorphism ring. -/
noncomputable def linearPolyEval
    (T : M →ₗ[ℚ] M) (P : Polynomial ℚ) : M →ₗ[ℚ] M :=
  Polynomial.eval₂ scalarRingHom T P

/-- Monomials act by scalar multiples of operator powers. -/
theorem linearPolyEval_monomial
    (T : M →ₗ[ℚ] M) (n : ℕ) (a : ℚ) (x : M) :
    linearPolyEval T (Polynomial.monomial n a) x = a • (T ^ n) x := by
  simp only [linearPolyEval, Polynomial.eval₂_monomial]
  rfl

/-- More explicit pointwise recursion characterization of the polynomial
functional calculus.  GLM may normalize this definition against the pinned
Mathlib polynomial-evaluation API without changing the theorem interface. -/
def PolynomialStable
    (W : Submodule ℚ M)
    (T : M →ₗ[ℚ] M) : Prop :=
  ∀ (P : Polynomial ℚ) (x : M), x ∈ W → linearPolyEval T P x ∈ W

/-- Stability under T implies stability under all operator powers. -/
theorem pow_mem_of_mem
    (W : Submodule ℚ M) (T : M →ₗ[ℚ] M)
    (hT : ∀ x : M, x ∈ W → T x ∈ W) (n : ℕ) :
    ∀ x : M, x ∈ W → (T ^ n) x ∈ W := by
  induction n with
  | zero =>
      intro x hx
      simpa using hx
  | succ n ih =>
      intro x hx
      rw [pow_succ]
      exact ih (T x) (hT x hx)

/-- Stability under T implies stability under all polynomials in T. -/
theorem polynomialStable_of_operatorStable
    (W : Submodule ℚ M)
    (T : M →ₗ[ℚ] M)
    (hT : ∀ x : M, x ∈ W → T x ∈ W) :
    PolynomialStable W T := by
  intro P x hx
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      have hsum : linearPolyEval T (P + Q) x
          = linearPolyEval T P x + linearPolyEval T Q x := by
        show (Polynomial.eval₂ scalarRingHom T (P + Q)) x
            = (Polynomial.eval₂ scalarRingHom T P) x
              + (Polynomial.eval₂ scalarRingHom T Q) x
        rw [Polynomial.eval₂_add]
        rfl
      rw [hsum]
      exact W.add_mem hP hQ
  | monomial n a =>
      rw [linearPolyEval_monomial]
      exact W.smul_mem a (pow_mem_of_mem W T hT n x hx)

/-- Finite spectral package: chosen directions are eigenvectors of one
observable with pairwise distinct eigenvalues. -/
structure FiniteSpectralFamily (ι : Type*) [Fintype ι] [DecidableEq ι]
    (M : Type u) [AddCommGroup M] [Module ℚ M] where
  observable : M →ₗ[ℚ] M
  vector : ι → M
  eigenvalue : ι → ℚ
  eigenvector : ∀ i, observable (vector i) = eigenvalue i • vector i
  eigenvalue_injective : Function.Injective eigenvalue

namespace FiniteSpectralFamily

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (S : FiniteSpectralFamily ι M)

/-- Unnormalized Lagrange polynomial isolating one chosen eigenvalue. -/
noncomputable def isolatorPolynomial (i : ι) : Polynomial ℚ :=
  ∏ j ∈ Finset.univ.erase i,
    (Polynomial.X - Polynomial.C (S.eigenvalue j))

/-- Nonzero normalization scalar of the isolating polynomial at its own
eigenvalue. -/
noncomputable def isolatorScale (i : ι) : ℚ :=
  (S.isolatorPolynomial i).eval (S.eigenvalue i)

/-- The isolator polynomial vanishes at every other eigenvalue. -/
theorem isolatorPolynomial_eval_other
    (i j : ι) (hji : j ≠ i) :
    (S.isolatorPolynomial i).eval (S.eigenvalue j) = 0 := by
  classical
  unfold isolatorPolynomial
  rw [Polynomial.eval_prod]
  apply Finset.prod_eq_zero
  · exact Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩
  · simp

/-- The normalization at the selected eigendirection is nonzero because all
eigenvalues are distinct. -/
theorem isolatorScale_ne_zero (i : ι) :
    S.isolatorScale i ≠ 0 := by
  classical
  unfold isolatorScale isolatorPolynomial
  rw [Polynomial.eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  exact sub_ne_zero.mpr (S.eigenvalue_injective.ne hji)

/-- Operator powers act on chosen eigenvectors by scalar powers. -/
theorem eigenvector_pow
    (n : ℕ) (i : ι) :
    (S.observable ^ n) (S.vector i) =
      (S.eigenvalue i ^ n) • S.vector i := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Module.End.mul_apply, S.eigenvector i,
        LinearMap.map_smul, ih, smul_smul, pow_succ]

/-- Polynomial action on one chosen eigenvector is scalar evaluation. -/
theorem linearPolyEval_eigenvector
    (P : Polynomial ℚ) (i : ι) :
    linearPolyEval S.observable P (S.vector i) =
      P.eval (S.eigenvalue i) • S.vector i := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      rw [hP, hQ]
      simp [Polynomial.eval_add, add_smul]
  | monomial n a =>
      rw [linearPolyEval_monomial, eigenvector_pow]
      simp [Polynomial.eval_monomial]

/-- The isolator kills every non-selected eigenvector. -/
theorem isolator_kills_other
    (i j : ι) (hji : j ≠ i) :
    linearPolyEval S.observable (S.isolatorPolynomial i) (S.vector j) = 0 := by
  rw [S.linearPolyEval_eigenvector]
  rw [S.isolatorPolynomial_eval_other i j hji]
  simp

/-- The isolator acts on its selected direction by the nonzero normalization
scalar. -/
theorem isolator_selects_self (i : ι) :
    linearPolyEval S.observable (S.isolatorPolynomial i) (S.vector i) =
      S.isolatorScale i • S.vector i := by
  exact S.linearPolyEval_eigenvector _ _

/-- A finite linear combination of the spectral directions. -/
def spectralCombination (a : ι → ℚ) : M :=
  ∑ i : ι, a i • S.vector i

/-- Applying the isolator to a finite spectral combination leaves exactly one
sheet. -/
theorem isolator_on_combination
    (a : ι → ℚ) (i : ι) :
    linearPolyEval S.observable (S.isolatorPolynomial i)
      (S.spectralCombination a) =
      (a i * S.isolatorScale i) • S.vector i := by
  classical
  simp only [spectralCombination]
  rw [map_sum]
  simp_rw [LinearMap.map_smul]
  rw [Finset.sum_eq_single i]
  · rw [S.isolator_selects_self]
    simp [mul_smul]
  · intro j hj hji
    rw [S.isolator_kills_other i j hji]
    simp
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- **CYCLIC SPECTRAL GENERATION.**

If a submodule is stable under the spectral observable and contains one
finite spectral seed with every coordinate nonzero, then it contains every
individual eigendirection. -/
theorem every_vector_mem_of_cyclic_seed
    (W : Submodule ℚ M)
    (hstable : ∀ x : M, x ∈ W → S.observable x ∈ W)
    (a : ι → ℚ)
    (ha : ∀ i, a i ≠ 0)
    (hseed : S.spectralCombination a ∈ W) :
    ∀ i : ι, S.vector i ∈ W := by
  intro i
  have hpoly :
      linearPolyEval S.observable (S.isolatorPolynomial i)
        (S.spectralCombination a) ∈ W :=
    polynomialStable_of_operatorStable W S.observable hstable
      (S.isolatorPolynomial i) (S.spectralCombination a) hseed
  rw [S.isolator_on_combination] at hpoly
  have hscale : a i * S.isolatorScale i ≠ 0 :=
    mul_ne_zero (ha i) (S.isolatorScale_ne_zero i)
  have hinv := W.smul_mem ((a i * S.isolatorScale i)⁻¹) hpoly
  rw [inv_smul_smul₀ hscale] at hinv
  exact hinv

/-- If the selected spectral directions span the ambient finite module, the
same hypotheses force the stable algebraic submodule to be all of M. -/
theorem eq_top_of_cyclic_seed
    (W : Submodule ℚ M)
    (hstable : ∀ x : M, x ∈ W → S.observable x ∈ W)
    (a : ι → ℚ)
    (ha : ∀ i, a i ≠ 0)
    (hseed : S.spectralCombination a ∈ W)
    (hspan : Submodule.span ℚ (Set.range S.vector) = ⊤) :
    W = ⊤ := by
  apply top_unique
  rw [← hspan]
  apply Submodule.span_le.mpr
  rintro x ⟨i,rfl⟩
  exact S.every_vector_mem_of_cyclic_seed W hstable a ha hseed i

end FiniteSpectralFamily

/-! ## Classical Hodge specialization interface -/

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicSpan

/-- A geometry-ready spectral realization of one finite family of genuine
classical Hodge basis directions at fixed codimension p.

Crucially, this package does NOT assume those basis directions are algebraic.
It supplies only an ambient observable, its diagonal action on the selected
Hodge directions, and stability of the already-existing algebraic atomic
span under that observable. -/
structure ClassicalHodgeSpectralOperator
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (ι : Type*) [Fintype ι] [DecidableEq ι] where
  basisIndex : ι → ClassicalHodgeBasisIndex V H p
  basisIndex_injective : Function.Injective basisIndex
  observable :
    RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
      RationalSingularCohomology H.analytification (2 * p)
  eigenvalue : ι → ℚ
  eigenvalue_injective : Function.Injective eigenvalue
  eigenvector : ∀ i,
    observable (classicalHodgeBasis V H p (basisIndex i)).1 =
      eigenvalue i • (classicalHodgeBasis V H p (basisIndex i)).1
  atomic_stable : ∀ x,
    x ∈ pointCycleClassSpan p (H.cycleClass p) →
      observable x ∈ pointCycleClassSpan p (H.cycleClass p)

namespace ClassicalHodgeSpectralOperator

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Forget the geometric labels and expose the underlying spectral family. -/
noncomputable def toFiniteSpectralFamily
    (S : ClassicalHodgeSpectralOperator V H p ι) :
    FiniteSpectralFamily ι
      (RationalSingularCohomology H.analytification (2 * p)) where
  observable := S.observable
  vector := fun i => (classicalHodgeBasis V H p (S.basisIndex i)).1
  eigenvalue := S.eigenvalue
  eigenvector := S.eigenvector
  eigenvalue_injective := S.eigenvalue_injective

/-- **ONE ALGEBRAIC CYCLIC SEED GENERATES EVERY SELECTED HODGE SHEET.**

No individual basis-cycle witnesses are assumed.  One algebraic linear
combination with nonzero coefficient in every selected eigendirection,
together with atomic-span invariance under the observable, forces every
selected genuine Hodge basis vector into the atomic algebraic span. -/
theorem selected_basis_algebraic_of_cyclic_seed
    (S : ClassicalHodgeSpectralOperator V H p ι)
    (a : ι → ℚ)
    (ha : ∀ i, a i ≠ 0)
    (hseed :
      ∑ i : ι,
        a i • (classicalHodgeBasis V H p (S.basisIndex i)).1 ∈
          pointCycleClassSpan p (H.cycleClass p)) :
    ∀ i : ι,
      (classicalHodgeBasis V H p (S.basisIndex i)).1 ∈
        pointCycleClassSpan p (H.cycleClass p) := by
  have hseed' : S.toFiniteSpectralFamily.spectralCombination a ∈
      pointCycleClassSpan p (H.cycleClass p) := hseed
  intro i
  exact S.toFiniteSpectralFamily.every_vector_mem_of_cyclic_seed
    (pointCycleClassSpan p (H.cycleClass p)) S.atomic_stable a ha hseed' i

/-- If a finite selected family exhausts the chosen Hodge basis index, then
one cyclic algebraic seed plus one stable spectral operator proves the full
weight-p Hodge inclusion. -/
theorem weight_hodge_of_cyclic_spectral_generation
    (S : ClassicalHodgeSpectralOperator V H p ι)
    (hsurj : Function.Surjective S.basisIndex)
    (a : ι → ℚ)
    (ha : ∀ i, a i ≠ 0)
    (hseed :
      ∑ i : ι,
        a i • (classicalHodgeBasis V H p (S.basisIndex i)).1 ∈
          pointCycleClassSpan p (H.cycleClass p)) :
    rationalHodgeSubspace (H.hodgeBigrading p) ≤
      pointCycleClassSpan p (H.cycleClass p) := by
  intro alpha halpha
  have hbasis : ∀ j : ClassicalHodgeBasisIndex V H p,
      (classicalHodgeBasis V H p j).1 ∈
        pointCycleClassSpan p (H.cycleClass p) := by
    intro j
    obtain ⟨i,rfl⟩ := hsurj j
    exact S.selected_basis_algebraic_of_cyclic_seed a ha hseed i
  have hle : Submodule.span ℚ
      (Set.range (classicalHodgeBasis V H p)) ≤
      (pointCycleClassSpan p (H.cycleClass p)).comap
        (ClassicalHodgeFiber V H p).subtype := by
    rw [Submodule.span_le]
    rintro x ⟨j, rfl⟩
    exact hbasis j
  have hmem : (⟨alpha, halpha⟩ : ClassicalHodgeFiber V H p) ∈
      Submodule.span ℚ (Set.range (classicalHodgeBasis V H p)) := by
    rw [(classicalHodgeBasis V H p).span_eq]
    exact Submodule.mem_top
  exact hle hmem

end ClassicalHodgeSpectralOperator

#check ClassicalHodgeSpectralOperator
#check ClassicalHodgeSpectralOperator.toFiniteSpectralFamily
#check ClassicalHodgeSpectralOperator.selected_basis_algebraic_of_cyclic_seed
#check ClassicalHodgeSpectralOperator.weight_hodge_of_cyclic_spectral_generation

#print axioms FiniteSpectralFamily.every_vector_mem_of_cyclic_seed
#print axioms FiniteSpectralFamily.eq_top_of_cyclic_seed
#print axioms ClassicalHodgeSpectralOperator.selected_basis_algebraic_of_cyclic_seed
#print axioms ClassicalHodgeSpectralOperator.weight_hodge_of_cyclic_spectral_generation

end GSTClassicalHodgeCyclicSpectralGeneration
