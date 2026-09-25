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

/-- Polynomial functional calculus of a rational linear endomorphism. -/
noncomputable def linearPolyEval
    (T : M →ₗ[ℚ] M) (P : Polynomial ℚ) : M →ₗ[ℚ] M :=
  Polynomial.eval₂ (LinearMap.id.codRestrict ⊤ (1 : M →ₗ[ℚ] M) (by simp)) T P

/-- More explicit pointwise recursion characterization of the polynomial
functional calculus.  GLM may normalize this definition against the pinned
Mathlib polynomial-evaluation API without changing the theorem interface. -/
def PolynomialStable
    (W : Submodule ℚ M)
    (T : M →ₗ[ℚ] M) : Prop :=
  ∀ (P : Polynomial ℚ) (x : M), x ∈ W → linearPolyEval T P x ∈ W

/-- Stability under T implies stability under all polynomials in T. -/
theorem polynomialStable_of_operatorStable
    (W : Submodule ℚ M)
    (T : M →ₗ[ℚ] M)
    (hT : ∀ x : M, x ∈ W → T x ∈ W) :
    PolynomialStable W T := by
  intro P
  refine Polynomial.induction_on' P ?add ?monomial
  · intro P Q hP hQ x hx
    simpa [linearPolyEval] using W.add_mem (hP x hx) (hQ x hx)
  · intro n a x hx
    induction n with
    | zero =>
        simpa [linearPolyEval] using W.smul_mem a hx
    | succ n ih =>
        have hTx := hT x hx
        -- Polynomial monomials act by repeated application of T.
        simpa [linearPolyEval, pow_succ] using ih (T x) hTx

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
  apply Finset.prod_ne_zero
  intro j hj
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  exact sub_ne_zero.mpr (S.eigenvalue_injective.ne hji)

/-- Polynomial action on one chosen eigenvector is scalar evaluation. -/
theorem linearPolyEval_eigenvector
    (P : Polynomial ℚ) (i : ι) :
    linearPolyEval S.observable P (S.vector i) =
      P.eval (S.eigenvalue i) • S.vector i := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      simp [linearPolyEval, hP, hQ, add_smul]
  | monomial n a =>
      induction n with
      | zero => simp [linearPolyEval]
      | succ n ih =>
          simp [linearPolyEval, pow_succ, ih, S.eigenvector,
            mul_smul]

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
  rw [map_sum]
  simp_rw [LinearMap.map_smul]
  rw [Finset.sum_eq_single i]
  · rw [S.isolator_selects_self]
    simp [mul_smul]
  · intro j hj hji
    rw [S.isolator_kills_other i j hji]
    simp
  · simp

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
  simpa [hscale] using hinv

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
  let F := S.toFiniteSpectralFamily
  have h := F.every_vector_mem_of_cyclic_seed
    (pointCycleClassSpan p (H.cycleClass p))
    S.atomic_stable a ha
  simpa [F, FiniteSpectralFamily.spectralCombination] using h hseed

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
  let alphaH : ClassicalHodgeFiber V H p := ⟨alpha,halpha⟩
  have hbasis : ∀ j : ClassicalHodgeBasisIndex V H p,
      (classicalHodgeBasis V H p j).1 ∈
        pointCycleClassSpan p (H.cycleClass p) := by
    intro j
    obtain ⟨i,rfl⟩ := hsurj j
    exact S.selected_basis_algebraic_of_cyclic_seed a ha hseed i
  have hreconstruct := (classicalHodgeBasis V H p).sum_repr alphaH
  rw [← hreconstruct]
  exact Submodule.sum_mem _ fun j hj =>
    Submodule.smul_mem _ _ (hbasis j)

#check ClassicalHodgeSpectralOperator
#check ClassicalHodgeSpectralOperator.toFiniteSpectralFamily
#check ClassicalHodgeSpectralOperator.selected_basis_algebraic_of_cyclic_seed
#check ClassicalHodgeSpectralOperator.weight_hodge_of_cyclic_spectral_generation

#print axioms FiniteSpectralFamily.every_vector_mem_of_cyclic_seed
#print axioms FiniteSpectralFamily.eq_top_of_cyclic_seed
#print axioms ClassicalHodgeSpectralOperator.selected_basis_algebraic_of_cyclic_seed
#print axioms ClassicalHodgeSpectralOperator.weight_hodge_of_cyclic_spectral_generation

end GSTClassicalHodgeCyclicSpectralGeneration
