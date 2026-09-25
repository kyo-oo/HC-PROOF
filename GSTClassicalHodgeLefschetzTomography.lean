import GSTClassicalHodgeFiniteSupportChart
import GSTPureHodgeLefschetzKernel
import GSTLefschetzPoincareReciprocity

/-!
# GST CLASSICAL HODGE — FINITE LEFSCHETZ TOMOGRAPHY

Every concrete Hodge class has finite multiplicity support.  After coding that
support by `Fin N`, place the N live multiplicity directions on the diagonal
of the square N x N GST world.

The existing pure-Hodge Lefschetz kernel is triangular on this diagonal:
from source i to target j it is zero for j < i and, for i <= j, has exact
coefficient

  choose (2*(j-i)) (j-i).

The diagonal coefficient is choose 0 0 = 1.  Hence the full finite transform
is unit triangular and injective.  This gives an exact tomography theorem:
all finite multiplicity coordinates of a Hodge state are recoverable from its
Lefschetz moments.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open GSTProjectiveOverC
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeFiniteSupportChart
open GSTPureHodgeLefschetzKernel
open GSTWorldCosmology
open GSTWorldPoincareDuality
open GSTTruncatedWorldCohomologyRing

namespace GSTClassicalHodgeLefschetzTomography

/-- Rationalized exact diagonal Lefschetz kernel on a finite multiplicity
chart. -/
def multiplicityLefschetzKernel
    {N : Nat} (i j : Fin N) : ℚ :=
  if h : i.1 ≤ j.1 then
    (Nat.choose (2 * (j.1 - i.1)) (j.1 - i.1) : ℚ)
  else 0

@[simp]
theorem multiplicityLefschetzKernel_self
    {N : Nat} (i : Fin N) :
    multiplicityLefschetzKernel i i = 1 := by
  simp [multiplicityLefschetzKernel]

@[simp]
theorem multiplicityLefschetzKernel_zero_of_lt
    {N : Nat} (i j : Fin N) (hji : j.1 < i.1) :
    multiplicityLefschetzKernel i j = 0 := by
  simp [multiplicityLefschetzKernel, show ¬ i.1 ≤ j.1 by omega]

/-- The rational kernel is exactly the rationalization of the existing GST
pure-diagonal transition coefficient at its unique live time. -/
theorem multiplicityLefschetzKernel_eq_worldAct
    {N : Nat} (i j : Fin N) (hij : i.1 ≤ j.1) :
    multiplicityLefschetzKernel i j =
      (worldAct N N
        ((L N N)^(2 * pureWeightGap i j))
        (GSTWorldPoincareDuality.worldBasis (pureDiagonalState i))
        (pureDiagonalState j) : ℚ) := by
  rw [pure_diagonal_lefschetz_forward_exact i j hij]
  simp [multiplicityLefschetzKernel, hij, pureWeightGap]

/-- Exact finite Lefschetz tomography transform.  The q-th moment receives
contributions only from source coordinates i <= q. -/
def lefschetzTomography
    {N : Nat} (a : Fin N → ℚ) : Fin N → ℚ :=
  fun q => ∑ i : Fin N, multiplicityLefschetzKernel i q * a i

/-- The q-th tomography coordinate is its original q-coordinate plus terms
strictly below q. -/
theorem lefschetzTomography_triangular
    {N : Nat} (a : Fin N → ℚ) (q : Fin N) :
    lefschetzTomography a q =
      a q +
        ∑ i : Fin N with i.1 < q.1,
          multiplicityLefschetzKernel i q * a i := by
  classical
  unfold lefschetzTomography
  rw [Finset.sum_eq_add_sum_diff_singleton q]
  · rw [multiplicityLefschetzKernel_self, one_mul]
    apply congrArg (fun z : ℚ => a q + z)
    apply Finset.sum_subset
    · intro i hi
      simp only [Finset.mem_filter]
      constructor
      · exact Finset.mem_univ i
      · by_contra hnot
        have hge : q.1 ≤ i.1 := by omega
        have hne : i ≠ q := by
          intro heq
          subst i
          omega
        have hgt : q.1 < i.1 := lt_of_le_of_ne hge (by
          intro hval
          apply hne
          apply Fin.ext
          exact hval.symm)
        rw [multiplicityLefschetzKernel_zero_of_lt i q hgt]
        simp
    · intro i hiU hiNot
      simp only [Finset.mem_filter] at hiNot
      push_neg at hiNot
      have hqi : q.1 ≤ i.1 := by omega
      by_cases hiq : i = q
      · subst i
        simp at hiNot
      · have hgt : q.1 < i.1 := by
          omega
        rw [multiplicityLefschetzKernel_zero_of_lt i q hgt]
        simp
  · simp

/-- **UNIT-TRIANGULAR INJECTIVITY.**  Exact Lefschetz tomography loses no
finite multiplicity information. -/
theorem lefschetzTomography_injective
    {N : Nat} : Function.Injective (@lefschetzTomography N) := by
  intro a b hab
  funext q
  induction q using Fin.induction with
  | zero =>
      have hq := congrFun hab ⟨0, q.2⟩
      rw [lefschetzTomography_triangular,
          lefschetzTomography_triangular] at hq
      simpa using hq
  | succ q ih =>
      have hq := congrFun hab q.succ
      rw [lefschetzTomography_triangular,
          lefschetzTomography_triangular] at hq
      have hlower :
          (∑ i : Fin N with i.1 < q.succ.1,
            multiplicityLefschetzKernel i q.succ * a i) =
          ∑ i : Fin N with i.1 < q.succ.1,
            multiplicityLefschetzKernel i q.succ * b i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [ih i (by simpa using hi)]
      rw [hlower] at hq
      exact add_right_cancel hq

/-- Zero tomography is equivalent to a zero finite state. -/
theorem lefschetzTomography_eq_zero_iff
    {N : Nat} (a : Fin N → ℚ) :
    lefschetzTomography a = 0 ↔ a = 0 := by
  constructor
  · intro h
    apply lefschetzTomography_injective
    simpa using h
  · rintro rfl
    funext q
    simp [lefschetzTomography]

/-- Any nonzero finite multiplicity state has a nonzero exact Lefschetz
moment. -/
theorem exists_nonzero_lefschetzMoment
    {N : Nat} (a : Fin N → ℚ) (ha : a ≠ 0) :
    ∃ q : Fin N, lefschetzTomography a q ≠ 0 := by
  by_contra h
  push_neg at h
  apply ha
  exact (lefschetzTomography_eq_zero_iff a).mp (by
    funext q
    exact h q)

/-- Finite vector of the live coefficients of a compact fibered Hodge state. -/
def supportCoordinateVector
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (f : FiberedHodgeAddress V H) :
    Fin (fiberedSupportSize f) → ℚ :=
  fun i => f (((fiberedSupportEquivFin f).symm i).1)

/-- The support vector is zero exactly when the original compact address is
zero. -/
theorem supportCoordinateVector_eq_zero_iff
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (f : FiberedHodgeAddress V H) :
    supportCoordinateVector f = 0 ↔ f = 0 := by
  constructor
  · intro hz
    apply Finsupp.ext
    intro s
    by_cases hs : s ∈ f.support
    · let slive : LiveFiberedAddress f := ⟨s, hs⟩
      have hi := congrFun hz (fiberedSupportEquivFin f slive)
      simpa [supportCoordinateVector, slive] using hi
    · exact Finsupp.not_mem_support_iff.mp hs
  · rintro rfl
    funext i
    simp [supportCoordinateVector]

/-- **LEFSCHETZ TOMOGRAPHY OF ONE CLASSICAL HODGE STATE.**  A nonzero
finite-support Hodge coordinate state always produces a nonzero exact
central-binomial Lefschetz moment in its finite multiplicity chart. -/
theorem nonzero_fiberedAddress_has_nonzero_lefschetzMoment
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (f : FiberedHodgeAddress V H)
    (hf : f ≠ 0) :
    ∃ q : Fin (fiberedSupportSize f),
      lefschetzTomography (supportCoordinateVector f) q ≠ 0 := by
  have hvec : supportCoordinateVector f ≠ 0 := by
    intro hz
    exact hf ((supportCoordinateVector_eq_zero_iff f).mp hz)
  exact exists_nonzero_lefschetzMoment (supportCoordinateVector f) hvec

/-- Any nonzero genuine rational Hodge class has a finite multiplicity chart
with a nonzero exact GST Lefschetz moment. -/
theorem nonzero_hodgeClass_has_nonzero_lefschetzMoment
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0) :
    ∃ q : Fin
        (fiberedSupportSize (fiberedWeightCoordinates V H p alpha)),
      lefschetzTomography
        (supportCoordinateVector
          (fiberedWeightCoordinates V H p alpha)) q ≠ 0 := by
  apply nonzero_fiberedAddress_has_nonzero_lefschetzMoment
  intro hzero
  apply halpha
  apply fiberedWeightCoordinates_injective V H p
  simpa [fiberedWeightCoordinates] using hzero

/-- Tomography crown: exact central-binomial kernel, unit-triangular
injectivity, and finite detection of every nonzero classical Hodge state. -/
theorem classical_hodge_lefschetz_tomography_crown
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) :
    (∀ N, Function.Injective (@lefschetzTomography N))
    ∧ (∀ p : Nat, ∀ alpha : ClassicalHodgeFiber V H p,
      alpha ≠ 0 →
        ∃ q : Fin
            (fiberedSupportSize (fiberedWeightCoordinates V H p alpha)),
          lefschetzTomography
            (supportCoordinateVector
              (fiberedWeightCoordinates V H p alpha)) q ≠ 0) := by
  exact ⟨
    fun N => lefschetzTomography_injective,
    fun p alpha h =>
      nonzero_hodgeClass_has_nonzero_lefschetzMoment V H p alpha h⟩

#check multiplicityLefschetzKernel
#check multiplicityLefschetzKernel_eq_worldAct
#check lefschetzTomography
#check lefschetzTomography_triangular
#check lefschetzTomography_injective
#check lefschetzTomography_eq_zero_iff
#check exists_nonzero_lefschetzMoment
#check supportCoordinateVector
#check supportCoordinateVector_eq_zero_iff
#check nonzero_fiberedAddress_has_nonzero_lefschetzMoment
#check nonzero_hodgeClass_has_nonzero_lefschetzMoment
#check classical_hodge_lefschetz_tomography_crown

#print axioms multiplicityLefschetzKernel_eq_worldAct
#print axioms lefschetzTomography_injective
#print axioms nonzero_hodgeClass_has_nonzero_lefschetzMoment
#print axioms classical_hodge_lefschetz_tomography_crown

end GSTClassicalHodgeLefschetzTomography
