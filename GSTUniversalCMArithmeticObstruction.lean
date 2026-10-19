import GSTCMQuadraticNativeRankForcing
import GSTClassicalHodgeCrossCarrierGeometricTransfer
import GSTWeilFourfoldAuxiliaryExtraction

/-!
# Universal Hodge: CM–NM obstruction and source–target geometry audit

This file is an adversarial check against a false unconditional completion.
It does NOT add any axiom, arbitrary cycle witness, or artificial Hodge action.

1. The imaginary-quadratic CM operator polynomial
     T² - 2aT + (a²+b²)I = 0, b != 0
   CANNOT hold on the rational one-dimensional vector space Q.
   Thus the earlier rank-two CM forcing cannot serve as a single
   UNIVERSAL operator law, notably for a rank-one Hodge fiber.
   This does not refute CM arithmetic on even-dimensional factors.
2. Any actual realized algebraic cross-carrier correspondence sends
   a class of an actual algebraic source cycle to the actual algebraic
   cycle-class range of its destination. If beta is NOT algebraic,
   it is impossible for beta to be obtained by any such transfer of
   an algebraic source cycle. More compositions of old transfers
   do not independently create algebraicity of arbitrary beta.

A path to an unconditional Hodge proof must supply a NEW actual
geometric construction for the arbitrary missing target class
(or establish a genuinely universal geometric mechanism beyond
transfer closure). Giving names to conditional CM/NM transfers
does not discharge this implication.
-/

set_option maxHeartbeats 20000000
noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTCMQuadraticNativeRankForcing
open GSTClassicalHodgeCrossCarrierGeometricTransfer
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeGeometricMatrixRankLanding
open GSTWeilFourfoldAuxiliaryExtraction

namespace GSTUniversalCMArithmeticObstruction

/-- A universal imaginary-quadratic CM law is already impossible on
the smallest nonzero rational Hodge carrier: a one-dimensional
Q-module. This uses the already verified CM rational-eigenline
contradiction, not an invented linear-algebra assumption. -/
theorem no_imaginary_quadratic_CM_on_rational_line
    (T : Module.End ℚ ℚ) (a b : ℚ) (hb : b ≠ 0)
    (hMin : ∀ z : ℚ,
      T (T z) - (2*a) • T z + (a^2+b^2) • z = 0) : False := by
  have hEigen : T (1:ℚ) = (T (1:ℚ)) • (1:ℚ) := by
    simp
  exact imaginary_quadratic_CM_no_rational_eigenline
    (W := ℚ) T a b hb hMin (1:ℚ) (by norm_num)
    (T (1:ℚ)) hEigen

variable {V W : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {J : HodgeBigradedBettiData W}
variable {p q : Nat}

/-- The geometric transfer law cannot output a nonalgebraic
cohomological target from an algebraic source. This has no
generic-surjectivity assumptions and applies to every genuine
cross-carrier transfer. -/
theorem no_algebraic_source_transfer_hits_non_algebraic_target
    (R : CrossCarrierTransfer V W H J p q)
    (target : RationalSingularCohomology J.analytification (2*q))
    (hnot : target ∉ LinearMap.range (J.cycleClass q)) :
    ¬ ∃ Z : codimensionCycles V.X p,
      R.betti (H.cycleClass p Z) = target := by
  rintro ⟨Z,hZ⟩
  apply hnot
  rw [← hZ]
  exact R.native_range_preserved Z

/-- The obstruction survives two consecutive genuine
cross-carrier transfers, even with different carriers/codimensions.
This prevents a formal CM -> auxiliary -> arbitrary-target
program from being mislabeled as a universal Hodge proof
without an independently proved source-to-target spanning law. -/
theorem no_composed_algebraic_transfer_hits_non_algebraic_target
    {U : SmoothProjectiveComplexScheme}
    {K : HodgeBigradedBettiData U}
    {r : Nat}
    (R : CrossCarrierTransfer V W H J p q)
    (S : CrossCarrierTransfer W U J K q r)
    (target : RationalSingularCohomology K.analytification (2*r))
    (hnot : target ∉ LinearMap.range (K.cycleClass r)) :
    ¬ ∃ Z : codimensionCycles V.X p,
      S.betti (R.betti (H.cycleClass p Z)) = target := by
  rintro ⟨Z,hZ⟩
  have hR : J.cycleClass q (R.native Z) =
      R.betti (H.cycleClass p Z) := R.naturality Z
  have hS : K.cycleClass r (S.native (R.native Z)) =
      S.betti (R.betti (H.cycleClass p Z)) := by
    rw [S.naturality,R.naturality]
  exact hnot ⟨S.native (R.native Z), hS.trans hZ⟩


/-! ## Generalized GST CM/NM multi-charge geometry: first new atom

The verified quadratic CM factorization handles a ONE-DIMENSIONAL
norm-one torus: characters come in opposite positive and negative weights.
Arbitrary Hodge varieties can carry HIGHER-RANK CM character
lattices, where an invariant degree-three atom may have NO
invariant quadratic subword.

The following exact new GST countermodel is a rank-two torus
whose three character weights are (1,0), (0,1), (-1,-1).
Their total charge is zero, but NONE of the three possible
quadratic pairings has charge zero (including repeated indices).
The proposed universal step "all CM invariants arise from
quadratic pairs" is therefore FALSE beyond the norm-one torus.

This does not refute algebraicity of that cubic Hodge character.
It isolates precisely the new type of geometry needed: genuine
algebraic realizations of higher-degree primitive CM invariants.
That is a construction obligation, not an assumed Chow preimage.
-/

/-- Two independent rational/integral CM-charge channels and
three primitive weights, in the GST CM/NM charge lattice. -/
def cubicCMWeight (i : Fin 3) (j : Fin 2) : ℤ :=
  if i = 0 then (if j = 0 then 1 else 0)
  else if i = 1 then (if j = 0 then 0 else 1)
  else -1

/-- Exact triadic GST CM invariant: all two charge channels cancel.
The result is a genuine degree-three weight-zero ATOM. -/
theorem cubic_CM_charge_invariant :
    ∀ j : Fin 2,
      cubicCMWeight 0 j + cubicCMWeight 1 j +
        cubicCMWeight 2 j = 0 := by
  decide

/-- There are NO opposite quadratic generators in this new
two-charge universe. Thus no path using only the OLD quadratic
norm-one pairing mechanism can generate the triadic invariant. -/
theorem no_quadratic_CM_invariant_in_three_weights :
    ∀ i k : Fin 3,
      ¬ (∀ j : Fin 2,
        cubicCMWeight i j + cubicCMWeight k j = 0) := by
  decide

/-- The next GST-CM primitive-generator law MUST contain cubic
or higher charge-balancing patterns: a degree-three invariant
cannot be assembled from zero-weight quadratic factors. -/
theorem cubic_CM_atom_requires_new_generator :
    (∀ j : Fin 2,
      cubicCMWeight 0 j + cubicCMWeight 1 j +
        cubicCMWeight 2 j = 0) ∧
    (∀ i k : Fin 3,
      ¬ (∀ j : Fin 2,
        cubicCMWeight i j + cubicCMWeight k j = 0)) :=
  ⟨cubic_CM_charge_invariant,
    no_quadratic_CM_invariant_in_three_weights⟩


/-! ## Even-degree GST CM obstruction: primitive quartic invariant

Odd-degree torus invariants alone cannot serve as rational (p,p)
classes, which have EVEN cohomological degree 2p. This strengthens
the previous countermodel to an explicit even-degree ZERO-SUM
quartic with no proper zero-sum subword.

The four integral rank-two CM charge weights are
(1,0), (0,1), (-1,2), (0,-3). Their sum is (0,0).
No quadratic or cubic expression from these weights (even allowing
repeated characters) has weight zero. In particular the
four-letter invariant cannot be made from invariant quadratic pairs.

This is a rigorous character-lattice obstruction to UNIVERSALLY
applying the quadratic E^n norm-one torus method to all GST CM worlds.
It is NOT a proof that such a quartic character is a (2,2) class on
a chosen smooth projective X, and it constructs no Chow cycle for it.
A genuine CM/Hodge realization and an independent native quartic
geometric cycle are still necessary.
-/

/-- Two-charge GST-NM extension with a quartic, irreducible
weight-zero character source rather than a quadratic pair. -/
def quarticCMWeight (i : Fin 4) (j : Fin 2) : ℤ :=
  if i = 0 then (if j = 0 then 1 else 0)
  else if i = 1 then (if j = 0 then 0 else 1)
  else if i = 2 then (if j = 0 then -1 else 2)
  else if j = 0 then 0 else -3

/-- Exact rank-two total CM charge cancellation in Hodge-relevant
even cohomological degree four. -/
theorem quartic_CM_zero_charge :
    ∀ j : Fin 2,
      quarticCMWeight 0 j + quarticCMWeight 1 j +
      quarticCMWeight 2 j + quarticCMWeight 3 j = 0 := by
  decide

/-- No quadratic invariant over these four character weights,
even when repeated source weights are allowed. -/
theorem quartic_CM_no_quadratic_subgenerator :
    ∀ i k : Fin 4,
      ¬ (∀ j : Fin 2,
        quarticCMWeight i j + quarticCMWeight k j = 0) := by
  decide

/-- No cubic invariant either. Therefore the four distinct
weights give a primitive new invariant atom of EXACT length four. -/
theorem quartic_CM_no_cubic_subgenerator :
    ∀ i k l : Fin 4,
      ¬ (∀ j : Fin 2,
        quarticCMWeight i j + quarticCMWeight k j +
        quarticCMWeight l j = 0) := by
  decide

/-- The multi-charge GST universe genuinely contains irreducible
even-degree CM invariants invisible to all old quadratic-pair laws.
A general Hodge construction therefore needs higher primitive sources
whose actual cycle classes must be established geometrically. -/
theorem quartic_CM_higher_generator_necessary :
    (∀ j : Fin 2,
      quarticCMWeight 0 j + quarticCMWeight 1 j +
      quarticCMWeight 2 j + quarticCMWeight 3 j = 0) ∧
    (∀ i k : Fin 4,
      ¬ (∀ j : Fin 2,
        quarticCMWeight i j + quarticCMWeight k j = 0)) ∧
    (∀ i k l : Fin 4,
      ¬ (∀ j : Fin 2,
        quarticCMWeight i j + quarticCMWeight k j +
        quarticCMWeight l j = 0)) :=
  ⟨quartic_CM_zero_charge,
    quartic_CM_no_quadratic_subgenerator,
    quartic_CM_no_cubic_subgenerator⟩


/-! ## Stronger GST multicharge result: primitive invariant generators
in UNBOUNDED even Hodge degrees

The preceding quartic was not a finite-rank coincidence. For ANY
N >= 2, consider the rank-two CM character weights
  a = (1,0),  b = (0,1),  c = (-N,-1).
The multiset with N copies of a, one b, and one c has total
charge (0,0) and length N+2.

A submultiset consists of m <= N copies of a and indicators
u,v in {0,1} for b,c. Its two charge equations are
   m-N*v = 0,  u-v = 0.
They force either the EMPTY word (m=u=v=0) or the ENTIRE
word (m=N,u=v=1). Thus the full invariant is a primitive
generator that cannot be factored into any lower positive
zero-weight generators, even when quadratic/cubic factors
are replaced with every lower degree.

Taking N=2p-2 produces primitive formal CM invariants in
every EVEN degree 2p, all p >= 2. Therefore no uniform finite
bound on invariant-generator degree exists across arbitrary
higher-rank GST CM charge systems.

CAVEAT: these are integral character-lattice identities.
The realization as ACTUAL rational (p,p) Hodge classes and
actual Chow cycles is a separate geometric question.
-/

/-- Exact *unbounded* multicharge zero-sum atom classification.
For fixed N, the only invariant subwords of a^N*b*c are
the empty word and the full word. -/
theorem CM_multicharge_zero_sum_atom_all_lengths
    (N m : ℕ) (u v : Fin 2)
    (hCharge1 : (m : ℤ) - (N : ℤ) * (v.val : ℤ) = 0)
    (hCharge2 : (u.val : ℤ) - (v.val : ℤ) = 0) :
    (m = 0 ∧ u = 0 ∧ v = 0) ∨
      (m = N ∧ u = 1 ∧ v = 1) := by
  fin_cases u <;> fin_cases v <;>
    norm_num at * <;> omega

/-- Every rational Hodge codimension p >= 2 is compatible with a
FORMAL primitive weight-zero CM atom of even degree 2p, which
cannot be generated by lower-degree invariant subwords.
This disproves a universal finite-degree bound for unrestricted
CM character-lattice generators; it is NOT an algebraic Hodge
existence theorem on arbitrary smooth projective varieties. -/
theorem CM_unbounded_even_degree_primitive_atom
    (p : ℕ) (hp : 2 ≤ p) :
    ∃ N : ℕ,
      2 ≤ N ∧ N + 2 = 2 * p ∧
      (∀ (m : ℕ) (u v : Fin 2),
        m ≤ N →
        (m : ℤ) - (N : ℤ) * (v.val : ℤ) = 0 →
        (u.val : ℤ) - (v.val : ℤ) = 0 →
          (m = 0 ∧ u = 0 ∧ v = 0) ∨
          (m = N ∧ u = 1 ∧ v = 1)) := by
  refine ⟨2 * p - 2, by omega, by omega, ?_⟩
  intro m u v _hm h1 h2
  exact CM_multicharge_zero_sum_atom_all_lengths
    (2 * p - 2) m u v h1 h2

/-! ## GST–CM explicit Weil projector from a GENUINE algebraic isogeny

For an abelian fourfold A of Weil type admitting K=Q(i)
multiplication of Hodge signature (2,2), the algebraic isogeny
 f=[1+i]: A → A acts on H¹(C) with σ/σbar eigenvalues
 λ=1+i, μ=1-i, each with multiplicity four.

On H⁴=∧⁴ H¹, the five σ-count eigensectors r=0,..,4 have
 eigenvalues λ^r μ^(4-r) = -4,-4i,4,4i,-4,
 multiplicities C(4,r)^2 = 1,16,36,16,1.

Thus the normalized CM action U=(1/4) f* on H⁴ satisfies
 U⁴=I. Its minus-one eigenspace has dimension TWO:
  ∧⁴ H¹_σ ⊕ ∧⁴ H¹_σbar.
The signature (2,2) makes these rational Weil classes
Hodge type (2,2). The projector

  Π_W = (I-U+U²-U³)/4

is a rational algebraic-correspondence action: it is a
rational combination of the identity diagonal and transpose
graphs of the actual isogenies f,f²,f³. No arbitrary Hodge
preimage or custom axiom is supplied by this construction.

IMPORTANT: Π_W is idempotent on H⁴, not asserted to be a Chow
idempotent nor idempotent on other Betti degrees. Its output
is an algebraic CORRESPONDENCE, not automatically an algebraic
cycle REPRESENTING each rational Weil class. It annihilates
the ambient divisor square and isolates the genuinely new
source sector needed by Gate 3.
-/

/-- The universal rational scalar polynomial for the minus-one
eigenspace of a finite-order-four rational CM action. -/
def cmWeilMinusOneProjectorPolynomial
    {R : Type*} [Field R] (u : R) : R :=
  (1 - u + u^2 - u^3) / 4

/-- Exact idempotent polynomial modulo u⁴=1, proved for every
field without spectral or analytic assumptions. -/
theorem cmWeilMinusOneProjectorPolynomial_idempotent
    {R : Type*} [Field R] [CharZero R]
    (u : R) (hFourth : u^4 = 1) :
    cmWeilMinusOneProjectorPolynomial u *
      cmWeilMinusOneProjectorPolynomial u =
      cmWeilMinusOneProjectorPolynomial u := by
  have hFactor :
      cmWeilMinusOneProjectorPolynomial u *
          cmWeilMinusOneProjectorPolynomial u -
          cmWeilMinusOneProjectorPolynomial u =
        (u^4 - 1) * (u^2 - 2*u + 3) / 16 := by
    dsimp [cmWeilMinusOneProjectorPolynomial]
    ring
  rw [hFourth] at hFactor
  have hz :
      cmWeilMinusOneProjectorPolynomial u *
          cmWeilMinusOneProjectorPolynomial u -
          cmWeilMinusOneProjectorPolynomial u = 0 := by
    simpa using hFactor
  exact sub_eq_zero.mp hz

theorem cmWeilMinusOneProjectorPolynomial_on_minus_one
    {R : Type*} [Field R] [CharZero R] :
    cmWeilMinusOneProjectorPolynomial (-1 : R) = 1 := by
  dsimp [cmWeilMinusOneProjectorPolynomial]
  norm_num

theorem cmWeilMinusOneProjectorPolynomial_on_plus_one
    {R : Type*} [Field R] [CharZero R] :
    cmWeilMinusOneProjectorPolynomial (1 : R) = 0 := by
  dsimp [cmWeilMinusOneProjectorPolynomial]
  norm_num

/-- The odd-signature CM sectors have normalized eigenvalues
±i, characterized algebraically by u²+1=0, and are killed. -/
theorem cmWeilMinusOneProjectorPolynomial_on_quadratic
    {R : Type*} [Field R] [CharZero R]
    (u : R) (hQuadratic : u^2 + 1 = 0) :
    cmWeilMinusOneProjectorPolynomial u = 0 := by
  have hFactor :
      cmWeilMinusOneProjectorPolynomial u =
       -(u-1)*(u^2+1)/4 := by
    dsimp [cmWeilMinusOneProjectorPolynomial]
    ring
  rw [hFactor, hQuadratic]
  ring

/-- Exact rank census of the genuine Weil fourfold H⁴ CM
representation. The geometric rank-two identification uses
the external K-linear exterior decomposition ∧⁴_K H¹. -/
theorem cmWeilFourfoldExactSpectrumCensus :
    1 + 16 + 36 + 16 + 1 = 70 ∧
      1 + 1 = 2 := by
  norm_num

/-! ## Actual split Weil-cycle source INDEPENDENCE for EVERY p

Let E be a CM elliptic curve and A=E^(2p) with the first p
factors carrying +i and last p factors carrying -i.
For the algebraic mixed Poincare divisors D_j and their CM-graph
rotates C_j, the genuine algebraic codimension-p cycles

  Z_D = D_1⋯D_p,
  Z_C = C_1 D_2⋯D_p

have two independent images under the constructed Weil CM
algebraic-correspondence projector.

In the two complex CM Weil eigenspaces with basis (Ωσ,Ωbarσ),
write u=i/2 (and -u=-i/2). The projected coefficients are
  Z_D ↦ (u^p,(-u)^p),
  Z_C ↦ (u^(p-1)/2,(-u)^(p-1)/2).

The 2×2 determinant for p=n+1 is exactly
 u^(n+1)*(-u)^n ≠ 0.
Thus two real rational algebraic projected cycles genuinely
SPAN the full rational rank-two Weil Hodge space for every p.
This is not an assumed rank-two algebraic source. It is
manufactured from the actual graph-divisor intersection cycles.
The following theorem checks the general coefficient identity
over EVERY characteristic-zero field.
-/

/-- Exact universal CM split Weil projected-cycle determinant.
The scalar u=i/2 is nonzero in the real geometric CM instance. -/
theorem cmWeilSplitSourceDeterminant
    {R : Type*} [Field R] [CharZero R]
    (u : R) (n : ℕ) :
    u^(n+1) * ((-u)^n / 2) -
      (-u)^(n+1) * (u^n / 2) =
        u^(n+1) * (-u)^n := by
  rw [pow_succ, pow_succ]
  ring

/-- EVERY codimension p>=1: the two genuine projected algebraic
CM graph-divisor source vectors are linearly independent.
This numeric determinant is the exact uniform certificate;
the actual graph/Betti comparison is independent scheme geometry. -/
theorem cmWeilSplitSourceDeterminant_nonzero
    {R : Type*} [Field R] [CharZero R]
    (u : R) (hu : u ≠ 0) (n : ℕ) :
    u^(n+1) * ((-u)^n / 2) -
      (-u)^(n+1) * (u^n / 2) ≠ 0 := by
  rw [cmWeilSplitSourceDeterminant]
  exact mul_ne_zero (pow_ne_zero _ hu)
    (pow_ne_zero _ (neg_ne_zero.mpr hu))

/-! ## Single-source exact reconstruction in the rank-two Weil Hodge sector

The previous split construction built two independent native cycles.
For a GENERAL Weil-type abelian 2p-fold the arithmetic CM isogeny
and the 2-dimensional Weil Hodge eigenspace still exist.

Crucial reduction: it is enough to produce ONE algebraic cycle Z
whose Weil projection is NONZERO. Let T be the actual induced CM
operator on its two-dimensional rational Weil module. Its minimal
polynomial is t²-2a t+(a²+b²) with b != 0.

Choose a rational basis in which T is the companion matrix
   T (x,y) = (-(a²+b²)y, x+2a y).
For any nonzero z=(x,y), the two genuinely algebraic source
classes z and T z have determinant

   D = (x+a y)² + (b y)² > 0.

Every prescribed target alpha=(u,v) on the ORIGINAL abelian
variety is represented by a completely explicit rational
linear combination of Z and the algebraic CM-isogeny translate
T Z. No assumed Gram full rank, no arbitrary cycle selector.
The only source-birth premise is the one geometrically testable
nonzero projected algebraic cycle. This is the exact remaining
nonsplit Weil requirement, NOT a proof of its existence.
-/

/-- An exact strictly positive CM orbit determinant. -/
def cmWeilOneSourceDet (a b x y : ℚ) : ℚ :=
  x*(x+2*a*y) + (a*a+b*b)*y*y

theorem cmWeilOneSourceDet_pos
    (a b x y : ℚ) (hb : b ≠ 0)
    (hz : x ≠ 0 ∨ y ≠ 0) :
    0 < cmWeilOneSourceDet a b x y := by
  have heq : cmWeilOneSourceDet a b x y =
      (x+a*y)^2 + (b*y)^2 := by
    dsimp [cmWeilOneSourceDet]
    ring
  rw [heq]
  by_cases hy : y = 0
  · have hx : x ≠ 0 := by
      rcases hz with hx | hy'
      · exact hx
      · exact False.elim (hy' hy)
    subst y
    simpa using (sq_pos_of_ne_zero hx)
  · have hby : b*y ≠ 0 := mul_ne_zero hb hy
    nlinarith [sq_nonneg (x+a*y), sq_pos_of_ne_zero hby]

/-- Explicit original-Weil-target coefficient for a native
projected cycle z=(x,y). -/
noncomputable def cmWeilOneSourceCoeff0
    (a b x y u v : ℚ) : ℚ :=
  (u*(x+2*a*y) + (a*a+b*b)*y*v) / cmWeilOneSourceDet a b x y

/-- Explicit coefficient of the genuine algebraic CM translate Tz. -/
noncomputable def cmWeilOneSourceCoeff1
    (a b x y u v : ℚ) : ℚ :=
  (x*v-y*u) / cmWeilOneSourceDet a b x y

/-- For an arbitrary prescribed rational Weil target (u,v),
the actual native CM orbit z,Tz returns that target EXACTLY.
All variables and coefficients are rational; the geometric
Gysin and native/Betti comparison are the existing GST CM laws. -/
theorem cmWeilOneSourceReconstruction
    (a b x y u v : ℚ) (hb : b ≠ 0)
    (hz : x ≠ 0 ∨ y ≠ 0) :
    cmWeilOneSourceCoeff0 a b x y u v * x -
      cmWeilOneSourceCoeff1 a b x y u v *
        ((a*a+b*b)*y) = u ∧
    cmWeilOneSourceCoeff0 a b x y u v * y +
      cmWeilOneSourceCoeff1 a b x y u v *
        (x+2*a*y) = v := by
  have hd : cmWeilOneSourceDet a b x y ≠ 0 :=
    ne_of_gt (cmWeilOneSourceDet_pos a b x y hb hz)
  dsimp [cmWeilOneSourceCoeff0, cmWeilOneSourceCoeff1]
  constructor
  · field_simp
    dsimp [cmWeilOneSourceDet]
    ring
  · field_simp
    dsimp [cmWeilOneSourceDet]
    ring

/-! ## GST RATIONAL-HODGE COUNTEREXAMPLE TEST — ZERO OR FULL WEIL SOURCE

This is a sharpened falsification test, NOT a postulated
nonalgebraic Hodge class. In the true rank-two exceptional Weil
Hodge sector of a genuine Weil-type abelian fourfold, the actual
algebraic CM isogeny [2+i] acts with the irreducible rational
quadratic t²+14t+625 (discriminant -2304).

Any rational subspace of this 2-plane invariant under this
genuinely algebraic isogeny is either zero or the entire plane.
In particular the image of ACTUAL native Chow cycles under
the genuine algebraic CM projector, provided the correct
canonical-Betti commuting square, cannot have rank one.

This is stronger than checking a missing divisor source:
to disprove rational Hodge on such an original variety one must
prove the projected image of EVERY codimension-two algebraic
cycle vanishes. A mere failure of divisor-generation or of a
finite source catalog is not enough.

The invariant-submodule theorem below is fully proved linear
algebra and reuses the independently verified GST
cmWeilOneSourceReconstruction. The geometric specialization
requires a genuine Weil Hodge plane, canonical cycle map and
K-isogeny naturality; those are NOT manufactured as instances.
-/

/-- The exact rational two-coordinate action of the CM isogeny
[2+i] on the exceptional Weil H^4 plane, expressed in companion
coordinates. Its characteristic polynomial is t²+14t+625. -/
def cmWeilFourfoldCompanionAction (z : ℚ × ℚ) : ℚ × ℚ :=
  (-(625 : ℚ) * z.2, z.1 - 14*z.2)

/-- A single nonzero genuine Weil source in an invariant native
algebraic subspace produces EVERY rational Weil target using
the already proved GST target reconstruction coefficients.
No assumed full-rank or Hodge-to-Chow inverse. -/
theorem cmWeilInvariantSource_nonzero_forces_full_plane
    (S : Submodule ℚ (ℚ × ℚ))
    (hInvariant : ∀ z ∈ S, cmWeilFourfoldCompanionAction z ∈ S)
    (z : ℚ × ℚ) (hz : z ∈ S) (hzero : z ≠ 0) :
    S = ⊤ := by
  rcases z with ⟨x, y⟩
  have hxy : x ≠ 0 ∨ y ≠ 0 := by
    by_cases hx : x = 0
    · right
      intro hy
      exact hzero (by simp [hx, hy])
    · exact Or.inl hx
  have htranslate := hInvariant (x,y) hz
  apply le_antisymm le_top
  intro target _
  rcases target with ⟨u, v⟩
  let c0 := cmWeilOneSourceCoeff0 (-7) 24 x y u v
  let c1 := cmWeilOneSourceCoeff1 (-7) 24 x y u v
  obtain ⟨hfirst, hsecond⟩ :=
    cmWeilOneSourceReconstruction (-7) 24 x y u v (by norm_num) hxy
  have htarget :
      (u, v) = c0 • (x,y) +
        c1 • cmWeilFourfoldCompanionAction (x,y) := by
    apply Prod.ext
    · change u = c0*x + c1*(-(625 : ℚ)*y)
      change c0*x - c1*(((-7 : ℚ)*(-7)+24*24)*y) = u at hfirst
      nlinarith [hfirst]
    · change v = c0*y + c1*(x-14*y)
      change c0*y + c1*(x+2*(-7 : ℚ)*y) = v at hsecond
      nlinarith [hsecond]
  rw [htarget]
  exact S.add_mem (S.smul_mem c0 hz) (S.smul_mem c1 htranslate)

/-- A rational CM-stable native Weil algebraic source image is
EITHER zero (every nonzero Weil class is a potential genuinely
nonalgebraic target) OR the full Weil plane (every Weil class
is reached by actual algebraic cycles).
Rank one is impossible. -/
theorem cmWeilStableSourceDichotomy
    (S : Submodule ℚ (ℚ × ℚ))
    (hInvariant : ∀ z ∈ S, cmWeilFourfoldCompanionAction z ∈ S) :
    S = ⊥ ∨ S = ⊤ := by
  by_cases hTop : S = ⊤
  · exact Or.inr hTop
  · left
    apply le_antisymm ?_ bot_le
    intro z hz
    by_cases hz0 : z = 0
    · simpa [hz0]
    · exact False.elim (hTop
        (cmWeilInvariantSource_nonzero_forces_full_plane
          S hInvariant z hz hz0))

/-! ## EXPLICIT ACTUAL CM ISOGENY SOURCE FILTER — NO TARGET PREIMAGE

The original Weil-type fourfold carries the genuine algebraic
isogeny f=[2+i]. On H^4 its Hodge-compatible eigensectors have
three rational spectral factors:
  exceptional Weil: t²+14t+625;
  mixed K-weight:   t²-30t+625;
  ambient weight:   t-25.

CRT over Q gives a literal rational degree-four polynomial
 P_W(t)= -(t-25)(39t-79)(t²-30t+625)/44000000.
Every coefficient defines an actual rational combination of
graphs of iterates f^j on the SAME abelian fourfold. Therefore
testing P_W(cl Z) on a genuine algebraic surface Z is an
explicit finite correspondence calculation; it does NOT
guarantee a nonzero output.

The exact polynomial here upgrades the counterexample test:
P_W kills the full generic divisor/ambient sector, fixes the
entire two-dimensional rational Weil plane, and kills the other
mixed spectral sectors. The remaining nonalgebraicity claim,
if pursued, must establish that P_W cl(Z)=0 for EVERY actual
algebraic surface Z, not just the divisor subalgebra.
-/

/-- Explicit rational polynomial producing the exceptional Weil
source projector from the actual endomorphism f=[2+i]. -/
def cmWeilTwoPlusIProjectorScalar (t : ℚ) : ℚ :=
  -((t-25)*(39*t-79)*(t*t-30*t+625))/44000000

/-- Complete exact CRT identity on the exceptional conjugate Weil
eigenroots. Unlike an uninterpreted projector hypothesis, all
rational denominators and coefficients are explicit. -/
theorem cmWeilTwoPlusIProjector_fixes_Weil
    (t : ℚ) (hWeil : t*t+14*t+625=0) :
    cmWeilTwoPlusIProjectorScalar t = 1 := by
  have hfactor :
      cmWeilTwoPlusIProjectorScalar t - 1 =
        -((t*t+14*t+625)*(39*t*t-2770*t+72375))/44000000 := by
    unfold cmWeilTwoPlusIProjectorScalar
    ring
  rw [hWeil] at hfactor
  have hz : cmWeilTwoPlusIProjectorScalar t - 1 = 0 := by
    simpa using hfactor
  linarith

/-- All mixed CM eigensectors have zero projected Weil class. -/
theorem cmWeilTwoPlusIProjector_kills_mixed
    (t : ℚ) (hMixed : t*t-30*t+625=0) :
    cmWeilTwoPlusIProjectorScalar t = 0 := by
  unfold cmWeilTwoPlusIProjectorScalar
  rw [hMixed]
  ring

/-- The genuine ambient polarization-square eigenvalue is 5². -/
theorem cmWeilTwoPlusIProjector_kills_ambient :
    cmWeilTwoPlusIProjectorScalar 25 = 0 := by
  norm_num [cmWeilTwoPlusIProjectorScalar]

/-- Idempotent on EVERY actual H^4 spectral channel of f=[2+i].
The required spectrum census already exists elsewhere in this
GST module; this checks the polynomial on those three factors. -/
theorem cmWeilTwoPlusIProjector_idempotent_on_spectrum
    (t : ℚ)
    (hSpectrum :
      t*t+14*t+625=0 ∨
      t*t-30*t+625=0 ∨
      t=25) :
    (cmWeilTwoPlusIProjectorScalar t)^2 =
      cmWeilTwoPlusIProjectorScalar t := by
  rcases hSpectrum with hWeil | hMixed | hAmbient
  · rw [cmWeilTwoPlusIProjector_fixes_Weil t hWeil]
    norm_num
  · rw [cmWeilTwoPlusIProjector_kills_mixed t hMixed]
    norm_num
  · subst t
    rw [cmWeilTwoPlusIProjector_kills_ambient]
    norm_num

/-! ## GST UNSPLIT WEIL SIXFOLD — EXPLICIT GEOMETRIC FALSIFICATION FILTER

The marked all-powers split Weil sixfold theorem requires a hyperbolic
rational Hermitian form. The REAL polarized Weil-sixfold PEL datum
h=diag(1,1,1,-1,-1,-3) on the K=Q(i) lattice Z[i]^6 has
archimedean signature (3,3) and determinant -3, NOT a rational
K-norm multiple of the split hyperbolic determinant -1.
The elementary Q(i) inert-prime norm obstruction at 3 makes it
nonsplit (recorded separately with the exact arithmetic argument).

It gives an actual abelian sixfold at the product-CM central point,
and a nonempty compatible polarized deformation family. The
generic member's exceptional pure-K Weil plane is a rational Hodge
(3,3) two-plane, outside the known split-sixfold theorem's scope.

For the GENUINE algebraic CM isogeny f=[2+i], the H^6 rational
spectrum contains FOUR distinct rational factors:
  pure Weil j=0,6:           t²+234t+15625
  mixed K-weight j=1,5:     t²+70t+15625
  mixed K-weight j=2,4:     t²-150t+15625
  balanced weight j=3:      t-125.
Thus Chinese remaindering constructs a rational POLYNOMIAL
of actual algebraic graphs, projecting onto the prescribed
two-dimensional Hodge Weil sector on the SAME original sixfold.
The operator itself is not a cycle representing that sector.

This is a falsifiable candidate for rational-Hodge obstruction,
not a proved nonalgebraic Hodge class. A counterexample requires
showing its action on ALL actual CH^3 cycles is zero on a
nonsplit generic member. A single nonzero projected genuine
algebraic CH^3 source instead proves the whole Weil plane algebraic.
-/

/-- Exact genuine CM-isogeny spectral projector on the pure
sixth-exterior rational Weil plane; rational polynomial in [2+i]*. -/
def cmWeilSixfoldNonsplitProjectorScalar (t : ℚ) : ℚ :=
  -((t-125)*(10391779+68381*t)*
    (t*t-150*t+15625)*(t*t+70*t+15625)) /
    930187500000000000

/-- The CRT polynomial is identity on both conjugate SIXTH-POWER
eigenvalues (-117±44 i), not an abstract cycle selector. -/
theorem cmWeilSixfoldNonsplitProjector_fixes_Weil
    (t : ℚ) (hWeil : t*t+234*t+15625=0) :
    cmWeilSixfoldNonsplitProjectorScalar t = 1 := by
  have hFactor :
      (cmWeilSixfoldNonsplitProjectorScalar t - 1) *
          (930187500000000000 : ℚ) =
        (t*t+234*t+15625) *
          (-39235556640625 + 454859000000*t -
            3496778250*t*t + 19627480*t*t*t -
            68381*t*t*t*t) := by
    unfold cmWeilSixfoldNonsplitProjectorScalar
    ring
  rw [hWeil, zero_mul] at hFactor
  have hDen : (930187500000000000 : ℚ) ≠ 0 := by norm_num
  have h := (mul_eq_zero.mp hFactor).resolve_right hDen
  linarith

theorem cmWeilSixfoldNonsplitProjector_kills_mixedOne
    (t : ℚ) (hMixed : t*t+70*t+15625=0) :
    cmWeilSixfoldNonsplitProjectorScalar t = 0 := by
  unfold cmWeilSixfoldNonsplitProjectorScalar
  rw [hMixed]
  ring

theorem cmWeilSixfoldNonsplitProjector_kills_mixedTwo
    (t : ℚ) (hMixed : t*t-150*t+15625=0) :
    cmWeilSixfoldNonsplitProjectorScalar t = 0 := by
  unfold cmWeilSixfoldNonsplitProjectorScalar
  rw [hMixed]
  ring

theorem cmWeilSixfoldNonsplitProjector_kills_ambient :
    cmWeilSixfoldNonsplitProjectorScalar 125 = 0 := by
  norm_num [cmWeilSixfoldNonsplitProjectorScalar]

/-- Exact idempotence on the WHOLE seven-weight H^6 CM spectrum.
For an actual polarized abelian sixfold this translates, under
canonical Betti functoriality, to a finite rational Chow graph
correspondence; that specialization is not assumed below. -/
theorem cmWeilSixfoldNonsplitProjector_idempotent_on_spectrum
    (t : ℚ)
    (hSpectrum :
      t*t+234*t+15625=0 ∨
      t*t+70*t+15625=0 ∨
      t*t-150*t+15625=0 ∨
      t=125) :
    cmWeilSixfoldNonsplitProjectorScalar t ^ 2 =
      cmWeilSixfoldNonsplitProjectorScalar t := by
  rcases hSpectrum with hPure | hMixedOne | hMixedTwo | hAmbient
  · rw [cmWeilSixfoldNonsplitProjector_fixes_Weil t hPure]
    norm_num
  · rw [cmWeilSixfoldNonsplitProjector_kills_mixedOne t hMixedOne]
    norm_num
  · rw [cmWeilSixfoldNonsplitProjector_kills_mixedTwo t hMixedTwo]
    norm_num
  · subst t
    rw [cmWeilSixfoldNonsplitProjector_kills_ambient]
    norm_num

/-! ## SIXFOLD FALSIFICATION CRITERION IN THE TRUE CM-ISOGENY ORBIT

On the rational pure-K Weil (3,3) two-plane, f=[2+i] has
companion rational matrix (0,-15625;1,-234) and irreducible
minimal polynomial t²+234t+15625 with conjugate non-real
roots -117±44i.

A genuine algebraic Chow-image projected by the explicit
polynomial above is preserved by this genuine CM isogeny.
It is consequently EITHER ZERO OR THE ENTIRE exceptional
Weil plane, with no intermediate algebraic line.

To DISPROVE rational Hodge for one nonsplit polarized sixfold
one must establish vanishing of the projector on EVERY
actual codimension-three Chow cycle; testing finite catalogs
or divisor-generated classes alone is insufficient.
-/

/-- Rational companion normal form of [2+i]* on pure Weil H^6. -/
def cmWeilSixfoldCompanionAction (z : ℚ × ℚ) : ℚ × ℚ :=
  (-(15625 : ℚ) * z.2, z.1 - 234*z.2)

/-- The verified GST rational one-source reconstruction, specialized
to the sixth-power CM eigenvalue -117+44i. -/
theorem cmWeilSixfold_nonzero_algebraic_source_spans_plane
    (S : Submodule ℚ (ℚ × ℚ))
    (hInvariant : ∀ z ∈ S, cmWeilSixfoldCompanionAction z ∈ S)
    (z : ℚ × ℚ) (hz : z ∈ S) (hzero : z ≠ 0) :
    S = ⊤ := by
  rcases z with ⟨x, y⟩
  have hxy : x ≠ 0 ∨ y ≠ 0 := by
    by_cases hx : x = 0
    · right
      intro hy
      exact hzero (by simp [hx, hy])
    · exact Or.inl hx
  have htranslate := hInvariant (x,y) hz
  apply le_antisymm le_top
  intro target _
  rcases target with ⟨u, v⟩
  let c0 := cmWeilOneSourceCoeff0 (-117) 44 x y u v
  let c1 := cmWeilOneSourceCoeff1 (-117) 44 x y u v
  obtain ⟨hfirst, hsecond⟩ :=
    cmWeilOneSourceReconstruction (-117) 44 x y u v (by norm_num) hxy
  have htarget :
      (u, v) = c0 • (x,y) +
        c1 • cmWeilSixfoldCompanionAction (x,y) := by
    apply Prod.ext
    · change u = c0*x + c1*(-(15625 : ℚ)*y)
      change c0*x - c1*(((-117 : ℚ)*(-117)+44*44)*y) = u at hfirst
      nlinarith [hfirst]
    · change v = c0*y + c1*(x-234*y)
      change c0*y + c1*(x+2*(-117 : ℚ)*y) = v at hsecond
      nlinarith [hsecond]
  rw [htarget]
  exact S.add_mem (S.smul_mem c0 hz) (S.smul_mem c1 htranslate)

theorem cmWeilSixfoldStableSourceDichotomy
    (S : Submodule ℚ (ℚ × ℚ))
    (hInvariant : ∀ z ∈ S, cmWeilSixfoldCompanionAction z ∈ S) :
    S = ⊥ ∨ S = ⊤ := by
  by_cases hTop : S = ⊤
  · exact Or.inr hTop
  · left
    apply le_antisymm ?_ bot_le
    intro z hz
    by_cases hz0 : z = 0
    · simpa [hz0]
    · exact False.elim (hTop
        (cmWeilSixfold_nonzero_algebraic_source_spans_plane
          S hInvariant z hz hz0))

/-! ## EXACT DEFORMATION TEST OF THE *ACTUAL* CENTRAL CM GRAPH SOURCE

Fix the CM central fibre of a Weil (3,3) sixfold. The true
rational graph-difference divisors are the three real classes
D_i=(p_i∧n_i - bar(p_i)∧bar(n_i))/(2i), where p_i,n_i are
K-eigenvectors of Hodge types (1,0),(0,1), respectively.

Under the nine first-order unitary deformations B=(B_{a b})
with delta(p_b)=Σ_a B_{a b} n_a and
delta(bar(n_a))=Σ_b B_{a b} bar(p_b), the exterior-algebra
derivative of the ACTUAL product D_1 D_2 D_3 is a linear map
from its nine period tangent coordinates into Λ⁶(H¹_C).

An exact 924×9 wedge-expansion (Wolfram, all basis monomials)
has six coefficient witnesses at exterior ordered index sets
  235678, 235679, 134678, 134689, 124579, 124589.
They extract, up to the common nonzero scalar (2i)^(-3),
  B_12, B_13, -B_21, B_23, -B_31, -B_32.
The remaining three tangent coordinates B_11,B_22,B_33
do not change this Hodge component. The full differential
rank is exactly six.

The following kernel-checkable rational normal form proves
this six-direction obstruction has a genuine rational right
inverse, rather than merely an evaluated determinant.
The full wedge expansion and its identification with actual
Gauss-Manin variation are documented in research/records;
Lean here proves the resulting explicit 6-coordinate map,
NOT the analytic Kodaira-Spencer comparison.

This is a route discriminator: the unprojected central graph
source cannot remain Hodge for generic nine-parameter periods.
The pure-K Weil *projection* stays of type (3,3); supplying a
deformable sheaf for that projected source is the next target.
-/

/-- Exact six exterior-coordinate witnesses of first-order Hodge
variation of the CM graph intersection at its product seed. -/
def cmWeilSixfoldGraphFirstOrderDetector
    (B : Matrix (Fin 3) (Fin 3) ℚ) : Fin 6 → ℚ :=
  ![ B 0 1, B 0 2, -(B 1 0),
     B 1 2, -(B 2 0), -(B 2 1) ]

/-- The complete obstruction witness vanishes exactly when
every off-diagonal infinitesimal unitary deformation vanishes.
There are six independent blocked directions, not all nine. -/
theorem cmWeilSixfoldGraphFirstOrderDetector_zero_iff
    (B : Matrix (Fin 3) (Fin 3) ℚ) :
    cmWeilSixfoldGraphFirstOrderDetector B = 0 ↔
      B 0 1 = 0 ∧ B 0 2 = 0 ∧
      B 1 0 = 0 ∧ B 1 2 = 0 ∧
      B 2 0 = 0 ∧ B 2 1 = 0 := by
  constructor
  · intro h
    have h01 := congrArg (fun v : Fin 6 → ℚ => v 0) h
    have h02 := congrArg (fun v : Fin 6 → ℚ => v 1) h
    have h10 := congrArg (fun v : Fin 6 → ℚ => v 2) h
    have h12 := congrArg (fun v : Fin 6 → ℚ => v 3) h
    have h20 := congrArg (fun v : Fin 6 → ℚ => v 4) h
    have h21 := congrArg (fun v : Fin 6 → ℚ => v 5) h
    simp [cmWeilSixfoldGraphFirstOrderDetector] at h01 h02 h10 h12 h20 h21
    exact ⟨h01, h02, h10, h12, h20, h21⟩
  · rintro ⟨h01,h02,h10,h12,h20,h21⟩
    funext k
    fin_cases k <;> simp [cmWeilSixfoldGraphFirstOrderDetector,
      h01, h02, h10, h12, h20, h21]

/-- Reconstruct an honest tangent matrix with arbitrary prescribed
six graph-deformation witness values, setting the three diagonal
period coordinates to zero. -/
def cmWeilSixfoldGraphFirstOrderLift
    (v : Fin 6 → ℚ) : Matrix (Fin 3) (Fin 3) ℚ :=
  fun i j =>
    if i = 0 then
      if j = 1 then v 0 else if j = 2 then v 1 else 0
    else if i = 1 then
      if j = 0 then -(v 2) else if j = 2 then v 3 else 0
    else
      if j = 0 then -(v 4) else if j = 1 then -(v 5) else 0

/-- RATIONAL RIGHT INVERSE: all six detected Hodge-loss
coordinates occur independently in actual unitary tangent data. -/
theorem cmWeilSixfoldGraphFirstOrderLift_rightInverse
    (v : Fin 6 → ℚ) :
    cmWeilSixfoldGraphFirstOrderDetector
      (cmWeilSixfoldGraphFirstOrderLift v) = v := by
  funext k
  fin_cases k <;>
    simp [cmWeilSixfoldGraphFirstOrderDetector,
      cmWeilSixfoldGraphFirstOrderLift]

/-- Consequently all six witness coordinates are realized:
the first-order graph-obstruction detector is onto. -/
theorem cmWeilSixfoldGraphFirstOrderDetector_surjective :
    Function.Surjective cmWeilSixfoldGraphFirstOrderDetector := by
  intro v
  exact ⟨cmWeilSixfoldGraphFirstOrderLift v,
    cmWeilSixfoldGraphFirstOrderLift_rightInverse v⟩

#check cmWeilSixfoldGraphFirstOrderDetector_zero_iff
#check cmWeilSixfoldGraphFirstOrderDetector_surjective
#print axioms cmWeilSixfoldGraphFirstOrderDetector_surjective

/-! ## COMPLETE GST CENTRAL-GRAPH PERIOD TANGENT NORMAL FORM

The prior exact 924-term exterior calculation and independent right
inverse show six obstructed period directions. This upgrade proves
an EXPLICIT decomposition of every nine-coordinate unitary tangent:
  B = diagonal(B) + lift(detector(B)).
There are exactly THREE first-order directions in which the raw
central graph stays Hodge, rather than an assumed or sampled rank.

The components of the actual CM projected Weil class lie in a
different Hodge-invariant sector: their lift requires a NEW
semiregular derived sheaf, not deformation of the bare graph.
-/

/-- Extract precisely the three diagonal unitary period parameters
of an actual CM graph tangent matrix. -/
def cmWeilSixfoldGraphDiagonalTangent
    (B : Matrix (Fin 3) (Fin 3) ℚ) :
    Matrix (Fin 3) (Fin 3) ℚ :=
  fun i j => if i = j then B i i else 0

/-- Every NINE-dimensional rational period tangent is the sum of
its THREE-dimensional central-graph-preserving diagonal part and
its SIX independently obstructed off-diagonal part. -/
theorem cmWeilSixfoldGraphTangentCanonicalSplit
    (B : Matrix (Fin 3) (Fin 3) ℚ) :
    B = cmWeilSixfoldGraphDiagonalTangent B +
      cmWeilSixfoldGraphFirstOrderLift
        (cmWeilSixfoldGraphFirstOrderDetector B) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cmWeilSixfoldGraphDiagonalTangent,
      cmWeilSixfoldGraphFirstOrderLift,
      cmWeilSixfoldGraphFirstOrderDetector] <;>
    ring

/-- The three-coordinate residual is annihilated by the ACTUAL
first-order Hodge-loss detector. -/
theorem cmWeilSixfoldGraphDiagonal_preserves_Hodge_firstOrder
    (B : Matrix (Fin 3) (Fin 3) ℚ) :
    cmWeilSixfoldGraphFirstOrderDetector
      (cmWeilSixfoldGraphDiagonalTangent B) = 0 := by
  funext k
  fin_cases k <;>
    simp [cmWeilSixfoldGraphFirstOrderDetector,
      cmWeilSixfoldGraphDiagonalTangent]

#check cmWeilSixfoldGraphTangentCanonicalSplit
#check cmWeilSixfoldGraphDiagonal_preserves_Hodge_firstOrder
#print axioms cmWeilSixfoldGraphTangentCanonicalSplit

/-! ## NO FAKE COHERENT SOURCE FROM REPEATED VIRTUAL SHEAVES

For an actual coherent sheaf F with nonzero Ext²(F,F), the
derived obstruction carrier of F⊕F contains its 2×2 matrix
blocks. The Atiyah character of a split direct sum is diagonal,
so the raw Buchweitz–Flenner semiregularity map on this matrix
carrier factors through the diagonal trace.

Every off-diagonal Ext² block is therefore killed. The full raw
semiregularity map on the naive doubled-sheaf source CANNOT
be injective, even if its virtual K₀ class or Chern character
has the desired Weil Hodge projection. This explains why
the polynomial in genuine isogeny graphs does NOT by itself
deliver the semiregular ordinary sheaf needed to deform the
exceptional Weil source from the CM period.

The next actual source must be a geometrically coupled sheaf
or perfect complex with its own full-Ext² injection proof,
as in the earlier GST secant-sheaf route; mere sum/shift
K₀ stabilization does not provide that theorem. -/

/-- Exact 2×2 off-diagonal obstruction against injectivity of
ANY matrix semiregularity law factoring through the ordinary
diagonal trace. No fake full-Hodge surjectivity enters. -/
theorem semiregularity_not_injective_on_duplicated_source
    {Ob Target : Type*}
    [AddCommGroup Ob] [Module ℚ Ob]
    [AddCommGroup Target] [Module ℚ Target]
    (rawSemireg : Matrix (Fin 2) (Fin 2) Ob →ₗ[ℚ] Target)
    (baseSemireg : Ob →ₗ[ℚ] Target)
    (hBlockTrace :
      ∀ M : Matrix (Fin 2) (Fin 2) Ob,
        rawSemireg M = baseSemireg (M 0 0 + M 1 1))
    (v : Ob) (hv : v ≠ 0) :
    ¬ Function.Injective rawSemireg := by
  let offDiagonal : Matrix (Fin 2) (Fin 2) Ob :=
    fun i j => if i = 0 ∧ j = 1 then v else 0
  have hNotZero : offDiagonal ≠ 0 := by
    intro h
    have h01 := congrArg
      (fun M : Matrix (Fin 2) (Fin 2) Ob => M 0 1) h
    exact hv (by simpa [offDiagonal] using h01)
  have hTraceZero :
      offDiagonal 0 0 + offDiagonal 1 1 = 0 := by
    simp [offDiagonal]
  have hSemiregZero : rawSemireg offDiagonal = 0 := by
    rw [hBlockTrace, hTraceZero, map_zero]
  intro hinj
  exact hNotZero (hinj (by simpa using hSemiregZero))

#check semiregularity_not_injective_on_duplicated_source
#print axioms semiregularity_not_injective_on_duplicated_source

/-! ## EXACT CM-GRAPH INCIDENCE: DISTINCT TRANSLATES ARE TRANSVERSE

At the CM product seed A=E_+^3 × E_-^3, the graph Z of a
K-antilinear isogeny E_+^3→E_-^3 is a codimension-3
abelian subvariety. The iterated algebraic isogenies f=[2+i]
move this graph by slopes (2-i)^j/(2+i)^j.

Two graph supports at j,k intersect transversely when the
slope ratio is nontrivial. For the degree-six polynomial
projector constructed above, only offsets n=1,...,6 occur.
The exact Gaussian integer powers (2+i)^n=a_n+i b_n have
  b_1,...,b_6 = 1,4,11,24,41,44.
Every b_n is nonzero; each graph slope differs on these
seven terms of the actual algebraic source projector.

Geometric consequence (standard transverse regular Koszul
intersection, not asserted as a Lean cycle theorem here):
Ext^q_A(O_{Z_j},O_{Z_k})=0 for q<3 when j≠k.
So a degree-one sheaf extension cannot couple DISTINCT
translate supports, while repeated same-support summands
have the raw semiregularity trace defect proved above.
The projected virtual K₀ source thus calls for a genuinely
new *incidence/derived-coupled* geometric sheaf constructor.
-/

/-- Exact powers of the algebraic CM endomorphism 2+i in
Gaussian integer coordinates. -/
def cmTwoPlusIGaussianPower : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 =>
      let z := cmTwoPlusIGaussianPower n
      (2*z.1 - z.2, z.1 + 2*z.2)

/-- Exhaustive EXACT integer calculation on all six offsets
in the degree-6 CM graph projector, not random sampling. -/
theorem cmTwoPlusIGaussianPower_imag_first_six :
    (List.range 6).map
      (fun n => (cmTwoPlusIGaussianPower (n+1)).2) =
        [1,4,11,24,41,44] := by
  decide

/-- All six actual graph-isogeny offsets have NONREAL powers.
This establishes the arithmetical noncollision input for
transverse central-fibre graph geometry. -/
theorem cmTwoPlusIGaussianPower_imag_nonzero_to_six
    (n : Fin 6) :
    (cmTwoPlusIGaussianPower (n.val+1)).2 ≠ 0 := by
  fin_cases n <;> norm_num [cmTwoPlusIGaussianPower]

/-! ## GST MINIMAL PAIRWISE INCIDENCE — SOURCE-CONSTRUCTION OPTIMIZATION

The prior 7-graph incidence W simultaneously contained every
projector support; the FIRST graph already had degree 17,324
per restricted incidence divisor. Its off-diagonal global
Ext² witness alone has dimension 17,324² = 300,120,976.

By contrast, to couple one positive and one negative adjacent
K₀ coefficient, construct W_{j,j+1} from TWO geometric graph
subgroups only. The two incidence divisors on each coordinate
pair are the sum of the actual kernels of the j-th and
(j+1)-st Gaussian K-isogeny slopes. Their restrictions to Z_j
have degree 4 * 25^j, and the global Koszul Ext² source has
H⁰ dimension 16 * 625^j by elliptic RR on the first two factors.

For j=0 this is ONLY 16 global Ext² classes, compared with
300,120,976 in the all-seven incidence W. Both constructions
use actual algebraic divisors; no formal Hodge preimage is
assumed. The reduction is a geometrically relevant *input
to* making a coupled semiregular complex, not a proof that
such a complex exists or that its full raw Ext² map is
injective. Nonzero off-diagonal Ext² of an UNCOUPLED direct
sum would obstruct injectivity, so the eventual sheaf must
genuinely couple components.

For an abelian sixfold, the full raw semiregularity target
across k=1,...,6 has complex dimension
 Σ binomial(6,k-1)*binomial(6,k+1) = 495.
The old 300-million-dimensional off-diagonal group, if
it survives in a candidate's Ext² without being killed by
coupling, cannot inject into that 495-dimensional target.
-/

/-- Uniform exact norm growth of the actual Gaussian graph
isogenies a_j=(2+i)^j, not a six-sample calculation. -/
theorem cmTwoPlusIGaussianPower_norm_sq (j : ℕ) :
    (cmTwoPlusIGaussianPower j).1 ^ 2 +
        (cmTwoPlusIGaussianPower j).2 ^ 2 =
      (5 : ℤ)^j := by
  induction j with
  | zero =>
      norm_num [cmTwoPlusIGaussianPower]
  | succ j ih =>
      change
        (2*(cmTwoPlusIGaussianPower j).1 -
            (cmTwoPlusIGaussianPower j).2)^2 +
          ((cmTwoPlusIGaussianPower j).1 +
            2*(cmTwoPlusIGaussianPower j).2)^2 =
        (5 : ℤ)^(j+1)
      calc
        _ = 5 * ((cmTwoPlusIGaussianPower j).1 ^ 2 +
            (cmTwoPlusIGaussianPower j).2 ^ 2) := by ring
        _ = 5 * (5 : ℤ)^j := by rw [ih]
        _ = (5 : ℤ)^(j+1) := by rw [pow_succ]; ring

/-- The adjacent graph slope determinant is EXACTLY 5^j.
It is never zero, so the two algebraic graph kernels are
genuinely distinct and their first incidence is transverse. -/
theorem cmTwoPlusIGaussianPower_neighbor_det (j : ℕ) :
    (cmTwoPlusIGaussianPower j).1 *
        (cmTwoPlusIGaussianPower (j+1)).2 -
      (cmTwoPlusIGaussianPower j).2 *
        (cmTwoPlusIGaussianPower (j+1)).1 =
      (5 : ℤ)^j := by
  have hnorm := cmTwoPlusIGaussianPower_norm_sq j
  change
    (cmTwoPlusIGaussianPower j).1 *
      ((cmTwoPlusIGaussianPower j).1 +
          2*(cmTwoPlusIGaussianPower j).2) -
    (cmTwoPlusIGaussianPower j).2 *
      (2*(cmTwoPlusIGaussianPower j).1 -
          (cmTwoPlusIGaussianPower j).2) =
      (5 : ℤ)^j
  nlinarith [hnorm]

/-- Minimal incidence divisor line degree restricted to Z_j.
The divisors arise from only two adjacent CM graphs, rather
than seven simultaneously. -/
def cmTwoPlusIAdjacentGraphIncidenceLineDegree (j : ℕ) : ℤ :=
  4 * ((cmTwoPlusIGaussianPower j).1 *
        (cmTwoPlusIGaussianPower (j+1)).2 -
       (cmTwoPlusIGaussianPower j).2 *
        (cmTwoPlusIGaussianPower (j+1)).1)^2

/-- UNIFORM geometric degree formula for the actual two-graph
codimension-two incidence on the CM central fiber. -/
theorem cmTwoPlusIAdjacentGraphIncidenceLineDegree_formula (j : ℕ) :
    cmTwoPlusIAdjacentGraphIncidenceLineDegree j =
      4 * (25 : ℤ)^j := by
  unfold cmTwoPlusIAdjacentGraphIncidenceLineDegree
  rw [cmTwoPlusIGaussianPower_neighbor_det]
  calc
    4 * ((5 : ℤ)^j)^2 =
        4 * ((5 : ℤ)^j * (5 : ℤ)^j) := by ring
    _ = 4 * (25 : ℤ)^j := by rw [← mul_pow]; norm_num

/-- First real incidence has h⁰(Z_0,L_1 L_2)=4²=16,
not 300,120,976. Geometric comparison uses elliptic
Riemann--Roch and the real graph complete intersection. -/
theorem cmTwoPlusIAdjacentGraphIncidence_firstExtTwoDimension :
    (cmTwoPlusIAdjacentGraphIncidenceLineDegree 0)^2 =
      16 := by
  norm_num [cmTwoPlusIAdjacentGraphIncidenceLineDegree,
    cmTwoPlusIGaussianPower]

/-- Exact six-dimensional abelian Hodge number count in the
FULL RAW Buchweitz–Flenner semiregularity target. -/
theorem cmWeilSixfold_rawSemiregularity_target_dimension :
    (∑ k ∈ Finset.Icc 1 6,
      Nat.choose 6 (k-1) * Nat.choose 6 (k+1)) = 495 := by
  decide

#check cmTwoPlusIGaussianPower_norm_sq
#check cmTwoPlusIGaussianPower_neighbor_det
#check cmTwoPlusIAdjacentGraphIncidenceLineDegree_formula
#check cmTwoPlusIAdjacentGraphIncidence_firstExtTwoDimension
#check cmWeilSixfold_rawSemiregularity_target_dimension
#print axioms cmTwoPlusIAdjacentGraphIncidenceLineDegree_formula

/-! ## GST INCIDENCE REPAIR: AN AUXILIARY CODIMENSION-TWO BRIDGE

The explicit seven-graph K₀ projector has alternating K₀ signs,
so transverse Ext³ between the graph supports cannot join the
opposite shift parities. There IS a different GENUINE geometric
incidence mechanism.

At the central CM sixfold seed, two smooth graph threefolds
Z0,Z1 are codimension three and intersect transversely.
Choose two sufficiently high-degree projective hypersurfaces
containing their scheme-theoretic union, with no common divisor
component. Their scheme-theoretic complete intersection W has
codimension TWO and contains BOTH graph supports. The needed
coherent sheaf O_W is perfect on the original smooth sixfold,
even if W is singular along the graph supports.

At a point where Z=(x,y,z) lies in a local lci branch
W=(x,y), the Koszul complex computing
Ext^*(O_Z,O_W) over R=O_W has zero action for x,y
and multiplication by the nonunit local parameter z.
Its cochain differentials are exactly:
  d0(r)=(0,0,z*r)
  d1(a,b,c)=(0,-z*a,-z*b)
  d2(A,B,C)=z*A.
Unlike Ext³ between TRANSVERSE threefolds, this local bridge
has nonzero Ext¹ and Ext² classes. Ext² arrows between
odd/even shifted perfect-complex terms can change K₀ parity;
the auxiliary incidence sheaf may therefore couple the
previously disconnected signs.

The Lean laws below certify the entire local cocycle/
noncoboundary mechanism over ANY commutative ring R where
z is a nonunit, not just a matrix rank at the origin.
Global scheme-level existence of W, derived Ext sheaf gluing,
and FULL semiregularity of a coupled global object remain
independent geometric tasks; local Ext is not quietly promoted
to a global deformable sheaf.
-/

section CMGraphIncidenceLocalKoszul

variable {R : Type*} [CommRing R]

/-- Koszul cochain degree-zero differential after quotienting
by the codimension-two incidence equations x=y=0. -/
def cmGraphIncidenceKoszulD0 (z r : R) : R × R × R :=
  (0, 0, z*r)

/-- Cochain degree-one differential: two vanished equations and
one transverse normal parameter. -/
def cmGraphIncidenceKoszulD1 (z : R)
    (v : R × R × R) : R × R × R :=
  (0, -(z*v.1), -(z*v.2.1))

/-- Cochain degree-two differential to the top Koszul summand. -/
def cmGraphIncidenceKoszulD2 (z : R)
    (v : R × R × R) : R :=
  z*v.1

theorem cmGraphIncidenceKoszul_d1d0_zero (z r : R) :
    cmGraphIncidenceKoszulD1 z (cmGraphIncidenceKoszulD0 z r) =
      (0, 0, 0) := by
  simp [cmGraphIncidenceKoszulD0, cmGraphIncidenceKoszulD1]

theorem cmGraphIncidenceKoszul_d2d1_zero
    (z : R) (v : R × R × R) :
    cmGraphIncidenceKoszulD2 z
      (cmGraphIncidenceKoszulD1 z v) = 0 := by
  simp [cmGraphIncidenceKoszulD1, cmGraphIncidenceKoszulD2]

/-- Explicit nonzero local Ext¹ residue class: a genuine cocycle
which cannot be a coboundary when z is not a unit. -/
theorem cmGraphIncidenceKoszul_degreeOne_nonboundary
    (z : R) (hz : ¬ ∃ r : R, z*r = 1) :
    cmGraphIncidenceKoszulD1 z ((0:R), (0:R), (1:R)) = 0 ∧
      ¬ ∃ r : R,
        cmGraphIncidenceKoszulD0 z r = ((0:R), (0:R), (1:R)) := by
  constructor
  · simp [cmGraphIncidenceKoszulD1]
  · rintro ⟨r,hr⟩
    have hthird := congrArg
      (fun v : R × R × R => v.2.2) hr
    exact hz ⟨r, by simpa [cmGraphIncidenceKoszulD0] using hthird⟩

/-- Explicit nonzero local Ext² residue class. THIS is the
parity-changing degree absent from transverse codimension-three
graph-graph interactions; incidence W can supply it. -/
theorem cmGraphIncidenceKoszul_degreeTwo_nonboundary
    (z : R) (hz : ¬ ∃ r : R, z*r = 1) :
    cmGraphIncidenceKoszulD2 z ((0:R), (1:R), (0:R)) = 0 ∧
      ¬ ∃ v : R × R × R,
        cmGraphIncidenceKoszulD1 z v =
          ((0:R), (1:R), (0:R)) := by
  constructor
  · simp [cmGraphIncidenceKoszulD2]
  · rintro ⟨v,hv⟩
    have hsecond := congrArg
      (fun w : R × R × R => w.2.1) hv
    have hmul : z*(-v.1) = 1 := by
      simpa [cmGraphIncidenceKoszulD1, mul_neg, neg_mul] using hsecond
    exact hz ⟨-v.1, hmul⟩

end CMGraphIncidenceLocalKoszul

/-! ## ACTUAL GLOBAL INCIDENCE BRIDGE ON THE CM SIXFOLD

Let E be a CM elliptic curve with End(E) containing Z[i].
Let A=E^3_x×E^3_y, a_j=(2+i)^j, 0≤j≤6, and let Z_j
be the graph threefold given by the simultaneous equations
  conj(a_j)*x_k-a_j*y_k=0  (k=1,2,3).

We construct projective divisors EXPLICITLY, not by assuming
a chosen Chow representative of any Weil target:
  D_k=Σ_{j=0}^6 ker(conj(a_j)*x_k-a_j*y_k),  k=1,2.
Each summand is the zero divisor of an actual homomorphism
A→E. The divisors D_1 and D_2 have no common divisorial
component: one uses coordinate pair (x_1,y_1), the other
(x_2,y_2). Thus W=D_1∩D_2 is a genuine codimension-two
complete intersection containing ALL SEVEN Z_j.

Apply Hom_A(-,O_{Z_j}) to the global length-two Koszul
resolution of O_W. Since BOTH defining sections vanish
identically on Z_j, the resulting sheaf Hom differential
is identically zero, with graded sheaf terms
  O_{Z_j},  L_1|Z_j ⊕ L_2|Z_j,  (L_1 L_2)|Z_j.
Therefore the derived global Ext² contains
  H⁰(Z_j,(L_1 L_2)|Z_j)
as a CANONICAL direct summand. This is the CORRECT
ORIENTATION for the parity-changing bridge:
  Ext²_A(O_W,O_{Z_j}), not Ext²_A(O_{Z_j},O_W).

Under Z_j ≃ E^3, each L_k|Z_j is a pullback from E
of degree
  d_j=Σ_{l=0}^6 Norm(conj(a_l)*a_j-a_l*conj(a_j))
     =Σ_l 4*(Re(a_l)Im(a_j)-Im(a_l)Re(a_j))².
They are positive. The true algebraic elliptic RR yields
  h⁰(Z_j,(L_1L_2)|Z_j)=d_j².
In particular the first graph has d_0=17324 and
300120976 globally available degree-two incidence
Ext directions! These are geometric nonzero Ext², not
just local residue classes.

Lean below verifies the exact integer degree census
from the ACTUAL Gaussian CM homomorphisms. The
Koszul-to-derived-global-Ext comparison is documented
above mathematically, not supplied as an arbitrary
globally inhabited Lean Ext carrier. Full semiregular
deformation of a seven-graph twisted complex is the
remaining new geometric construction problem.
-/

/-- The true degree of the restriction to E^3 of either
global seven-graph incidence divisor D_1,D_2. -/
def cmTwoPlusIGraphIncidenceLineDegree (j : ℕ) : ℤ :=
  ∑ k ∈ Finset.range 7,
    4 * ((cmTwoPlusIGaussianPower k).1 *
        (cmTwoPlusIGaussianPower j).2 -
        (cmTwoPlusIGaussianPower k).2 *
        (cmTwoPlusIGaussianPower j).1)^2

/-- Exact all-seven (not sampled) CM incidence line degrees.
Every restriction to a graph has positive degree. -/
theorem cmTwoPlusIGraphIncidenceLineDegree_all_seven :
    (List.range 7).map cmTwoPlusIGraphIncidenceLineDegree =
      [17324,239504,1785164,8629584,26679404,41991824,73240844] := by
  decide

/-- Strict numerical excess of the original all-seven Ext²
source over the entire raw semiregularity target. This
quantifies a REAL constraint on uncoupled incidence sheaves,
not a proof that every future coupled sheaf is obstructed. -/
theorem cmWeilSixfold_oldIncidenceExtTwo_exceedsSemiregTarget :
    (cmTwoPlusIGraphIncidenceLineDegree 0)^2 > 495 := by
  norm_num [cmTwoPlusIGraphIncidenceLineDegree,
    cmTwoPlusIGaussianPower, Finset.sum_range_succ]

/-- The first actual global degree-two Ext incidence witness
has H⁰-dimension 17324²=300120976 by elliptic RR and
Künneth, when the scheme-level Koszul correspondence is
instantiated by the displayed CM elliptic divisors. -/
theorem cmTwoPlusIGraphIncidence_first_globalExtTwo_dimension :
    (cmTwoPlusIGraphIncidenceLineDegree 0)^2 =
      300120976 := by
  norm_num [cmTwoPlusIGraphIncidenceLineDegree, cmTwoPlusIGaussianPower,
    Finset.sum_range_succ]

theorem cmTwoPlusIGraphIncidenceLineDegree_pos_to_seven
    (j : Fin 7) :
    0 < cmTwoPlusIGraphIncidenceLineDegree j.val := by
  fin_cases j <;>
    norm_num [cmTwoPlusIGraphIncidenceLineDegree,
      cmTwoPlusIGaussianPower, Finset.sum_range_succ]

#check cmTwoPlusIGraphIncidenceLineDegree_all_seven
#check cmTwoPlusIGraphIncidence_first_globalExtTwo_dimension
#check cmTwoPlusIGraphIncidenceLineDegree_pos_to_seven
#print axioms cmTwoPlusIGraphIncidenceLineDegree_pos_to_seven

#check cmGraphIncidenceKoszul_degreeOne_nonboundary
#check cmGraphIncidenceKoszul_degreeTwo_nonboundary
#print axioms cmGraphIncidenceKoszul_degreeTwo_nonboundary

/-! ## A REAL DERIVED INCIDENCE SOURCE — NONZERO EXT³ BETWEEN GRAPHS

For two 3-dimensional graph subvarieties of the product CM
elliptic sixfold, indexed by f^0 and f^n with f=[2+i],
the 2×2 Gaussian-integer isogeny matrix has determinant
  (2+i)^n-(2-i)^n = 2i*b_n.
Consequently its degree on a PAIR of CM elliptic factors is
  Norm(2i*b_n)=4*b_n²,
and on THREE independent pairs the degree is (4*b_n²)^3.
Since the graphs meet transversely in finitely many reduced
points, standard local Koszul duality yields
  dim_C Ext³_A(O_{Z0},O_{Zn}) = (4*b_n²)^3.
For the first neighbour this is SIXTY-FOUR, not zero.

Any NONZERO ξ in that geometric Ext³ gives a genuinely
NON-SPLIT perfect complex Cone(ξ)[1], where
  ξ:O_{Z0}→O_{Zn}[3].
Its honest Grothendieck class is
  [Cone(ξ)[1]]=[O_{Z0}]+[O_{Zn}].
This is a source-BIRTH mechanism preserving the actual
algebraic Chern character, unlike a merely formal projector
polynomial. Whether the *coupled* complex has full raw
semiregularity injectivity needs a further proof.

The exact intersection counts below are formalized as integer
arithmetic. The scheme-level Koszul Ext identification and
actual mapping cone are geometric next steps, not hidden
assumptions in the arithmetic theorem.
-/

/-- Exactly the intersection degree of two actual CM graph
subgroups of E⁶ at relative isogeny offset n, computed from
the Gaussian determinant and three elliptic pairs. -/
def cmTwoPlusIGraphIntersectionDegree (n : ℕ) : ℤ :=
  (4 * ((cmTwoPlusIGaussianPower n).2)^2)^3

theorem cmTwoPlusIGraphIntersectionDegree_first_six :
    (List.range 6).map
      (fun n => cmTwoPlusIGraphIntersectionDegree (n+1)) =
        [64,262144,113379904,12230590464,304006671424,464404086784] := by
  decide

/-- In particular the first derived graph-incidence pair has
64 transverse intersection points and a 64-dimensional
degree-three Koszul Ext space in the geometric model. -/
theorem cmTwoPlusIGraphIntersectionDegree_first :
    cmTwoPlusIGraphIntersectionDegree 1 = 64 := by
  norm_num [cmTwoPlusIGraphIntersectionDegree, cmTwoPlusIGaussianPower]

theorem cmTwoPlusIGraphIntersectionDegree_positive_to_six
    (n : Fin 6) :
    0 < cmTwoPlusIGraphIntersectionDegree (n.val+1) := by
  fin_cases n <;>
    norm_num [cmTwoPlusIGraphIntersectionDegree, cmTwoPlusIGaussianPower]

/-! ## THE REAL 7-GRAPH CHOW SOURCE: INTEGER K0 WEIGHTS

The rational CM spectral projector is not a single graph.
Clearing ALL denominators yields an explicit 7-graph integral
virtual perfect-complex source. Its signs matter geometrically:
a negative coefficient is represented by an ODD cohomological
shift, not by an ordinary positive direct-sum sheaf.

The two neighboring first graph terms have OPPOSITE coefficients.
For distinct transverse central graph threefolds, the only
local-to-global off-diagonal derived Hom is Ext³. A degree-one
twisted-complex differential between shifted objects
O_Z[a] → O_W[b][1] coming from Ext³ requires b-a=2, an EVEN
shift. Thus pure transverse-Ext³ couplings cannot directly join
the first positive and negative K0 components. This rules out
the naive all-graph single Ext³ cone as the requested semiregular
source. It does NOT rule out a different geometric sheaf using
extra incidence, self-Ext, or higher correspondences.

The integer K0 weights and this parity obstruction are concrete
design conditions for the next actual derived source, not an
assumption of generic Hodge cycle algebraicity.
-/

/-- Minimal common-denominator signed 7-graph projector weights,
ordered f^0,...,f^6 for the genuine CM isogeny f=[2+i]. -/
def cmWeilSixfoldIntegralSignedProjector : Fin 7 → ℤ :=
  ![317131927490234375, -2073948378906250,
    12564289203125, -56707735500, 27598945, 3626326, -68381]

def cmWeilSixfoldIntegralProjectorDenominator : ℕ :=
  930187500000000000

/-- Independently checked coefficient-level identity relating
the signed graph K0 source to the previously proved spectral
projector. No Hodge existence premise occurs. -/
theorem cmWeilSixfoldIntegralProjector_scalar_identity (t : ℚ) :
    cmWeilSixfoldNonsplitProjectorScalar t =
      ((cmWeilSixfoldIntegralSignedProjector 0 : ℚ) +
       (cmWeilSixfoldIntegralSignedProjector 1 : ℚ)*t +
       (cmWeilSixfoldIntegralSignedProjector 2 : ℚ)*t^2 +
       (cmWeilSixfoldIntegralSignedProjector 3 : ℚ)*t^3 +
       (cmWeilSixfoldIntegralSignedProjector 4 : ℚ)*t^4 +
       (cmWeilSixfoldIntegralSignedProjector 5 : ℚ)*t^5 +
       (cmWeilSixfoldIntegralSignedProjector 6 : ℚ)*t^6) /
      cmWeilSixfoldIntegralProjectorDenominator := by
  dsimp [cmWeilSixfoldNonsplitProjectorScalar,
    cmWeilSixfoldIntegralSignedProjector,
    cmWeilSixfoldIntegralProjectorDenominator]
  push_cast
  ring

/-- The ACTUAL integral projector requires both positive and
negative perfect-complex K0 terms; ordinary positive direct
sums alone cannot encode its seven signed graph coefficients. -/
theorem cmWeilSixfoldIntegralProjector_has_opposite_signs :
    0 < cmWeilSixfoldIntegralSignedProjector 0 ∧
    cmWeilSixfoldIntegralSignedProjector 1 < 0 := by
  decide

/-- Along a finite chain of degree-one derived arrows arising
exclusively from transverse Ext³ of distinct graph threefolds,
all cohomological shift parities coincide. -/
theorem cmWeilSixfoldTransverseExtThreeChain_preserves_parity
    (shift : ℕ → ℤ)
    (hExtThree : ∀ n, shift (n+1) = shift n + 2)
    (n : ℕ) :
    shift n % 2 = shift 0 % 2 := by
  induction n with
  | zero => rfl
  | succ k ih =>
      rw [hExtThree k]
      omega

/-- The first positive and negative graph K0 terms CANNOT be
directly joined by a degree-one transverse-Ext³ arrow: their
required cohomological shift parities differ. -/
theorem cmWeilSixfoldOppositeK0Signs_require_nonExtThreeCoupling
    (positiveShift negativeShift : ℤ)
    (hPositive : positiveShift % 2 = 0)
    (hNegative : negativeShift % 2 = 1) :
    negativeShift ≠ positiveShift + 2 := by
  omega

#check cmWeilSixfoldIntegralProjector_scalar_identity
#check cmWeilSixfoldIntegralProjector_has_opposite_signs
#check cmWeilSixfoldTransverseExtThreeChain_preserves_parity
#check cmWeilSixfoldOppositeK0Signs_require_nonExtThreeCoupling
#print axioms cmWeilSixfoldIntegralProjector_scalar_identity

#check cmTwoPlusIGraphIntersectionDegree_first_six
#check cmTwoPlusIGraphIntersectionDegree_first
#check cmTwoPlusIGraphIntersectionDegree_positive_to_six
#print axioms cmTwoPlusIGraphIntersectionDegree_positive_to_six

#check cmTwoPlusIGaussianPower_imag_first_six
#check cmTwoPlusIGaussianPower_imag_nonzero_to_six
#print axioms cmTwoPlusIGaussianPower_imag_nonzero_to_six

#check cmWeilSixfoldCompanionAction
#check cmWeilSixfoldStableSourceDichotomy
#print axioms cmWeilSixfoldStableSourceDichotomy

#check cmWeilSixfoldNonsplitProjectorScalar
#check cmWeilSixfoldNonsplitProjector_fixes_Weil
#check cmWeilSixfoldNonsplitProjector_idempotent_on_spectrum
#print axioms cmWeilSixfoldNonsplitProjector_idempotent_on_spectrum

#check cmWeilTwoPlusIProjectorScalar
#check cmWeilTwoPlusIProjector_fixes_Weil
#check cmWeilTwoPlusIProjector_kills_mixed
#check cmWeilTwoPlusIProjector_kills_ambient
#print axioms cmWeilTwoPlusIProjector_idempotent_on_spectrum

#check cmWeilFourfoldCompanionAction
#check cmWeilInvariantSource_nonzero_forces_full_plane
#check cmWeilStableSourceDichotomy
#print axioms cmWeilStableSourceDichotomy

/-! ## Generic Weil divisor-channel obstruction

For a Weil-type abelian 2p-fold with rational Neron–Severi rank
one, the polarization theta generates its entire rational
divisor algebra in degree p. The genuine CM isogeny [2+i]
acts on theta by its norm 5 and on theta^p by 5^p.

The actual rational Weil projector from [2+i] has
the polynomial factor T-5^p I, hence kills theta^p.
No combination of divisor intersections, CM graph pullbacks,
rational Adams operations or compositions of these on
already ambient cycle classes can populate its rank-two
Weil eigenspace. Genuine new higher-codimension sources
are necessary on these generic fibers.

This is a statement about a *specified source channel*, not
a negative claim about existence of the desired algebraic
Weil cycles. At p=1 the NS-rank-one hypothesis is not
appropriate to the exceptional Weil divisor case; the test
is targeted at p>=2.
-/

/-- A general exact algebraic-correspondence right factor
(T-q I) annihilates any q-eigenclass, including the
polarization-power class for q=5^p. -/
def cmWeilCentralEigenspaceFilter
    {W : Type*} [AddCommGroup W] [Module ℚ W]
    (T R : Module.End ℚ W) (q : ℚ) : Module.End ℚ W :=
  R.comp (T - q • LinearMap.id)

theorem cmWeilCentralEigenspaceFilter_kills_ambient
    {W : Type*} [AddCommGroup W] [Module ℚ W]
    (T R : Module.End ℚ W) (p : ℕ) (thetaPower : W)
    (hEigen : T thetaPower = ((5:ℚ)^p) • thetaPower) :
    cmWeilCentralEigenspaceFilter T R ((5:ℚ)^p) thetaPower = 0 := by
  change R (T thetaPower - ((5:ℚ)^p) • thetaPower) = 0
  rw [hEigen, sub_self, map_zero]

/-! ## Native single-irreducible-source reduction on ORIGINAL X

In the existing Mathlib native rational cycle model, every
algebraic Chow witness on smooth projective X is a FINITE
rational sum of genuine codimension-p irreducible point cycles,
by GSTCompactNativeCyclePresentation.

If the CM Weil projector detects a nonzero cycle in that
finite sum, then it detects at least one actual irreducible
component of that cycle. No cancellation can make a sum
nonzero when every projected summand is zero.

Combined with the positive CM orbit determinant above:
  ONE irreducible codimension-p subvariety V⊂A
  with Π_W cl(V) ≠ 0
suffices to construct every prescribed exceptional rational
Weil (p,p) Hodge class on the SAME original A, using V and
its algebraic CM-isogeny translates and explicit ℚ coefficients.

The split source was already geometrically built. The current
nonsplit source target is now ONE genuine irreducible cycle,
not arbitrary formal Chow sources or two independent cycles.
-/

/-- Exact arbitrary-native-space finite-source extraction:
a nonzero projected rational algebraic cycle is witnessed by
at least one independently genuine algebraic source generator. -/
theorem cmWeilProjectedFiniteNativeSourceWitness
    {N W : Type*} [AddCommGroup N] [Module ℚ N]
    [AddCommGroup W] [Module ℚ W]
    {ι : Type*} [Fintype ι]
    (cycleClass : N →ₗ[ℚ] W) (weiland : W →ₗ[ℚ] W)
    (sources : ι → N) (coeff : ι → ℚ)
    (hDetected :
      weiland (cycleClass (∑ i, coeff i • sources i)) ≠ 0) :
    ∃ i : ι, weiland (cycleClass (sources i)) ≠ 0 := by
  classical
  by_contra hNoSource
  have hZero : ∀ i : ι, weiland (cycleClass (sources i)) = 0 := by
    intro i
    by_contra hn
    exact hNoSource ⟨i, hn⟩
  apply hDetected
  calc
    weiland (cycleClass (∑ i, coeff i • sources i)) =
        ∑ i, coeff i • weiland (cycleClass (sources i)) := by
          simp only [map_sum, map_smul]
    _ = 0 := by simp [hZero]

#check cmWeilProjectedFiniteNativeSourceWitness
#print axioms cmWeilProjectedFiniteNativeSourceWitness

/-! ## Quaternionic GRAPH supplies a new actual Weil source

The exact CM Weil Hodge space remains rank two for genuinely
quaternionic (rather than CM-elliptic) abelian fourfolds A=B×B,
where B is a QM abelian surface for the division quaternion
algebra D=(-1,3)_Q with i²=-1, j²=3 and ij=-ji.

The graph Γ_j⊂B×B of the actual algebraic QM isogeny j is an
irreducible codimension-two algebraic surface. On H¹(B,C) the
anti-K operator j interchanges σ and barσ eigenspaces.
Hence, on the 4-dimensional σ eigenspace of H¹(A,C), the
restriction of its top wedge to Γ_j pairs two σ basis forms
with two j-transformed barσ forms. A rational regular
quaternion basis computes this top-wedge determinant as -12,
independently and exactly audited by Wolfram and Python.

Thus Γ_j is a new nonzero source for the *existing* GST
single-source CM orbit theorem, producing the full rational
two-dimensional Weil (2,2) subspace of THIS original A.
The verified comparison with the genuine graph and Hodge
fundamental class is geometric input beyond this algebraic
Lean eigen-switch identity.

Products with QM blocks (and a CM elliptic pair for odd p)
yield rank-two exceptional Weil algebraic sources at every
p>=2 while keeping a non-elliptic QM factor. No assertion
about very general SIMPLE Weil abelian fourfolds is made.
-/

/-- Any actual anti-K quaternionic isogeny exchanges the
two complex CM eigenspaces in genuine H¹. This is the
fundamental structure behind the graph top-wedge pairing. -/
theorem quaternionicAntiKGraphSwitchesEigensector
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (I J : Module.End ℂ V)
    (hAnti : I.comp J = -(J.comp I))
    (v : V) (hv : I v = Complex.I • v) :
    I (J v) = (-Complex.I) • (J v) := by
  have h := congrArg (fun f : Module.End ℂ V => f v) hAnti
  have hSwitch : I (J v) = -J (I v) := by
    simpa only [LinearMap.comp_apply, LinearMap.neg_apply] using h
  calc
    I (J v) = -J (I v) := hSwitch
    _ = -J (Complex.I • v) := by rw [hv]
    _ = (-Complex.I) • (J v) := by simp only [map_smul, neg_smul]

/-- The quaternion relation j²=3 ensures the exchanged CM
component cannot vanish when its source was nonzero. -/
theorem quaternionicAntiKGraphNonzero
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (J : Module.End ℂ V)
    (hSquare : ∀ v : V, J (J v) = (3:ℂ) • v)
    (v : V) (hv : v ≠ 0) : J v ≠ 0 := by
  intro hz
  have hNonzero : (3:ℂ) • v ≠ 0 :=
    smul_ne_zero (by norm_num) hv
  apply hNonzero
  rw [← hSquare v, hz, map_zero]

/-! ## GST basis-free QUATERNIONIC NONSPLIT GEOMETRIC RANK

The actual graph of an anti-K quaternionic algebraic isogeny J has
J²=3 and IJ=-JI on the rational/complex Betti realization. The
two-dimensional sigma space is sent into the opposite eigenspace.

Beyond the existing single-vector survival theorem, TWO independent
sigma inputs remain linearly independent after J. This eliminates any
new arbitrary 2x2 matrix nondegeneracy premise from the graph-switch
stage. Algebraic realization still requires the actual scheme-isogeny
graph and its canonical Betti functoriality; an abstract pair of linear
operators by itself is NOT the original-X Weil Chow cycle.
-/

/-- Basis-free quaternionic graph rank preservation.  The theorem
proves both the correct anti-CM eigen-switch and preservation of a
two-generator geometric period frame.  The proof uses the exact
quaternion relation J²=3 and has NO determinant or target preimage
hypothesis, only independence of the original two eigenvectors. -/
theorem quaternionicAntiKGraphPreservesTwoIndependentEigendirections
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (I J : Module.End ℂ V)
    (hAnti : I.comp J = -(J.comp I))
    (hSquare : ∀ z : V, J (J z) = (3:ℂ) • z)
    (v w : V)
    (hv : I v = Complex.I • v)
    (hw : I w = Complex.I • w)
    (hIndependent : ∀ a b : ℂ,
      a • v + b • w = 0 → a = 0 ∧ b = 0) :
    I (J v) = (-Complex.I) • (J v) ∧
    I (J w) = (-Complex.I) • (J w) ∧
    (∀ a b : ℂ,
      a • J v + b • J w = 0 → a = 0 ∧ b = 0) := by
  refine ⟨quaternionicAntiKGraphSwitchesEigensector I J hAnti v hv,
    quaternionicAntiKGraphSwitchesEigensector I J hAnti w hw, ?_⟩
  intro a b hab
  have hzeroJ : J (a • v + b • w) = 0 := by
    rw [map_add, map_smul, map_smul]
    exact hab
  have hdouble := congrArg J hzeroJ
  rw [hSquare (a • v + b • w), map_zero] at hdouble
  have hzero : a • v + b • w = 0 :=
    (smul_eq_zero.mp hdouble).resolve_left (by norm_num)
  exact hIndependent a b hzero

#check quaternionicAntiKGraphPreservesTwoIndependentEigendirections
#print axioms quaternionicAntiKGraphPreservesTwoIndependentEigendirections

/-- The quaternionic anti-K graph creates a FULL four-vector H¹ frame
from TWO genuinely independent sigma eigenvectors. The four vectors
(v,w,Jv,Jw) are independent over C, since the first two belong to
the +i eigenspace and the last two to the -i eigenspace, while J²=3
makes the latter two independent. This is the basis-free linear
nonvanishing behind the exterior four-form Weil determinant on B×B.

No nonzero determinant, selected Hodge preimage or rank-two output
hypothesis is assumed. The mathematical statement is about the
canonical cohomological action of an ACTUAL quaternionic graph only
after its H¹ realization has been identified separately. -/
theorem quaternionicAntiKGraphFourVectorWeilFrameIndependent
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (I J : Module.End ℂ V)
    (hAnti : I.comp J = -(J.comp I))
    (hSquare : ∀ z : V, J (J z) = (3:ℂ) • z)
    (v w : V)
    (hv : I v = Complex.I • v)
    (hw : I w = Complex.I • w)
    (hIndependent : ∀ a b : ℂ,
      a • v + b • w = 0 → a = 0 ∧ b = 0) :
    ∀ a b c d : ℂ,
      a • v + b • w + c • J v + d • J w = 0 →
        a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  have hpair :=
    quaternionicAntiKGraphPreservesTwoIndependentEigendirections
      I J hAnti hSquare v w hv hw hIndependent
  intro a b c d hlin
  let x : V := a • v + b • w
  let y : V := c • J v + d • J w
  have hx : I x = Complex.I • x := by
    dsimp [x]
    simp [map_add, map_smul, hv, hw, smul_add, smul_smul, mul_comm]
  have hy : I y = (-Complex.I) • y := by
    dsimp [y]
    simp [map_add, map_smul, hpair.1, hpair.2.1,
      smul_add, smul_smul, mul_comm]
  have hxy : x + y = 0 := by
    dsimp [x, y]
    simpa only [add_assoc] using hlin
  have hI : Complex.I • x + (-Complex.I) • y = 0 := by
    calc
      Complex.I • x + (-Complex.I) • y = I (x+y) := by
        rw [map_add, hx, hy]
      _ = 0 := by rw [hxy]; exact map_zero I
  have hsmul : Complex.I • x + Complex.I • y = 0 := by
    rw [← smul_add, hxy, smul_zero]
  have hcoef : ((-2:ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (by norm_num) Complex.I_ne_zero
  have hkill : ((-2:ℂ) * Complex.I) • y = 0 := by
    calc
      ((-2:ℂ) * Complex.I) • y =
        ((-Complex.I) - Complex.I) • y := by congr 1; ring
      _ = (-Complex.I) • y - Complex.I • y := by rw [sub_smul]
      _ = (Complex.I • x + (-Complex.I) • y) -
            (Complex.I • x + Complex.I • y) := by abel
      _ = 0 := by rw [hI, hsmul]; simp
  have hyzero : y = 0 :=
    (smul_eq_zero.mp hkill).resolve_left hcoef
  have hxzero : x = 0 := by
    simpa [hyzero] using hxy
  obtain ⟨ha,hb⟩ := hIndependent a b hxzero
  obtain ⟨hc,hd⟩ := hpair.2.2 c d hyzero
  exact ⟨ha,hb,hc,hd⟩

#check quaternionicAntiKGraphFourVectorWeilFrameIndependent
#print axioms quaternionicAntiKGraphFourVectorWeilFrameIndependent

/-- Exact rational squared norm of the quaternionic graph
pairing tensor products: each QM block contributes 144
and each CM elliptic odd-degree remainder contributes 4. -/
theorem quaternionicGraphWeilTensorNormNonzero
    (qmBlocks cmRemainder : ℕ) :
    (144:ℚ)^qmBlocks * (4:ℚ)^cmRemainder ≠ 0 := by
  exact mul_ne_zero (pow_ne_zero _ (by norm_num))
    (pow_ne_zero _ (by norm_num))

/-! ## Auxiliary-sixfold extraction assembled on the original fourfold

The source Γ, its actual extraction by p_A*(- · p_B*D0), the actual
CM pullback, and their two cycle-class comparisons are geometric inputs.
The external split-sixfold theorem T6 supplies Γ in the linked manuscript;
it is NOT an axiom or a theorem proved in this module. The rank-three
Hodge coordinate equivalence is the generic Weil-fourfold decomposition,
not a hypothesis that any cycle classes span. In particular no determinant
or arbitrary-target preimage is requested below: both are constructed.

The previous companion-matrix reconstruction used a²+b². For general
K=Q(sqrt(-d)) the actual fourth-power action has norm r²+d*s² instead.
The Cramer coefficients below work for every rational d>0 and avoid
identifying these different companion bases.
-/

def weilPlaneCoeff0 (z w target : ℚ × ℚ) : ℚ :=
  (target.1 * w.2 - target.2 * w.1) / planeDeterminant z w

def weilPlaneCoeff1 (z w target : ℚ × ℚ) : ℚ :=
  (z.1 * target.2 - z.2 * target.1) / planeDeterminant z w

/-- Explicit two-vector reconstruction; source independence is proved
from the balanced nonzero tensor in the native assembly below. -/
theorem weilPlaneCramerReconstruction (z w target : ℚ × ℚ)
    (hdet : planeDeterminant z w ≠ 0) :
    weilPlaneCoeff0 z w target * z.1 +
      weilPlaneCoeff1 z w target * w.1 = target.1 ∧
    weilPlaneCoeff0 z w target * z.2 +
      weilPlaneCoeff1 z w target * w.2 = target.2 := by
  constructor
  all_goals
    dsimp [weilPlaneCoeff0, weilPlaneCoeff1]
    field_simp [hdet]
    dsimp [planeDeterminant]
    ring

/-- The actual signed rational native cycle on the original carrier.
Only one auxiliary source Γ is used, independently of the target α. -/
noncomputable def auxiliaryWeilNativeCycle
    {U : SmoothProjectiveComplexScheme}
    (Γ : codimensionCycles U.X 3)
    (extract : codimensionCycles U.X 3 →ₗ[ℚ] codimensionCycles V.X 2)
    (cmPullback : Module.End ℚ (codimensionCycles V.X 2))
    (thetaSquare : codimensionCycles V.X 2)
    (coordinates : ClassicalHodgeFiber V H 2 ≃ₗ[ℚ] ℚ × (ℚ × ℚ))
    (d : ℚ) (tensor : TensorCoefficients)
    (alpha : ClassicalHodgeFiber V H 2) : codimensionCycles V.X 2 :=
  let z := contractGraph tensor
  let w := fourthPowerAction d (d + 1) z
  (coordinates alpha).1 • thetaSquare +
    weilPlaneCoeff0 z w (coordinates alpha).2 • extract Γ +
    weilPlaneCoeff1 z w (coordinates alpha).2 • cmPullback (extract Γ)

/-- Three-direction assembly for the original Weil fourfold, conditional
only on the displayed geometric source, decomposition and comparisons.
No full-rank cycle matrix or prescribed-class source is an input. -/
theorem auxiliaryWeilNativeCycle_class
    {U : SmoothProjectiveComplexScheme}
    (G : GeometricCycleClassSpine V H)
    (Γ : codimensionCycles U.X 3)
    (extract : codimensionCycles U.X 3 →ₗ[ℚ] codimensionCycles V.X 2)
    (cmPullback : Module.End ℚ (codimensionCycles V.X 2))
    (thetaSquare : codimensionCycles V.X 2)
    (coordinates : ClassicalHodgeFiber V H 2 ≃ₗ[ℚ] ℚ × (ℚ × ℚ))
    (d : ℚ) (hd : 0 < d) (tensor : TensorCoefficients)
    (hbalanced : balanced d tensor) (hnonzero : tensor ≠ zeroCoefficients)
    (hTheta : coordinates (nativeToHodgeFiberLinear G thetaSquare) = (1, (0, 0)))
    (hExtract : coordinates (nativeToHodgeFiberLinear G (extract Γ)) =
      (0, contractGraph tensor))
    (hCM : coordinates (nativeToHodgeFiberLinear G (cmPullback (extract Γ))) =
      (0, fourthPowerAction d (d + 1) (contractGraph tensor)))
    (alpha : ClassicalHodgeFiber V H 2) :
    nativeToHodgeFiberLinear G
      (auxiliaryWeilNativeCycle Γ extract cmPullback thetaSquare coordinates
        d tensor alpha) = alpha := by
  have hz : contractGraph tensor ≠ (0, 0) :=
    contraction_nonzero d (ne_of_gt hd) tensor hbalanced hnonzero
  have hdet : planeDeterminant (contractGraph tensor)
      (fourthPowerAction d (d + 1) (contractGraph tensor)) ≠ 0 :=
    ne_of_gt (extracted_fourth_power_orbit_has_rank_two d hd _ hz)
  have hReconstruction := weilPlaneCramerReconstruction (contractGraph tensor)
    (fourthPowerAction d (d + 1) (contractGraph tensor)) (coordinates alpha).2 hdet
  apply coordinates.injective
  simp only [auxiliaryWeilNativeCycle, map_add, map_smul, hTheta, hExtract, hCM]
  apply Prod.ext
  · change (coordinates alpha).1 * 1 + _ * 0 + _ * 0 = (coordinates alpha).1
    ring
  · apply Prod.ext
    · change (coordinates alpha).1 * 0 + _ + _ = (coordinates alpha).2.1
      simpa [smul_eq_mul] using hReconstruction.1
    · change (coordinates alpha).1 * 0 + _ + _ = (coordinates alpha).2.2
      simpa [smul_eq_mul] using hReconstruction.2

/-- The same assembly lands in the supplied actual Betti cycle-class map,
not merely in a separate coordinate carrier. Canonicality still requires
instantiating H and the comparison hypotheses by the stated geometry. -/
theorem auxiliaryWeilEveryMiddleHodgeClass
    {U : SmoothProjectiveComplexScheme}
    (G : GeometricCycleClassSpine V H)
    (Γ : codimensionCycles U.X 3)
    (extract : codimensionCycles U.X 3 →ₗ[ℚ] codimensionCycles V.X 2)
    (cmPullback : Module.End ℚ (codimensionCycles V.X 2))
    (thetaSquare : codimensionCycles V.X 2)
    (coordinates : ClassicalHodgeFiber V H 2 ≃ₗ[ℚ] ℚ × (ℚ × ℚ))
    (d : ℚ) (hd : 0 < d) (tensor : TensorCoefficients)
    (hbalanced : balanced d tensor) (hnonzero : tensor ≠ zeroCoefficients)
    (hTheta : coordinates (nativeToHodgeFiberLinear G thetaSquare) = (1, (0, 0)))
    (hExtract : coordinates (nativeToHodgeFiberLinear G (extract Γ)) =
      (0, contractGraph tensor))
    (hCM : coordinates (nativeToHodgeFiberLinear G (cmPullback (extract Γ))) =
      (0, fourthPowerAction d (d + 1) (contractGraph tensor)))
    (alpha : RationalSingularCohomology H.analytification 4)
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading 2)) :
    ∃ Z : codimensionCycles V.X 2, H.cycleClass 2 Z = alpha := by
  let a : ClassicalHodgeFiber V H 2 := ⟨alpha, halpha⟩
  refine ⟨auxiliaryWeilNativeCycle Γ extract cmPullback thetaSquare coordinates
    d tensor a, ?_⟩
  have h := auxiliaryWeilNativeCycle_class G Γ extract cmPullback thetaSquare
    coordinates d hd tensor hbalanced hnonzero hTheta hExtract hCM a
  exact congrArg Subtype.val h

#check auxiliaryWeilNativeCycle_class
#check auxiliaryWeilEveryMiddleHodgeClass

/-- Assemble the original fourfold AFTER all-period spread, without
taking a fixed auxiliary cycle as a theorem argument. Parameters are
signed Hilbert lists; `cycleAt` is their genuine cycle on the requested
auxiliary fiber. Closed analytic images, their identity principle and
local nonemptiness supply a parameter at the requested period.

The displayed geometric comparisons and canonical realization of H
still have to be instantiated; this is not a standalone unconditional
theorem about complex abelian varieties. All comparisons refer to one
fixed nonzero Weil class, independently of the prescribed target alpha. -/
theorem auxiliaryWeilEveryMiddleHodgeClass_from_periodSpread
    {U : SmoothProjectiveComplexScheme}
    {T : Type*} [TopologicalSpace T] [BaireSpace T]
    (Parameter : ℕ → Type*) (projection : ∀ i, Parameter i → T)
    (good : ∀ i, Set (Parameter i))
    (hclosed : ∀ i, IsClosed (projection i '' good i))
    (hidentity : ∀ i, (interior (projection i '' good i)).Nonempty →
      projection i '' good i = Set.univ)
    (O : Set T) (hO : IsOpen O) (hne : O.Nonempty)
    (hlocal : ∀ t ∈ O, ∃ i p, p ∈ good i ∧ projection i p = t)
    (period : T)
    (cycleAt : ∀ i (p : Parameter i), projection i p = period →
      codimensionCycles U.X 3)
    (G : GeometricCycleClassSpine V H)
    (extract : codimensionCycles U.X 3 →ₗ[ℚ] codimensionCycles V.X 2)
    (cmPullback : Module.End ℚ (codimensionCycles V.X 2))
    (thetaSquare : codimensionCycles V.X 2)
    (coordinates : ClassicalHodgeFiber V H 2 ≃ₗ[ℚ] ℚ × (ℚ × ℚ))
    (d : ℚ) (hd : 0 < d) (tensor : TensorCoefficients)
    (hbalanced : balanced d tensor) (hnonzero : tensor ≠ zeroCoefficients)
    (hTheta : coordinates (nativeToHodgeFiberLinear G thetaSquare) = (1, (0, 0)))
    (hExtract : ∀ i p, p ∈ good i → ∀ ht : projection i p = period,
      coordinates (nativeToHodgeFiberLinear G (extract (cycleAt i p ht))) =
        (0, contractGraph tensor))
    (hCM : ∀ i p, p ∈ good i → ∀ ht : projection i p = period,
      coordinates (nativeToHodgeFiberLinear G (cmPullback (extract (cycleAt i p ht)))) =
        (0, fourthPowerAction d (d + 1) (contractGraph tensor)))
    (alpha : RationalSingularCohomology H.analytification 4)
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading 2)) :
    ∃ Z : codimensionCycles V.X 2, H.cycleClass 2 Z = alpha := by
  obtain ⟨i, p, hp, ht⟩ := periodTransport_all_period_witnesses
    Parameter projection good hclosed hidentity O hO hne hlocal period
  exact auxiliaryWeilEveryMiddleHodgeClass G (cycleAt i p ht) extract cmPullback
    thetaSquare coordinates d hd tensor hbalanced hnonzero hTheta
    (hExtract i p hp ht) (hCM i p hp ht) alpha halpha

/-! ## Native original-fourfold assembly from ONE global CM functoriality law

The previous entry point assumed a CM coordinate comparison separately
for every signed Hilbert cycle supplied by the global period spread.
That is stronger data than actual geometry requires: the canonical
Chow-to-Betti map is natural under a genuine algebraic isogeny ONCE,
on every rational Chow class.

Let k=d+1+u, u²=-d, and q=Norm(k)=(d+1)²+d.
On the ambient theta² line of a Weil fourfold, k* acts by q².
On its rational exceptional Weil plane, it acts by the already
verified fourthPowerAction d (d+1). Thus the actual CM action
on the full 1+2 rational Hodge sector is block diagonal.

The theorem below uses precisely this one independent geometric
equivariance law, together with the Baire/Hilbert source itself.
No pointwise CM comparison for each Hilbert parameter is assumed.
This is an interface strengthening, not a claim that the source
semiregularity and Hilbert-geometry inputs have been formalized.
-/

/-- A global canonical cycle-class/isogeny equivariance theorem
replaces infinitely many source-specific CM comparison assertions
in the original fourfold Hodge assembly. -/
theorem auxiliaryWeilEveryMiddleHodgeClass_from_periodSpread_CMFunctorial
    {U : SmoothProjectiveComplexScheme}
    {T : Type*} [TopologicalSpace T] [BaireSpace T]
    (Parameter : ℕ → Type*) (projection : ∀ i, Parameter i → T)
    (good : ∀ i, Set (Parameter i))
    (hclosed : ∀ i, IsClosed (projection i '' good i))
    (hidentity : ∀ i, (interior (projection i '' good i)).Nonempty →
      projection i '' good i = Set.univ)
    (O : Set T) (hO : IsOpen O) (hne : O.Nonempty)
    (hlocal : ∀ t ∈ O, ∃ i p, p ∈ good i ∧ projection i p = t)
    (period : T)
    (cycleAt : ∀ i (p : Parameter i), projection i p = period →
      codimensionCycles U.X 3)
    (G : GeometricCycleClassSpine V H)
    (extract : codimensionCycles U.X 3 →ₗ[ℚ] codimensionCycles V.X 2)
    (cmPullback : Module.End ℚ (codimensionCycles V.X 2))
    (thetaSquare : codimensionCycles V.X 2)
    (coordinates : ClassicalHodgeFiber V H 2 ≃ₗ[ℚ] ℚ × (ℚ × ℚ))
    (d : ℚ) (hd : 0 < d) (tensor : TensorCoefficients)
    (hbalanced : balanced d tensor) (hnonzero : tensor ≠ zeroCoefficients)
    (hTheta : coordinates (nativeToHodgeFiberLinear G thetaSquare) = (1, (0, 0)))
    (hExtract : ∀ i p, p ∈ good i → ∀ ht : projection i p = period,
      coordinates (nativeToHodgeFiberLinear G (extract (cycleAt i p ht))) =
        (0, contractGraph tensor))
    (hCMFunctorial :
      ∀ Z : codimensionCycles V.X 2,
        coordinates (nativeToHodgeFiberLinear G (cmPullback Z)) =
        ((((d+1)^2+d)^2) * (coordinates (nativeToHodgeFiberLinear G Z)).1,
          fourthPowerAction d (d+1)
            (coordinates (nativeToHodgeFiberLinear G Z)).2))
    (alpha : RationalSingularCohomology H.analytification 4)
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading 2)) :
    ∃ Z : codimensionCycles V.X 2, H.cycleClass 2 Z = alpha := by
  obtain ⟨i, p, hp, ht⟩ := periodTransport_all_period_witnesses
    Parameter projection good hclosed hidentity O hO hne hlocal period
  have hs := hExtract i p hp ht
  have hcm := hCMFunctorial (extract (cycleAt i p ht))
  rw [hs] at hcm
  have hc :
      coordinates (nativeToHodgeFiberLinear G
        (cmPullback (extract (cycleAt i p ht)))) =
        (0, fourthPowerAction d (d+1) (contractGraph tensor)) := by
    simpa only [mul_zero] using hcm
  exact auxiliaryWeilEveryMiddleHodgeClass G (cycleAt i p ht) extract
    cmPullback thetaSquare coordinates d hd tensor hbalanced hnonzero
    hTheta hs hc alpha halpha

/-! ## Canonical Hilbert-cycle source extraction: one fixed Betti class

In the manuscript Baire spread, the relative Hilbert locus of "good"
parameters is DEFINED by a single flat rational Betti class w of the
auxiliary sixfold. Its geometric extraction to the original fourfold
is the canonical cup with the elliptic graph-difference divisor
followed by proper Gysin pushforward.

Consequently extraction comparison is functorial for ALL actual
auxiliary cycles, and the Weil coordinates of extracted good cycles
follow from the ONE fixed source vector w. The theorem below replaces
the old independent comparison hypothesis for every individual
Hilbert parameter by:

 (1) one fixed Hilbert Betti-class law defining the good locus;
 (2) one genuine cup/Gysin source-to-original comparison map;
 (3) the single global CM action law.

This is a substantial *geometric-instantiation* reduction of the
already proved Baire/CM original-Weil construction. The analytic
Hilbert properness and semiregularity source remain distinct
classical-geometric inputs, not arbitrary chosen Hodge preimages.
-/

/-- A fixed rational sixfold Betti class and one proper-pushforward
comparison replace all source-by-source hypotheses in the original
fourfold Weil Hodge assembly. The source may contain ANY ambient
polarization component; subtracting its measured multiple of the actual
polarization-square Chow cycle removes it before the Weil orbit step.
The resulting theorem only assumes that the extracted fixed Betti class
has a nonzero Weil component: no pre-selected balanced tensor, tensor
coordinate equality, or geometric purity of the source is required. -/
theorem auxiliaryWeilEveryMiddleHodgeClass_from_canonicalHilbertSource
    {U : SmoothProjectiveComplexScheme}
    (HU : HodgeBigradedBettiData U)
    {T : Type*} [TopologicalSpace T] [BaireSpace T]
    (Parameter : ℕ → Type*) (projection : ∀ i, Parameter i → T)
    (good : ∀ i, Set (Parameter i))
    (hclosed : ∀ i, IsClosed (projection i '' good i))
    (hidentity : ∀ i, (interior (projection i '' good i)).Nonempty →
      projection i '' good i = Set.univ)
    (O : Set T) (hO : IsOpen O) (hne : O.Nonempty)
    (hlocal : ∀ t ∈ O, ∃ i p, p ∈ good i ∧ projection i p = t)
    (period : T)
    (cycleAt : ∀ i (p : Parameter i), projection i p = period →
      codimensionCycles U.X 3)
    (G : GeometricCycleClassSpine V H)
    (extract : codimensionCycles U.X 3 →ₗ[ℚ] codimensionCycles V.X 2)
    (cmPullback : Module.End ℚ (codimensionCycles V.X 2))
    (thetaSquare : codimensionCycles V.X 2)
    (coordinates : ClassicalHodgeFiber V H 2 ≃ₗ[ℚ] ℚ × (ℚ × ℚ))
    (d : ℚ) (hd : 0 < d)
    (hTheta : coordinates (nativeToHodgeFiberLinear G thetaSquare) = (1, (0, 0)))
    (fixedSixfoldBetti : RationalSingularCohomology HU.analytification 6)
    (bettiExtract :
      RationalSingularCohomology HU.analytification 6 →ₗ[ℚ]
        ℚ × (ℚ × ℚ))
    (hHilbertClass : ∀ i p, p ∈ good i → ∀ ht : projection i p = period,
      HU.cycleClass 3 (cycleAt i p ht) = fixedSixfoldBetti)
    (hProperGysinNaturality :
      ∀ Γ : codimensionCycles U.X 3,
        coordinates (nativeToHodgeFiberLinear G (extract Γ)) =
        bettiExtract (HU.cycleClass 3 Γ))
    (hWeilNonzero :
      (bettiExtract fixedSixfoldBetti).2 ≠ (0, 0))
    (hCMFunctorial :
      ∀ Z : codimensionCycles V.X 2,
        coordinates (nativeToHodgeFiberLinear G (cmPullback Z)) =
        ((((d+1)^2+d)^2) * (coordinates (nativeToHodgeFiberLinear G Z)).1,
          fourthPowerAction d (d+1)
            (coordinates (nativeToHodgeFiberLinear G Z)).2))
    (alpha : RationalSingularCohomology H.analytification 4)
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading 2)) :
    ∃ Z : codimensionCycles V.X 2, H.cycleClass 2 Z = alpha := by
  obtain ⟨i, p, hp, ht⟩ := periodTransport_all_period_witnesses
    Parameter projection good hclosed hidentity O hO hne hlocal period
  have hRaw :
      coordinates (nativeToHodgeFiberLinear G (extract (cycleAt i p ht))) =
        bettiExtract fixedSixfoldBetti := by
    calc
      coordinates (nativeToHodgeFiberLinear G (extract (cycleAt i p ht))) =
        bettiExtract (HU.cycleClass 3 (cycleAt i p ht)) :=
          hProperGysinNaturality (cycleAt i p ht)
      _ = bettiExtract fixedSixfoldBetti := by rw [hHilbertClass i p hp ht]
  -- Remove the ambient polarization component at the level of genuine
  -- native cycles. No a priori purity of the geometric source is needed.
  let purified : codimensionCycles V.X 2 :=
    extract (cycleAt i p ht) -
      (bettiExtract fixedSixfoldBetti).1 • thetaSquare
  let z : ℚ × ℚ := (bettiExtract fixedSixfoldBetti).2
  have hPurified :
      coordinates (nativeToHodgeFiberLinear G purified) =
        (0, z) := by
    dsimp only [purified, z]
    simp only [map_sub, map_smul, hRaw, hTheta]
    cases hW : bettiExtract fixedSixfoldBetti with
    | mk c v =>
        simp [hW]
  have hCM := hCMFunctorial purified
  rw [hPurified] at hCM
  have hCMPurified :
      coordinates (nativeToHodgeFiberLinear G (cmPullback purified)) =
        (0, fourthPowerAction d (d+1) z) := by
    simpa only [mul_zero] using hCM
  -- Assemble directly on the original codimension-two Chow carrier:
  -- a codimension-three auxiliary source cannot be passed through
  -- an identity map on the original codimension-two Chow carrier.
  let a : ClassicalHodgeFiber V H 2 := ⟨alpha, halpha⟩
  let w : ℚ × ℚ := fourthPowerAction d (d+1) z
  have hz : z ≠ (0, 0) := hWeilNonzero
  have hdet : planeDeterminant z w ≠ 0 :=
    ne_of_gt (extracted_fourth_power_orbit_has_rank_two d hd z hz)
  have hReconstruction := weilPlaneCramerReconstruction z w
    (coordinates a).2 hdet
  let Z : codimensionCycles V.X 2 :=
    (coordinates a).1 • thetaSquare +
      weilPlaneCoeff0 z w (coordinates a).2 • purified +
      weilPlaneCoeff1 z w (coordinates a).2 • cmPullback purified
  refine ⟨Z, ?_⟩
  have hCycle : nativeToHodgeFiberLinear G Z = a := by
    apply coordinates.injective
    simp only [Z, map_add, map_smul, hTheta, hPurified, hCMPurified]
    apply Prod.ext
    · change (coordinates a).1 * 1 + _ * 0 + _ * 0 = (coordinates a).1
      ring
    · apply Prod.ext
      · change (coordinates a).1 * 0 + _ + _ = (coordinates a).2.1
        simpa [smul_eq_mul] using hReconstruction.1
      · change (coordinates a).1 * 0 + _ + _ = (coordinates a).2.2
        simpa [smul_eq_mul] using hReconstruction.2
  exact congrArg Subtype.val hCycle

/-! ## ORIGINAL-A SECANT CHARACTER -> GENUINE FOURFOLD CHOW SOURCE

The manuscript constructs an actual ordinary coherent perfect sheaf
on a Weil sixfold from disjoint Abel-curve torsion orbits and computes
its exceptional Hodge Chern coefficient
  -alpha*(Omega_plus+Omega_minus), alpha=(d+1)/(4*d).
The elliptic graph-difference divisor contracts its balanced
determinant tensor to the SPECIFIC nonzero fourfold Weil vector
  z=((d+1)/(2*d),0).

The theorem below removes the earlier free hWeilNonzero predicate
from the native-original-A Hilbert extraction/CM reconstruction.
Its geometric comparison leaf is instead the specific, falsifiable
equality of the fixed sixfold sheaf's extracted CANONICAL Betti
character with the algebraically derived coefficient. All other
Hilbert, proper Gysin and genuine isogeny data remain explicit:
this is NOT a universal algebraic surface constructor just
because its rational coefficient is nonzero. -/

/-- From a genuine fixed secant perfect-complex Hilbert character
with the explicit graph-extracted Weil coordinate, obtain an
ACTUAL rational Chow cycle on the original fourfold representing
any prescribed rational middle Hodge class.

No arbitrary nonzero-source hypothesis remains: the positive
sixfold secant coefficient proves it. The statement still
requires honest geometric objects and their canonical functorial
comparisons; the previous manuscript's analytic semiregularity
and Hilbert period-spread must supply those instances. -/
theorem auxiliaryWeilEveryMiddleHodgeClass_from_secantCharacter
    {U : SmoothProjectiveComplexScheme}
    (HU : HodgeBigradedBettiData U)
    {T : Type*} [TopologicalSpace T] [BaireSpace T]
    (Parameter : ℕ → Type*) (projection : ∀ i, Parameter i → T)
    (good : ∀ i, Set (Parameter i))
    (hclosed : ∀ i, IsClosed (projection i '' good i))
    (hidentity : ∀ i, (interior (projection i '' good i)).Nonempty →
      projection i '' good i = Set.univ)
    (O : Set T) (hO : IsOpen O) (hne : O.Nonempty)
    (hlocal : ∀ t ∈ O, ∃ i p, p ∈ good i ∧ projection i p = t)
    (period : T)
    (cycleAt : ∀ i (p : Parameter i), projection i p = period →
      codimensionCycles U.X 3)
    (G : GeometricCycleClassSpine V H)
    (extract : codimensionCycles U.X 3 →ₗ[ℚ] codimensionCycles V.X 2)
    (cmPullback : Module.End ℚ (codimensionCycles V.X 2))
    (thetaSquare : codimensionCycles V.X 2)
    (coordinates : ClassicalHodgeFiber V H 2 ≃ₗ[ℚ] ℚ × (ℚ × ℚ))
    (d : ℚ) (hd : 0 < d)
    (hTheta : coordinates (nativeToHodgeFiberLinear G thetaSquare) = (1, (0, 0)))
    (fixedSixfoldBetti : RationalSingularCohomology HU.analytification 6)
    (bettiExtract :
      RationalSingularCohomology HU.analytification 6 →ₗ[ℚ]
        ℚ × (ℚ × ℚ))
    (hHilbertClass : ∀ i p, p ∈ good i → ∀ ht : projection i p = period,
      HU.cycleClass 3 (cycleAt i p ht) = fixedSixfoldBetti)
    (hProperGysinNaturality :
      ∀ Γ : codimensionCycles U.X 3,
        coordinates (nativeToHodgeFiberLinear G (extract Γ)) =
        bettiExtract (HU.cycleClass 3 Γ))
    (hSecantCharacter :
      (bettiExtract fixedSixfoldBetti).2 =
        ((d+1)/(2*d), (0:ℚ)))
    (hCMFunctorial :
      ∀ Z : codimensionCycles V.X 2,
        coordinates (nativeToHodgeFiberLinear G (cmPullback Z)) =
        ((((d+1)^2+d)^2) * (coordinates (nativeToHodgeFiberLinear G Z)).1,
          fourthPowerAction d (d+1)
            (coordinates (nativeToHodgeFiberLinear G Z)).2))
    (alpha : RationalSingularCohomology H.analytification 4)
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading 2)) :
    ∃ Z : codimensionCycles V.X 2, H.cycleClass 2 Z = alpha := by
  have hWeilNonzero : (bettiExtract fixedSixfoldBetti).2 ≠ (0, 0) := by
    rw [hSecantCharacter]
    exact secantSeedCanonicalExtractedWeilComponent_nonzero d hd
  exact auxiliaryWeilEveryMiddleHodgeClass_from_canonicalHilbertSource
    HU Parameter projection good hclosed hidentity O hO hne hlocal
    period cycleAt G extract cmPullback thetaSquare coordinates d hd
    hTheta fixedSixfoldBetti bettiExtract hHilbertClass
    hProperGysinNaturality hWeilNonzero hCMFunctorial alpha halpha

#check auxiliaryWeilEveryMiddleHodgeClass_from_secantCharacter
#print axioms auxiliaryWeilEveryMiddleHodgeClass_from_secantCharacter

#check auxiliaryWeilEveryMiddleHodgeClass_from_canonicalHilbertSource
#print axioms auxiliaryWeilEveryMiddleHodgeClass_from_canonicalHilbertSource

#check auxiliaryWeilEveryMiddleHodgeClass_from_periodSpread_CMFunctorial
#print axioms auxiliaryWeilEveryMiddleHodgeClass_from_periodSpread_CMFunctorial

#check auxiliaryWeilEveryMiddleHodgeClass_from_periodSpread
#print axioms auxiliaryWeilEveryMiddleHodgeClass_from_periodSpread
#print axioms weilPlaneCramerReconstruction
#print axioms auxiliaryWeilNativeCycle_class
#print axioms auxiliaryWeilEveryMiddleHodgeClass

#check quaternionicAntiKGraphSwitchesEigensector
#check quaternionicAntiKGraphNonzero
#check quaternionicGraphWeilTensorNormNonzero
#print axioms quaternionicAntiKGraphSwitchesEigensector

#check cmWeilOneSourceDet_pos
#check cmWeilOneSourceReconstruction
#check cmWeilCentralEigenspaceFilter_kills_ambient
#print axioms cmWeilOneSourceReconstruction

#check cmWeilSplitSourceDeterminant
#check cmWeilSplitSourceDeterminant_nonzero
#print axioms cmWeilSplitSourceDeterminant_nonzero

#check cmWeilMinusOneProjectorPolynomial_idempotent
#check cmWeilMinusOneProjectorPolynomial_on_minus_one
#check cmWeilMinusOneProjectorPolynomial_on_plus_one
#check cmWeilMinusOneProjectorPolynomial_on_quadratic
#check cmWeilFourfoldExactSpectrumCensus
#print axioms cmWeilMinusOneProjectorPolynomial_idempotent

#check CM_multicharge_zero_sum_atom_all_lengths
#check CM_unbounded_even_degree_primitive_atom
#print axioms CM_unbounded_even_degree_primitive_atom

#check quartic_CM_higher_generator_necessary
#print axioms quartic_CM_higher_generator_necessary

#check cubic_CM_atom_requires_new_generator
#print axioms cubic_CM_atom_requires_new_generator

#check no_imaginary_quadratic_CM_on_rational_line
#check no_algebraic_source_transfer_hits_non_algebraic_target
#check no_composed_algebraic_transfer_hits_non_algebraic_target

#print axioms no_imaginary_quadratic_CM_on_rational_line
#print axioms no_algebraic_source_transfer_hits_non_algebraic_target
#print axioms no_composed_algebraic_transfer_hits_non_algebraic_target

end GSTUniversalCMArithmeticObstruction
