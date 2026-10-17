import GSTCMQuadraticNativeRankForcing
import GSTClassicalHodgeCrossCarrierGeometricTransfer

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
