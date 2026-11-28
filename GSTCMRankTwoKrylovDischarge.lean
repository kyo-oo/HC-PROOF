import GSTCMQuadraticNativeRankForcing
import GSTClassicalHodgeRealizedCorrespondenceKrylovFinale
import GSTNativeSingleFoldOrbitLawLanding
import GSTClassicalHodgeGeometricCycleClassSpine
import GSTClassicalHodgeExactClayStatement
import GSTHodgeSingleHypothesisConditional

/-!
# GST CM RANK-TWO KRYLOV DISCHARGE — the single-fold orbit law at every
# dead-or-rank-two-CM world

THE MERGE MODULE of the CM wave: three previously unconnected engines of the
boss's own corpus, fused into one new discharge route for
`NativeGSTSingleFoldOrbitLaw` (X).

## The engines merged (the full citation ledger)

* FROM `GSTCMQuadraticNativeRankForcing.lean` (the CM rank-forcing file,
  kernel-certified in the corpus universe, NEVER before used by any X
  landing): `imaginary_quadratic_CM_no_rational_eigenline` — the imaginary
  quadratic CM polynomial T² - 2aT + (a²+b²), b ≠ 0, eliminates ALL rational
  eigenlines, on ANY rational module.
* FROM `GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra.lean` (the
  realized-correspondence word algebra): `RealizedCorrespondenceWord` as the
  list of rationally weighted realized closed correspondences,
  `realizedWordPair`, and the single-letter word algebra.
* FROM `GSTClassicalHodgeRealizedCorrespondenceKrylovFinale.lean`: the
  `RealizedCorrespondenceKrylovCertificate` structure and `IsKrylovCyclic`
  — the exact shape of X's per-weight demand.
* FROM `GSTNativeSingleFoldOrbitLawLanding.lean`: the empty-word certificate,
  the zero-cycle Hodge membership, and the subsingleton discharge for dead
  weights.
* FROM `GSTClassicalHodgeGeometricCycleClassSpine.lean`:
  `GeometricCycleClassSpine.algebraic_is_hodge` — every genuine algebraic
  cycle's class is Hodge, the free `seed_hodge` field of the certificate.
* FROM `GSTHodgeSingleHypothesisConditional.lean`: X itself and the compiled
  conditional `exactHodge_of_one_GST_fold_orbit` (X ⇒ Y, kernel-certified).

## The new mathematics (this module)

At a weight whose rational Hodge fiber is TWO-dimensional and carries a
Hodge-compatible realized closed correspondence R satisfying the imaginary
CM polynomial, ONE nonzero algebraic seed cycle Z gives the FULL
`RealizedCorrespondenceKrylovCertificate`:

* the certificate's word is the SINGLE LETTER [(1, R)] — one genuine
  correspondence, not a free operator;
* the certificate's seed is Z, Hodge by the geometric spine;
* the Krylov orbit of Z's class under the single word spans the whole fiber:
  if the second orbit vector were a rational multiple of the seed, the seed
  would be a rational eigenvector of the CM word — and the CM eigenline
  elimination forbids exactly that; the pair is then linearly independent,
  two independent vectors in a two-dimensional space, and the corpus's own
  `span_eq_top_of_card_eq_finrank'` engine closes the span.

This is the rank-two analogue of the monogenic discharge
(`native_GST_single_fold_orbit_law_of_dead_or_monogenic_weights`): the
monogenic route certified X at one-generator fibers; the CM route here
certifies X at TWO-generator fibers with an imaginary-CM correspondence —
a world class the discharge never reached before (the constructed finite-line
worlds at M ≥ 2 required the bespoke M-cycle rotation gate; the general
rank-two CM discharge below needs no bespoke gate, only the CM polynomial).

## The boundary (the no-mistake clause)

The discharge is pointwise in (V, H): it certifies X (and therefore Y,
through the compiled conditional) at every world SUPPLYING the per-weight
dead-or-rank-two-CM structure. The universal statement over all smooth
projective complex varieties is not a claim of this module; the corpus's
own countermodel discipline (the Weil zero-or-full test) governs that
boundary exactly as before. No `sorry`, no new axioms, no
`native_decide`.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra
open GSTClassicalHodgeRealizedCorrespondenceKrylovFinale
open GSTCMQuadraticNativeRankForcing
open GSTNativeSingleFoldOrbitLawLanding
open GSTClassicalHodgeExactClayStatement
open GSTHodgeSingleHypothesisConditional

namespace GSTCMRankTwoKrylovDischarge

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-! ## §1 The single-letter word algebra -/

/-- The single-letter word `[(1, R)]` has exactly R's cohomological operator:
one genuine realized closed correspondence, weighted by one, with the empty
tail contributing the zero pair. -/
theorem realizedWordPair_singleton_cohomology
    (R : RealizedFiniteClosedCorrespondence V H p) :
    (realizedWordPair [(1, R)]).cohomologyOperator = R.cohomologyOperator := by
  simp [realizedWordPair, CycleClassOperatorPair.zero, CycleClassOperatorPair.smul,
    CycleClassOperatorPair.add]

/-! ## §2 The CM word certificate -/

/-- **THE CM WORD CERTIFICATE.** One genuine realized closed correspondence R
(Hodge-compatible) as a SINGLE-LETTER word, with a genuine algebraic seed
cycle Z. The word's Hodge preservation is exactly R's compatibility; the
seed's Hodge membership is supplied (at a world with a geometric spine it is
free, by `GeometricCycleClassSpine.algebraic_is_hodge`). -/
noncomputable def cmWordCertificate
    (R : RealizedFiniteClosedCorrespondence V H p)
    (hR : R.HodgeCompatible)
    (Z : codimensionCycles V.X p)
    (hZhodge : H.cycleClass p Z ∈ rationalHodgeSubspace (H.hodgeBigrading p)) :
    RealizedCorrespondenceKrylovCertificate V H p where
  word := [(1, R)]
  word_hodge := by
    intro alpha
    rw [realizedWordPair_singleton_cohomology]
    exact hR alpha
  seedCycle := Z
  seed_hodge := hZhodge

/-- The certificate's Hodge operator IS R's Hodge operator, pointwise: the
single-letter word pair's cohomological operator is R's operator (§1), and
the certificate's `hodgeOperator` is that operator restricted to the fiber. -/
theorem cmWordCertificate_hodgeOperator_apply
    (R : RealizedFiniteClosedCorrespondence V H p)
    (hR : R.HodgeCompatible)
    (Z : codimensionCycles V.X p)
    (hZhodge : H.cycleClass p Z ∈ rationalHodgeSubspace (H.hodgeBigrading p))
    (alpha : ClassicalHodgeFiber V H p) :
    (cmWordCertificate R hR Z hZhodge).hodgeOperator alpha
      = R.hodgeOperator hR alpha := by
  apply Subtype.ext
  show (realizedWordPair [(1, R)]).cohomologyOperator alpha.1
      = R.cohomologyOperator alpha.1
  rw [realizedWordPair_singleton_cohomology]

/-! ## §3 Cyclicity at a rank-two CM weight -/

/-- **CYCLICITY AT A RANK-TWO CM WEIGHT.** If the rational Hodge fiber at p
is two-dimensional, R is a Hodge-compatible realized closed correspondence
whose Hodge operator satisfies the imaginary quadratic CM polynomial
T² - 2aT + (a²+b²) = 0 with b ≠ 0, and Z is a genuine algebraic cycle whose
class is nonzero, then the single-letter CM word certificate is Krylov
cyclic: the orbit of Z's class under the ONE word spans the whole fiber.

The proof is the CM eigenline elimination: the second orbit vector cannot be
a rational multiple of the seed (that would make the seed a rational
eigenvector of the CM word, which `imaginary_quadratic_CM_no_rational_eigenline`
forbids), so the first two orbit vectors are linearly independent — two
independent vectors in a two-dimensional space — and the corpus's own
`span_eq_top_of_card_eq_finrank'` engine closes the span. -/
theorem isKrylovCyclic_of_rank_two_CM_word
    (R : RealizedFiniteClosedCorrespondence V H p)
    (hR : R.HodgeCompatible)
    (a b : ℚ) (hb : b ≠ 0)
    (hMin : ∀ z : ClassicalHodgeFiber V H p,
      R.hodgeOperator hR (R.hodgeOperator hR z) -
        (2*a) • R.hodgeOperator hR z + (a^2+b^2) • z = 0)
    [FiniteDimensional ℚ (ClassicalHodgeFiber V H p)]
    (hrank : Module.finrank ℚ (ClassicalHodgeFiber V H p) = 2)
    (Z : codimensionCycles V.X p)
    (hZhodge : H.cycleClass p Z ∈ rationalHodgeSubspace (H.hodgeBigrading p))
    (hZ : H.cycleClass p Z ≠ 0) :
    (cmWordCertificate R hR Z hZhodge).IsKrylovCyclic := by
  -- The seed orbit vector is nonzero: its underlying class is Z's class.
  have horb0ne : (cmWordCertificate R hR Z hZhodge).hodgeOrbit 0 ≠ 0 := by
    intro h0
    apply hZ
    have hval : Subtype.val ((cmWordCertificate R hR Z hZhodge).hodgeOrbit 0)
        = Subtype.val (0 : ClassicalHodgeFiber V H p) :=
      congrArg Subtype.val h0
    exact hval
  -- The first two orbit vectors are linearly independent.
  have hLI : LinearIndependent ℚ
      ![(cmWordCertificate R hR Z hZhodge).hodgeOrbit 0,
        (cmWordCertificate R hR Z hZhodge).hodgeOrbit 1] := by
    apply (LinearIndependent.pair_iff).2
    intro a' b' hab
    rcases eq_or_ne b' 0 with hb0 | hb0
    · refine ⟨?_, hb0⟩
      rw [hb0, zero_smul, add_zero] at hab
      exact (smul_eq_zero.mp hab).resolve_right horb0ne
    · exfalso
      -- Isolate the second orbit vector.
      have hbt : b' • (cmWordCertificate R hR Z hZhodge).hodgeOrbit 1
          = -(a' • (cmWordCertificate R hR Z hZhodge).hodgeOrbit 0) := by
        rw [add_comm] at hab
        exact eq_neg_of_add_eq_zero_left hab
      have hscale : (cmWordCertificate R hR Z hZhodge).hodgeOrbit 1
          = b'⁻¹ • (b' • (cmWordCertificate R hR Z hZhodge).hodgeOrbit 1) := by
        rw [smul_smul, inv_mul_cancel₀ hb0, one_smul]
      have hstep2 : (cmWordCertificate R hR Z hZhodge).hodgeOrbit 1
          = b'⁻¹ • (-(a' • (cmWordCertificate R hR Z hZhodge).hodgeOrbit 0)) := by
        rw [hscale, hbt]
      have hrepr : (cmWordCertificate R hR Z hZhodge).hodgeOrbit 1
          = (-(b'⁻¹ * a' : ℚ)) • (cmWordCertificate R hR Z hZhodge).hodgeOrbit 0 := by
        rw [hstep2, smul_neg, smul_smul, neg_smul]
      -- STRIKE 10 (the strike-9 receipt: the hMinC transfer is unnecessary —
      -- and its defeq does not ride — because the single-letter word's
      -- operator only PROPOSITIONALLY equals R's, via the §1 lemma, while the
      -- orbit's successor step IS definitionally the certificate's operator).
      -- The repair: bridge the orbit term to R's operator through the
      -- pointwise identity (backwards rewrite), then fire the CM eigenline
      -- elimination DIRECTLY at R's operator with hMin unchanged.
      have hrepr' : R.hodgeOperator hR
            ((cmWordCertificate R hR Z hZhodge).hodgeOrbit 0)
          = (-(b'⁻¹ * a' : ℚ)) •
              (cmWordCertificate R hR Z hZhodge).hodgeOrbit 0 := by
        rw [← cmWordCertificate_hodgeOperator_apply R hR Z hZhodge]
        exact hrepr
      exact imaginary_quadratic_CM_no_rational_eigenline
        (R.hodgeOperator hR) a b hb hMin
        ((cmWordCertificate R hR Z hZhodge).hodgeOrbit 0) horb0ne
        (-(b'⁻¹ * a' : ℚ)) hrepr'
  -- Two independent vectors in a two-dimensional fiber span everything.
  have htop : Submodule.span ℚ
      (Set.range (![(cmWordCertificate R hR Z hZhodge).hodgeOrbit 0,
        (cmWordCertificate R hR Z hZhodge).hodgeOrbit 1] :
        Fin 2 → ClassicalHodgeFiber V H p)) = ⊤ :=
    hLI.span_eq_top_of_card_eq_finrank' (by simpa [hrank])
  -- The orbit range contains the spanning pair (indices 0 and 1).
  have hsub : Set.range (![(cmWordCertificate R hR Z hZhodge).hodgeOrbit 0,
      (cmWordCertificate R hR Z hZhodge).hodgeOrbit 1] :
      Fin 2 → ClassicalHodgeFiber V H p)
      ⊆ Set.range (cmWordCertificate R hR Z hZhodge).hodgeOrbit := by
    rintro x ⟨i, rfl⟩
    fin_cases i
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  show Submodule.span ℚ
      (Set.range (cmWordCertificate R hR Z hZhodge).hodgeOrbit) = ⊤
  have hle : ⊤ ≤ Submodule.span ℚ
      (Set.range (cmWordCertificate R hR Z hZhodge).hodgeOrbit) := by
    rw [← htop]
    exact Submodule.span_le.mpr
      (hsub.trans
        (Submodule.subset_span
          (s := Set.range (cmWordCertificate R hR Z hZhodge).hodgeOrbit)))
  exact top_le_iff.mp hle

/-! ## §4 The law at dead-or-rank-two-CM worlds -/

/-- **THE NATIVE GST SINGLE-FOLD ORBIT LAW, DISCHARGED FOR
DEAD-OR-RANK-TWO-CM WORLDS.** If every weight of `H` is either dead (a
subsingleton rational Hodge fiber) or rank-two CM (a two-dimensional fiber
carrying a Hodge-compatible realized closed correspondence with the
imaginary quadratic CM polynomial and a nonzero algebraic seed cycle), then
the single-fold orbit law holds at (V, H) — unconditionally. At the dead
weights the certificate is the free zero-seed empty word; at the live
weights it is the single-letter CM word with the algebraic seed, and
cyclicity is the CM eigenline elimination of §3.

At a world with a geometric cycle-class spine, the seed's Hodge membership
is FREE (`algebraic_is_hodge`) — the live-weight hypothesis reduces to the
nonvanishing of the seed class plus the CM correspondence data. -/
theorem native_GST_single_fold_orbit_law_of_dead_or_rank_two_CM_weights
    (G : GeometricCycleClassSpine V H)
    (h : ∀ q : Nat,
      Subsingleton (ClassicalHodgeFiber V H q) ∨
      ∃ Z : codimensionCycles V.X q,
        H.cycleClass q Z ≠ 0 ∧
        ∃ R : RealizedFiniteClosedCorrespondence V H q,
          ∃ hR : R.HodgeCompatible,
          ∃ a b : ℚ, b ≠ 0 ∧
            (∀ z : ClassicalHodgeFiber V H q,
              R.hodgeOperator hR (R.hodgeOperator hR z) -
                (2*a) • R.hodgeOperator hR z + (a^2+b^2) • z = 0) ∧
            FiniteDimensional ℚ (ClassicalHodgeFiber V H q) ∧
            Module.finrank ℚ (ClassicalHodgeFiber V H q) = 2) :
    NativeGSTSingleFoldOrbitLaw V H := by
  intro q
  rcases h q with hsub | ⟨Z, hZne, R, hR, a, b, hb, hMin, hFD, hrank⟩
  · exact ⟨emptyWordKrylovCertificate (p := q) 0
      (zeroCycleClass_mem_hodgeFiber H q),
      isKrylovCyclic_of_subsingleton hsub _⟩
  · haveI := hFD
    exact ⟨cmWordCertificate R hR Z (G.algebraic_is_hodge q Z),
      isKrylovCyclic_of_rank_two_CM_word R hR a b hb hMin hrank Z
        (G.algebraic_is_hodge q Z) hZne⟩

/-! ## §5 The Y composition (through the compiled conditional) -/

/-- The exact elementwise Hodge conjecture statement at every
dead-or-rank-two-CM world with a geometric spine: X discharged here, Y
concluded by the kernel-certified conditional of the corpus. -/
theorem everyHodgeClass_is_rational_algebraic_of_dead_or_rank_two_CM_weights
    (G : GeometricCycleClassSpine V H)
    (h : ∀ q : Nat,
      Subsingleton (ClassicalHodgeFiber V H q) ∨
      ∃ Z : codimensionCycles V.X q,
        H.cycleClass q Z ≠ 0 ∧
        ∃ R : RealizedFiniteClosedCorrespondence V H q,
          ∃ hR : R.HodgeCompatible,
          ∃ a b : ℚ, b ≠ 0 ∧
            (∀ z : ClassicalHodgeFiber V H q,
              R.hodgeOperator hR (R.hodgeOperator hR z) -
                (2*a) • R.hodgeOperator hR z + (a^2+b^2) • z = 0) ∧
            FiniteDimensional ℚ (ClassicalHodgeFiber V H q) ∧
            Module.finrank ℚ (ClassicalHodgeFiber V H q) = 2) :
    EveryHodgeClassIsRationalAlgebraic H :=
  exactHodge_of_one_GST_fold_orbit
    (native_GST_single_fold_orbit_law_of_dead_or_rank_two_CM_weights G h)

/-- The finite-rational-combination (verbatim Clay wording) form. -/
theorem everyHodgeClass_is_finite_rational_combination_of_dead_or_rank_two_CM_weights
    (G : GeometricCycleClassSpine V H)
    (h : ∀ q : Nat,
      Subsingleton (ClassicalHodgeFiber V H q) ∨
      ∃ Z : codimensionCycles V.X q,
        H.cycleClass q Z ≠ 0 ∧
        ∃ R : RealizedFiniteClosedCorrespondence V H q,
          ∃ hR : R.HodgeCompatible,
          ∃ a b : ℚ, b ≠ 0 ∧
            (∀ z : ClassicalHodgeFiber V H q,
              R.hodgeOperator hR (R.hodgeOperator hR z) -
                (2*a) • R.hodgeOperator hR z + (a^2+b^2) • z = 0) ∧
            FiniteDimensional ℚ (ClassicalHodgeFiber V H q) ∧
            Module.finrank ℚ (ClassicalHodgeFiber V H q) = 2) :
    EveryHodgeClassIsFiniteRationalCombination H :=
  finiteRationalCombination_of_one_GST_fold_orbit
    (native_GST_single_fold_orbit_law_of_dead_or_rank_two_CM_weights G h)

/-! ## §6 The master package -/

/-- **THE DEAD-OR-RANK-TWO-CM WORLD PACKAGE.** The law (X), the elementwise
exact Hodge statement (Y), and the finite-rational-combination form — one
theorem, at every world supplying the per-weight dead-or-rank-two-CM
structure with a geometric cycle-class spine. -/
theorem the_dead_or_rank_two_CM_world_package
    (G : GeometricCycleClassSpine V H)
    (h : ∀ q : Nat,
      Subsingleton (ClassicalHodgeFiber V H q) ∨
      ∃ Z : codimensionCycles V.X q,
        H.cycleClass q Z ≠ 0 ∧
        ∃ R : RealizedFiniteClosedCorrespondence V H q,
          ∃ hR : R.HodgeCompatible,
          ∃ a b : ℚ, b ≠ 0 ∧
            (∀ z : ClassicalHodgeFiber V H q,
              R.hodgeOperator hR (R.hodgeOperator hR z) -
                (2*a) • R.hodgeOperator hR z + (a^2+b^2) • z = 0) ∧
            FiniteDimensional ℚ (ClassicalHodgeFiber V H q) ∧
            Module.finrank ℚ (ClassicalHodgeFiber V H q) = 2) :
    NativeGSTSingleFoldOrbitLaw V H ∧
    EveryHodgeClassIsRationalAlgebraic H ∧
    EveryHodgeClassIsFiniteRationalCombination H :=
  ⟨native_GST_single_fold_orbit_law_of_dead_or_rank_two_CM_weights G h,
    everyHodgeClass_is_rational_algebraic_of_dead_or_rank_two_CM_weights G h,
    everyHodgeClass_is_finite_rational_combination_of_dead_or_rank_two_CM_weights
      G h⟩

/-! ## §7 The receipts -/

#check realizedWordPair_singleton_cohomology
#check cmWordCertificate
#check cmWordCertificate_hodgeOperator_apply
#check isKrylovCyclic_of_rank_two_CM_word
#check native_GST_single_fold_orbit_law_of_dead_or_rank_two_CM_weights
#check everyHodgeClass_is_rational_algebraic_of_dead_or_rank_two_CM_weights
#check everyHodgeClass_is_finite_rational_combination_of_dead_or_rank_two_CM_weights
#check the_dead_or_rank_two_CM_world_package

#print axioms realizedWordPair_singleton_cohomology
#print axioms cmWordCertificate
#print axioms cmWordCertificate_hodgeOperator_apply
#print axioms isKrylovCyclic_of_rank_two_CM_word
#print axioms native_GST_single_fold_orbit_law_of_dead_or_rank_two_CM_weights
#print axioms everyHodgeClass_is_rational_algebraic_of_dead_or_rank_two_CM_weights
#print axioms everyHodgeClass_is_finite_rational_combination_of_dead_or_rank_two_CM_weights
#print axioms the_dead_or_rank_two_CM_world_package

end GSTCMRankTwoKrylovDischarge
end -- noncomputable section
