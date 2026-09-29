import GSTClassicalHodgeFirstFailureBiFiniteTransposePureTransversality

/-!
# GST CLASSICAL HODGE — BI-FINITE TRANSPOSE DIAGONAL MODULO ATOMIC

Pure transpose transversality still asks directly for a nonzero separator read.
This file converts that analytic-looking nonvanishing into a geometric
one-state diagonal statement modulo classes which are already algebraic.

For one obstructed Hodge basis sheet `e_i`, suppose an actual bi-finite closed
correspondence `K` has genuine forward/transpose cycle-class naturality and
sends `e_i` into the predecessor Hodge fiber.  It is enough to know that

    K^t K (e_i) = lambda * e_i + a,

where `lambda != 0` and `a` belongs to the complete atomic cycle-class span at
the successor weight.

The microscopic separator kills `a` and detects `e_i`.  Therefore it detects
`K^t K (e_i)` with read `lambda * S(e_i)`, which is nonzero.  This produces the
pure-transversality packet and the already-proved first-failure contradiction.

This is substantially weaker than a scalar round-trip, a global diagonal
formula, a coisometry, or a correspondence realizing a matrix unit.  Only one
basis state and equality modulo the actual algebraic cycle-class span are used.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeFirstFailureBiFiniteTransposeDiagonalModuloAtomic

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeAtomicAnnihilator
open GSTClassicalHodgeSingleSheetCrown
open GSTClassicalHodgeFiniteClosedCorrespondenceTranspose
open GSTClassicalHodgeFirstGhostTransposeAdjointGeometry
open GSTClassicalHodgeFirstPrimitiveProjectiveFailure
open GSTClassicalHodgeFirstFailurePoincareReadCollision
open GSTClassicalHodgeFirstFailureBiFiniteTransposePureTransversality

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- One actual bi-finite correspondence whose transpose round trip has a
nonzero diagonal coefficient on the obstructed basis sheet modulo already
algebraic successor classes. -/
structure FirstFailureBiFiniteTransposeDiagonalModuloAtomic
    (p : Nat)
    (i : ClassicalHodgeBasisIndex V H (p + 1))
    (S : BasisAtomicSeparator V H (p + 1) i)
    (K : BiFiniteClosedCorrespondence V) where
  naturality : BiFiniteTransposeNaturality K (p + 1) p
  return_hodge :
    naturality.forward.cohomologyOperator
        (classicalHodgeBasis V H (p + 1) i).1 ∈
      rationalHodgeSubspace (H.hodgeBigrading p)
  diagonalScalar : ℚ
  diagonalScalar_ne_zero : diagonalScalar ≠ 0
  roundtrip_sub_diagonal_atomic :
    naturality.transpose.cohomologyOperator
        (naturality.forward.cohomologyOperator
          (classicalHodgeBasis V H (p + 1) i).1)
      - diagonalScalar • (classicalHodgeBasis V H (p + 1) i).1 ∈
        pointCycleClassSpan (p + 1) (H.cycleClass (p + 1))

namespace FirstFailureBiFiniteTransposeDiagonalModuloAtomic

/-- The separator kills the algebraic correction term in the round-trip
formula. -/
theorem separator_roundtrip_sub_diagonal_eq_zero
    {i : ClassicalHodgeBasisIndex V H (p + 1)}
    {S : BasisAtomicSeparator V H (p + 1) i}
    {K : BiFiniteClosedCorrespondence V}
    (R : FirstFailureBiFiniteTransposeDiagonalModuloAtomic
      (V := V) (H := H) p i S K) :
    S.detector
      (R.naturality.transpose.cohomologyOperator
          (R.naturality.forward.cohomologyOperator
            (classicalHodgeBasis V H (p + 1) i).1)
        - R.diagonalScalar •
            (classicalHodgeBasis V H (p + 1) i).1) = 0 := by
  have hker :
      pointCycleClassSpan (p + 1) (H.cycleClass (p + 1)) ≤
        LinearMap.ker S.detector :=
    (annihilatesPointCycles_iff_atomicSpan_le_ker
      (p + 1) (H.cycleClass (p + 1)) S.detector).mp S.annihilates_atoms
  exact hker R.roundtrip_sub_diagonal_atomic

/-- Consequently the exact separator read of the transpose round trip is the
nonzero diagonal scalar times the separator's nonzero basis read. -/
theorem separator_roundtrip_eq_scalar_mul
    {i : ClassicalHodgeBasisIndex V H (p + 1)}
    {S : BasisAtomicSeparator V H (p + 1) i}
    {K : BiFiniteClosedCorrespondence V}
    (R : FirstFailureBiFiniteTransposeDiagonalModuloAtomic
      (V := V) (H := H) p i S K) :
    S.detector
      (R.naturality.transpose.cohomologyOperator
        (R.naturality.forward.cohomologyOperator
          (classicalHodgeBasis V H (p + 1) i).1)) =
      R.diagonalScalar *
        S.detector (classicalHodgeBasis V H (p + 1) i).1 := by
  have hz := R.separator_roundtrip_sub_diagonal_eq_zero
  rw [LinearMap.map_sub, LinearMap.map_smul] at hz
  simp only [smul_eq_mul] at hz
  linarith

/-- The transpose round trip is therefore automatically transverse to the
microscopic atomic separator. -/
theorem separator_roundtrip_ne_zero
    {i : ClassicalHodgeBasisIndex V H (p + 1)}
    {S : BasisAtomicSeparator V H (p + 1) i}
    {K : BiFiniteClosedCorrespondence V}
    (R : FirstFailureBiFiniteTransposeDiagonalModuloAtomic
      (V := V) (H := H) p i S K) :
    S.detector
      (R.naturality.transpose.cohomologyOperator
        (R.naturality.forward.cohomologyOperator
          (classicalHodgeBasis V H (p + 1) i).1)) ≠ 0 := by
  rw [R.separator_roundtrip_eq_scalar_mul]
  exact mul_ne_zero R.diagonalScalar_ne_zero S.detects_basis

/-- Forget the diagonal-mod-atomic calculation to the minimal pure
transversality packet. -/
noncomputable def toPureTransverse
    {i : ClassicalHodgeBasisIndex V H (p + 1)}
    {S : BasisAtomicSeparator V H (p + 1) i}
    {K : BiFiniteClosedCorrespondence V}
    (R : FirstFailureBiFiniteTransposeDiagonalModuloAtomic
      (V := V) (H := H) p i S K) :
    FirstFailureBiFiniteTransposePureTransverse
      (V := V) (H := H) p i S K where
  naturality := R.naturality
  return_hodge := R.return_hodge
  separator_transverse := R.separator_roundtrip_ne_zero

/-- At a globally least bad successor weight even this weak diagonal-mod-atomic
correspondence law is impossible. -/
theorem firstFailure_forbids_diagonalModuloAtomic
    (F : FirstAtomicDefectWeight V H)
    (hp : F.weight = p + 1)
    {i : ClassicalHodgeBasisIndex V H (p + 1)}
    {S : BasisAtomicSeparator V H (p + 1) i}
    {K : BiFiniteClosedCorrespondence V}
    (R : FirstFailureBiFiniteTransposeDiagonalModuloAtomic
      (V := V) (H := H) p i S K) : False :=
  R.toPureTransverse.firstFailure_forbids_biFiniteTransposePureTransverse F hp

end FirstFailureBiFiniteTransposeDiagonalModuloAtomic

/-- **DIAGONAL-MOD-ATOMIC HODGE CROWN.**
If every microscopic successor separator admits one actual bi-finite
correspondence whose transpose round trip contains that basis sheet with a
nonzero coefficient modulo actual algebraic classes, the full Stage-2G Hodge
statement follows. -/
theorem bigradedBettiHodge_of_diagonalModuloAtomicFamily
    (hzero :
      GSTClassicalHodgeAtomicDefectDuality.atomicDefectLinearMap V H 0 = 0)
    (R : ∀ p : Nat,
      ∀ i : ClassicalHodgeBasisIndex V H (p + 1),
      ∀ S : BasisAtomicSeparator V H (p + 1) i,
        ∃ K : BiFiniteClosedCorrespondence V,
          Nonempty
            (FirstFailureBiFiniteTransposeDiagonalModuloAtomic
              (V := V) (H := H) p i S K)) :
    BigradedBettiHodgeStatement V H := by
  apply bigradedBettiHodge_of_biFiniteTransposePureTransverseFamily hzero
  intro q i S
  rcases R q i S with ⟨K, hK⟩
  rcases hK with ⟨RK⟩
  exact ⟨K, ⟨RK.toPureTransverse⟩⟩

#check FirstFailureBiFiniteTransposeDiagonalModuloAtomic
#check FirstFailureBiFiniteTransposeDiagonalModuloAtomic.separator_roundtrip_eq_scalar_mul
#check FirstFailureBiFiniteTransposeDiagonalModuloAtomic.separator_roundtrip_ne_zero
#check FirstFailureBiFiniteTransposeDiagonalModuloAtomic.toPureTransverse
#check FirstFailureBiFiniteTransposeDiagonalModuloAtomic.firstFailure_forbids_diagonalModuloAtomic
#check bigradedBettiHodge_of_diagonalModuloAtomicFamily

#print axioms FirstFailureBiFiniteTransposeDiagonalModuloAtomic.separator_roundtrip_eq_scalar_mul
#print axioms FirstFailureBiFiniteTransposeDiagonalModuloAtomic.separator_roundtrip_ne_zero
#print axioms FirstFailureBiFiniteTransposeDiagonalModuloAtomic.toPureTransverse
#print axioms bigradedBettiHodge_of_diagonalModuloAtomicFamily

end GSTClassicalHodgeFirstFailureBiFiniteTransposeDiagonalModuloAtomic
