import GSTClassicalHodgeComplementaryDefectReciprocity

/-!
# GST CLASSICAL HODGE — DEFECT RECIPROCITY MODULO ATOMIC CLASSES

Exact ambient inversion is stronger than the atomic-defect argument needs.
The quotient forgets every genuine algebraic cycle-class combination.  Hence a
return operator only has to recover the source Hodge class up to an algebraic
error:

  R (L alpha) - lambda * alpha in AtomicSpan.

After quotienting, the error vanishes and the round trip is exactly
`lambda * id` on the Hodge defect.

This file formalizes that weaker, genuinely quotient-native frontier.  It is
strictly weaker than an exact cohomological inverse and is therefore the
preferred externalization target for the complementary Lefschetz/Poincare
route.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeDefectModuloAtomicReciprocity

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeAtomicDefectDuality
open GSTClassicalHodgeCrossWeightNativePropagation
open GSTClassicalHodgeCrossWeightAtomicDefectDescent
open GSTClassicalHodgeComplementaryDefectReciprocity
open GSTClassicalHodgeGeometricCycleClassSpine

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p q : Nat}

/-- A genuine graded forward operator and a genuine graded return operator
whose round trip is a nonzero scalar modulo the complete atomic cycle-class
span, only on the actual Hodge source sector. -/
structure HodgeDefectReturnModuloAtomic
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p q : Nat) where
  forward : GradedCycleClassOperatorPair V H p q
  backward : GradedCycleClassOperatorPair V H q p
  forward_hodge :
    ∀ alpha : CohAt H p,
      alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p) →
        forward.cohomologyOperator alpha ∈
          rationalHodgeSubspace (H.hodgeBigrading q)
  scalar : ℚ
  scalar_ne_zero : scalar ≠ 0
  roundtrip_mod_atomic :
    ∀ alpha : CohAt H p,
      alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p) →
        backward.cohomologyOperator
            (forward.cohomologyOperator alpha) - scalar • alpha ∈
          AtomicSpanAt H p

namespace HodgeDefectReturnModuloAtomic

/-- On an actual Hodge class, reciprocity modulo algebraic classes becomes an
exact scalar round trip after passing to atomic defects. -/
theorem defect_roundtrip_on_hodge
    (R : HodgeDefectReturnModuloAtomic V H p q)
    (alpha : ClassicalHodgeFiber V H p) :
    R.backward.defectOperator
        (R.forward.defectOperator (atomicDefectLinearMap V H p alpha)) =
      R.scalar • atomicDefectLinearMap V H p alpha := by
  rw [atomicDefectLinearMap_apply,
      GradedCycleClassOperatorPair.defectOperator_mk,
      GradedCycleClassOperatorPair.defectOperator_mk]
  have hzero :
      Submodule.Quotient.mk
          (R.backward.cohomologyOperator
              (R.forward.cohomologyOperator alpha.1) -
            R.scalar • alpha.1) =
        (0 : DefectAt V H p) :=
    (Submodule.Quotient.mk_eq_zero (AtomicSpanAt H p)).2
      (R.roundtrip_mod_atomic alpha.1 alpha.2)
  have hsub :
      Submodule.Quotient.mk
          (R.backward.cohomologyOperator
            (R.forward.cohomologyOperator alpha.1)) -
        R.scalar • Submodule.Quotient.mk alpha.1 =
      (0 : DefectAt V H p) := by
    simpa using hzero
  exact sub_eq_zero.mp hsub

/-- If every Hodge defect vanishes at the target weight, then every source
Hodge defect vanishes as well.  No exact ambient inverse is required. -/
theorem source_atomicDefect_zero_of_target_hodge
    (R : HodgeDefectReturnModuloAtomic V H p q)
    (alpha : ClassicalHodgeFiber V H p)
    (htarget : atomicDefectLinearMap V H q = 0) :
    atomicDefectLinearMap V H p alpha = 0 := by
  let beta : ClassicalHodgeFiber V H q :=
    ⟨R.forward.cohomologyOperator alpha.1,
      R.forward_hodge alpha.1 alpha.2⟩
  have hbeta : atomicDefectLinearMap V H q beta = 0 := by
    rw [htarget]
    rfl
  have hforward :
      R.forward.defectOperator (atomicDefectLinearMap V H p alpha) = 0 := by
    rw [← R.forward.defect_equivariant alpha
      (R.forward_hodge alpha.1 alpha.2)]
    exact hbeta
  have hback := congrArg R.backward.defectOperator hforward
  have hscalar :
      R.scalar • atomicDefectLinearMap V H p alpha = 0 := by
    rw [R.defect_roundtrip_on_hodge alpha]
    simpa using hback
  have hinv := congrArg (fun z => R.scalar⁻¹ • z) hscalar
  simpa [smul_smul, R.scalar_ne_zero] using hinv

/-- Map-level backward propagation of the Hodge conclusion. -/
theorem source_hodge_of_target_hodge
    (R : HodgeDefectReturnModuloAtomic V H p q)
    (htarget : atomicDefectLinearMap V H q = 0) :
    atomicDefectLinearMap V H p = 0 := by
  apply LinearMap.ext
  intro alpha
  exact R.source_atomicDefect_zero_of_target_hodge alpha htarget

end HodgeDefectReturnModuloAtomic

/-- Preferred complementary-power interface: the genuine return only has to
invert the n-fold principal cut modulo algebraic classes on Hodge inputs. -/
structure PrincipalCutPowerReturnModuloAtomic
    (G : GeometricCycleClassSpine V H)
    (p n : Nat) where
  returnPair : GradedCycleClassOperatorPair V H (p + n) p
  scalar : ℚ
  scalar_ne_zero : scalar ≠ 0
  roundtrip_mod_atomic :
    ∀ alpha : CohAt H p,
      alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p) →
        returnPair.cohomologyOperator
            ((principalCutPairIterate G p n).cohomologyOperator alpha) -
          scalar • alpha ∈ AtomicSpanAt H p

namespace PrincipalCutPowerReturnModuloAtomic

/-- The power law induces the general Hodge-defect reciprocity package. -/
noncomputable def toHodgeDefectReturnModuloAtomic
    (R : PrincipalCutPowerReturnModuloAtomic G p n) :
    HodgeDefectReturnModuloAtomic V H p (p + n) where
  forward := principalCutPairIterate G p n
  backward := R.returnPair
  forward_hodge := principalCutPairIterate_hodge G p n
  scalar := R.scalar
  scalar_ne_zero := R.scalar_ne_zero
  roundtrip_mod_atomic := R.roundtrip_mod_atomic

/-- Hodge at the complementary target weight propagates back through a return
law that is correct only modulo genuine algebraic classes. -/
theorem source_hodge_of_target_hodge
    (R : PrincipalCutPowerReturnModuloAtomic G p n)
    (htarget : atomicDefectLinearMap V H (p + n) = 0) :
    atomicDefectLinearMap V H p = 0 :=
  R.toHodgeDefectReturnModuloAtomic.source_hodge_of_target_hodge htarget

end PrincipalCutPowerReturnModuloAtomic

/-- Hard-Lefschetz-shaped preferred interface. -/
abbrev ComplementaryReturnModuloAtomic
    (G : GeometricCycleClassSpine V H)
    (d p : Nat) :=
  PrincipalCutPowerReturnModuloAtomic G p (complementaryExponent d p)

#check HodgeDefectReturnModuloAtomic
#check HodgeDefectReturnModuloAtomic.defect_roundtrip_on_hodge
#check HodgeDefectReturnModuloAtomic.source_hodge_of_target_hodge
#check PrincipalCutPowerReturnModuloAtomic
#check PrincipalCutPowerReturnModuloAtomic.source_hodge_of_target_hodge
#check ComplementaryReturnModuloAtomic

#print axioms HodgeDefectReturnModuloAtomic.defect_roundtrip_on_hodge
#print axioms HodgeDefectReturnModuloAtomic.source_hodge_of_target_hodge
#print axioms PrincipalCutPowerReturnModuloAtomic.source_hodge_of_target_hodge

end GSTClassicalHodgeDefectModuloAtomicReciprocity
