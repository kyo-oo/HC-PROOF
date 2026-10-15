import GSTPrimitiveAlgebraicMotiveProjector
import GSTPolarizedHodgeResidualEnergy
import GSTResidualZeroLogicalCountermodel

/-!
# Mathbox: the exact zero-norm target is the primitive rational Hodge conjecture

Single original research goal: PROVE that the canonical primitive
rational Hodge residual r_alpha has Q(r_alpha,r_alpha)=0 for every
smooth projective complex X, p, alpha, by independent geometry.

This file gives the mathematically decisive TYPE-CORRECT implication
and its converse, using the complete IMAGE of actual algebraic cycles
and positive-definite primitive polarization. It proves that the
requested zero-norm claim is EQUIVALENT to genuine algebraicity of
every primitive rational Hodge class. That is a rigorous diagnosis;
it is NOT a proof of the outstanding universal statement.

The only prior geometric assumptions are:
* P.cycleClass is the genuine rational algebraic cycle-class map.
* P.cycles are honest native codimension-p cycles.
* independent intersection-dual probes detect their classes.
* the finitely many P.cycles span the ENTIRE ALGEBRAIC IMAGE
  (not all rational Hodge classes; finite dimensionality permits
  a basis of this image independently of the Hodge conjecture).
* Q is the positive-definite rational Hodge--Riemann polarization
  on the primitive (p,p) rational Hodge fiber.

Under exactly those properties, there is no algebraic/projection
identity left to prove that implies Q(r,r)=0: any such proof
must add a genuinely new, independent geometric theorem implying
the rational Hodge conjecture itself.

The verified rational positive-residual countermodel imported
above demonstrates that positivity, duality and algebraic projector
idempotence ALONE do not establish universal residual zero.
That countermodel is not a counterexample to Hodge on a variety.
-/

set_option maxHeartbeats 4000000
noncomputable section

open GSTUniversalHodgeResidualProjection
open GSTPrimitiveAlgebraicMotiveProjector
open GSTPolarizedHodgeResidualEnergy

namespace GSTResidualNormZeroExactHodgeEquivalence

variable {ι N V : Type*}
  [Fintype ι] [DecidableEq ι]
  [AddCommGroup N] [Module ℚ N]
  [AddCommGroup V] [Module ℚ V]

/-- The finite generators span the EXISTING native image. This
is independent of whether Hodge classes outside that image exist. -/
def ExistingNativeImageSpanned
    (P : GeometricDualCyclePacket ι N V) : Prop :=
  ∀ Z : N, ∃ coeff : ι → ℚ,
    P.cycleClass Z = ∑ i, coeff i • P.cycleClass (P.cycles i)

/-- Projection defined by a genuine algebraic Gram matrix fixes
EVERY currently algebraic cohomology class, not only its generators. -/
theorem algebraicProjector_fixes_entire_native_image
    (P : GeometricDualCyclePacket ι N V)
    (hspan : ExistingNativeImageSpanned P)
    (Z : N) :
    algebraicProjector P (P.cycleClass Z) = P.cycleClass Z := by
  classical
  obtain ⟨coeff, hcoeff⟩ := hspan Z
  calc
    algebraicProjector P (P.cycleClass Z) =
        algebraicProjector P
          (∑ i, coeff i • P.cycleClass (P.cycles i)) := by
            rw [hcoeff]
    _ = ∑ i, coeff i • algebraicProjector P
          (P.cycleClass (P.cycles i)) := by
            simp only [map_sum, map_smul]
    _ = ∑ i, coeff i • P.cycleClass (P.cycles i) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [algebraicProjector_fixes_generator P i]
    _ = P.cycleClass Z := hcoeff.symm

/-- Exact residual zero for an already-algebraic class.
No Hodge conjecture used: only the known NATIVE image basis. -/
theorem residual_zero_of_algebraic_target
    (P : GeometricDualCyclePacket ι N V)
    (hspan : ExistingNativeImageSpanned P)
    (alpha : V)
    (halgebraic : alpha ∈ LinearMap.range P.cycleClass) :
    residualClass P alpha = 0 := by
  obtain ⟨Z, hZ⟩ := halgebraic
  have hfix : algebraicProjector P alpha = alpha := by
    calc
      algebraicProjector P alpha =
          algebraicProjector P (P.cycleClass Z) := by rw [hZ]
      _ = P.cycleClass Z :=
          algebraicProjector_fixes_entire_native_image P hspan Z
      _ = alpha := hZ
  rw [residualClass]
  change alpha - algebraicProjector P alpha = 0
  rw [hfix]
  exact sub_self _

/-- Positive definiteness kills a zero-norm vector, but does NOT
prove the norm of an arbitrary residual is zero. -/
theorem residual_zero_of_zero_polarized_norm
    (P : GeometricDualCyclePacket ι N V)
    (Q : V →ₗ[ℚ] V →ₗ[ℚ] ℚ)
    (hPositive : ∀ v : V, v ≠ 0 → 0 < (Q v) v)
    (alpha : V)
    (hEnergy : (Q (residualClass P alpha))
      (residualClass P alpha) = 0) :
    residualClass P alpha = 0 := by
  by_contra hnonzero
  have hpos := hPositive (residualClass P alpha) hnonzero
  rw [hEnergy] at hpos
  exact (lt_irrefl (0 : ℚ)) hpos

/-- Exact pointwise equivalence: the demanded zero-norm statement
is neither stronger nor weaker than algebraicity of the target
primitive rational Hodge class (once its existing image is fully
accounted for). -/
theorem zero_norm_iff_actual_rational_algebraic
    (P : GeometricDualCyclePacket ι N V)
    (hspan : ExistingNativeImageSpanned P)
    (Q : V →ₗ[ℚ] V →ₗ[ℚ] ℚ)
    (hPositive : ∀ v : V, v ≠ 0 → 0 < (Q v) v)
    (alpha : V) :
    (Q (residualClass P alpha)) (residualClass P alpha) = 0 ↔
       alpha ∈ LinearMap.range P.cycleClass := by
  constructor
  · intro hEnergy
    exact exact_target_representation_of_zero_residual P alpha
      (residual_zero_of_zero_polarized_norm P Q hPositive alpha hEnergy)
  · intro halgebraic
    rw [residual_zero_of_algebraic_target P hspan alpha halgebraic]
    simp

/-- The user's EXACT universal request (all residual norms vanish)
is EQUIVALENT to the full rational Hodge class-surjectivity target
for the selected primitive fiber. This equivalence is kernel-checked;
the universal assertion itself is NOT asserted or proved. -/
theorem all_residual_norms_zero_iff_full_primitive_hodge
    (P : GeometricDualCyclePacket ι N V)
    (hspan : ExistingNativeImageSpanned P)
    (Q : V →ₗ[ℚ] V →ₗ[ℚ] ℚ)
    (hPositive : ∀ v : V, v ≠ 0 → 0 < (Q v) v) :
    (∀ alpha : V,
       (Q (residualClass P alpha)) (residualClass P alpha) = 0) ↔
    Function.Surjective P.cycleClass := by
  constructor
  · intro hzero alpha
    obtain ⟨Z, hZ⟩ :=
      (zero_norm_iff_actual_rational_algebraic
        P hspan Q hPositive alpha).mp (hzero alpha)
    exact ⟨Z, hZ⟩
  · intro honto alpha
    exact (zero_norm_iff_actual_rational_algebraic
      P hspan Q hPositive alpha).mpr (honto alpha)

#check algebraicProjector_fixes_entire_native_image
#check residual_zero_of_algebraic_target
#check residual_zero_of_zero_polarized_norm
#check zero_norm_iff_actual_rational_algebraic
#check all_residual_norms_zero_iff_full_primitive_hodge
#print axioms all_residual_norms_zero_iff_full_primitive_hodge

end GSTResidualNormZeroExactHodgeEquivalence
