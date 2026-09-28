import GSTClassicalHodgePrimitiveQuotientDualProjectiveAction
import GSTClassicalHodgeAtomicAnnihilator

/-!
# GST CLASSICAL HODGE — PRIMITIVE ALGEBRAIC ANNIHILATOR

The minimal primitive separator should not be viewed as a detector attached to
one arbitrary chosen Hodge basis.  After passing to the primitive geometric
quotient there is a canonical basis-free object it belongs to: the annihilator
of the complete image of genuine algebraic cycle classes.

Let

    Q_p = H^{2p}(X,Q) / lowerGeometricImage_p

and let `A_p` be the image in `Q_p` of the actual codimension-p cycle-class
range.  Every genuine same-weight projective word preserves `A_p`: on native
cycles the word has an exact cycle-class commuting square, and the lower
geometric image is already projective-word stable.

Dually, the annihilator

    A_p^⊥ ⊂ Q_p^*

is invariant under the contragredient projective-word action.  A minimal
primitive separator descends to a NONZERO element of this invariant
annihilator.  Hence any Stage-2G failure produces a nonzero basis-free invariant
dual subrepresentation after all lower-weight geometry has been divided out.

This removes arbitrary Hodge-basis permutations from the remaining geometric
problem.  The frontier is now an intrinsic irreducibility/no-ghost statement
for the independently verified projective action on the primitive quotient.
-/

set_option maxHeartbeats 90000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgePrimitiveAlgebraicAnnihilator

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeProjectiveWordOrbit
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeAtomicAnnihilator
open GSTClassicalHodgeMinimalPrimitiveSeparatorGhost
open GSTClassicalHodgePrimitiveGeometricQuotient
open GSTClassicalHodgePrimitiveQuotientDetector
open GSTClassicalHodgePrimitiveQuotientProjectiveAction
open GSTClassicalHodgePrimitiveQuotientDualProjectiveAction

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Actual algebraic cycle-class range, observed inside the primitive quotient. -/
noncomputable def primitiveAlgebraicImage
    (G : GeometricCycleClassSpine V H)
    (p : Nat) :
    Submodule ℚ (PrimitiveGeometricQuotient G p) :=
  Submodule.map (lowerGeometricImage G p).mkQ
    (LinearMap.range (H.cycleClass p))

/-- Every genuine same-weight projective word preserves the primitive algebraic
image.  This is pure cycle-class naturality plus quotient descent. -/
theorem primitiveAlgebraicImage_stable_projectiveWord
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (W : ProjectiveOperatorWord V p) :
    primitiveAlgebraicImage G p ≤
      (primitiveAlgebraicImage G p).comap
        (primitiveProjectiveAction G p W) := by
  rintro y ⟨x, hx, rfl⟩
  rcases hx with ⟨Z, rfl⟩
  rw [primitiveProjectiveAction_mk]
  have hnat := W.cycleClass_eval G Z
  refine ⟨H.cycleClass p (W.eval Z), ⟨W.eval Z, rfl⟩, ?_⟩
  exact congrArg (lowerGeometricImage G p).mkQ hnat.symm

/-- Basis-free annihilator of the genuine algebraic image in the primitive
quotient. -/
noncomputable def primitiveAlgebraicAnnihilator
    (G : GeometricCycleClassSpine V H)
    (p : Nat) :
    Submodule ℚ
      (PrimitiveGeometricQuotient G p →ₗ[ℚ] ℚ) where
  carrier := { ell | primitiveAlgebraicImage G p ≤ LinearMap.ker ell }
  zero_mem' := by
    intro x hx
    rfl
  add_mem' := by
    intro a b ha hb x hx
    simp [ha hx, hb hx]
  smul_mem' := by
    intro c a ha x hx
    simp [ha hx]

@[simp]
theorem mem_primitiveAlgebraicAnnihilator_iff
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (ell : PrimitiveGeometricQuotient G p →ₗ[ℚ] ℚ) :
    ell ∈ primitiveAlgebraicAnnihilator G p ↔
      primitiveAlgebraicImage G p ≤ LinearMap.ker ell :=
  Iff.rfl

/-- The dual projective action preserves the algebraic annihilator. -/
theorem primitiveAlgebraicAnnihilator_stable_dualProjective
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (W : ProjectiveOperatorWord V p) :
    primitiveAlgebraicAnnihilator G p ≤
      (primitiveAlgebraicAnnihilator G p).comap
        (primitiveProjectiveDualAction G p W) := by
  intro ell hell
  change primitiveAlgebraicImage G p ≤
    LinearMap.ker (primitiveProjectiveDualAction G p W ell)
  intro x hx
  change ell (primitiveProjectiveAction G p W x) = 0
  exact hell (primitiveAlgebraicImage_stable_projectiveWord G p W hx)

/-- The original atomic separator annihilates the full genuine cycle-class
range, not only the individual point generators. -/
theorem minimalSeparator_cycleClassRange_le_ker
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G) :
    LinearMap.range (H.cycleClass M.weight) ≤
      LinearMap.ker M.separator.detector := by
  rw [smoothProjective_cycleClass_range_eq_atomic_span V H M.weight]
  exact (annihilatesPointCycles_iff_atomicSpan_le_ker
    M.weight (H.cycleClass M.weight) M.separator.detector).mp
      M.separator.annihilates_atoms

/-- Therefore the descended minimal primitive detector lies in the basis-free
primitive algebraic annihilator. -/
theorem primitiveQuotientDetector_mem_algebraicAnnihilator
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G) :
    primitiveQuotientDetector G M ∈
      primitiveAlgebraicAnnihilator G M.weight := by
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  rfl
  exact minimalSeparator_cycleClassRange_le_ker G M hx

/-- The invariant annihilator is nontrivial whenever a minimal primitive ghost
exists. -/
theorem primitiveAlgebraicAnnihilator_ne_bot_of_minimalGhost
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G) :
    primitiveAlgebraicAnnihilator G M.weight ≠ ⊥ := by
  intro hbot
  have hmem := primitiveQuotientDetector_mem_algebraicAnnihilator G M
  rw [hbot] at hmem
  have hz : primitiveQuotientDetector G M = 0 := by simpa using hmem
  exact primitiveQuotientDetector_ne_zero G M hz

/-- **BASIS-FREE PRIMITIVE FAILURE PACKET.**
Every Stage-2G failure produces a nonzero projective-dual-invariant annihilator
of the complete genuine algebraic image in one primitive quotient. -/
theorem not_hodge_yields_nonzero_invariant_primitive_algebraic_annihilator
    (G : GeometricCycleClassSpine V H)
    (hnot : ¬ BigradedBettiHodgeStatement V H) :
    ∃ M : MinimalPrimitiveGhost G,
      primitiveAlgebraicAnnihilator G M.weight ≠ ⊥
      ∧ primitiveQuotientDetector G M ∈
          primitiveAlgebraicAnnihilator G M.weight
      ∧ primitiveQuotientDetector G M ≠ 0
      ∧ (∀ W : ProjectiveOperatorWord V M.weight,
          primitiveAlgebraicAnnihilator G M.weight ≤
            (primitiveAlgebraicAnnihilator G M.weight).comap
              (primitiveProjectiveDualAction G M.weight W)) := by
  let M := minimalPrimitiveGhostOfFailure G hnot
  exact ⟨M,
    primitiveAlgebraicAnnihilator_ne_bot_of_minimalGhost G M,
    primitiveQuotientDetector_mem_algebraicAnnihilator G M,
    primitiveQuotientDetector_ne_zero G M,
    fun W => primitiveAlgebraicAnnihilator_stable_dualProjective
      G M.weight W⟩

#check primitiveAlgebraicImage
#check primitiveAlgebraicImage_stable_projectiveWord
#check primitiveAlgebraicAnnihilator
#check primitiveAlgebraicAnnihilator_stable_dualProjective
#check minimalSeparator_cycleClassRange_le_ker
#check primitiveQuotientDetector_mem_algebraicAnnihilator
#check primitiveAlgebraicAnnihilator_ne_bot_of_minimalGhost
#check not_hodge_yields_nonzero_invariant_primitive_algebraic_annihilator

#print axioms primitiveAlgebraicImage_stable_projectiveWord
#print axioms primitiveAlgebraicAnnihilator_stable_dualProjective
#print axioms primitiveQuotientDetector_mem_algebraicAnnihilator
#print axioms not_hodge_yields_nonzero_invariant_primitive_algebraic_annihilator

end GSTClassicalHodgePrimitiveAlgebraicAnnihilator
