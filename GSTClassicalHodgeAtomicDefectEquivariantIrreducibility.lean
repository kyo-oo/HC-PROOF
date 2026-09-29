import GSTClassicalHodgeAtomicDefectOperatorDescent
import GSTClassicalHodgeRankFreeArsenalIrreducibility
import GSTClassicalHodgeArsenalNonCircularity

/-!
# GST CLASSICAL HODGE — ATOMIC DEFECT EQUIVARIANT IRREDUCIBILITY

The previous quotient-descent layer showed that every ambient cohomological
operator preserving the complete atomic cycle-class span acts canonically on
the atomic defect quotient.  The rank-free GST arsenal independently proves
that a nonzero Hodge submodule stable under every local matrix unit is the
whole Hodge fiber.

This file is the exact splice between those two worlds.

An ambient operator is called `AtomicNaturalHodgeOperator` when:

* it preserves the genuine atomic point-cycle span;
* it preserves the rational `(p,p)` Hodge fiber through a specified Hodge
  endomorphism;
* its ambient action agrees exactly with that Hodge endomorphism on Hodge
  classes.

Such an operator automatically preserves the algebraic Hodge subspace and the
atomic defect map is equivariant for its descended quotient action.  Hence a
family of independently constructed atomic-natural ambient operators whose
Hodge restrictions are the GST matrix units makes the algebraic Hodge
subspace rank-free invariant.  One nonzero algebraic seed then triggers the
existing GST irreducibility theorem and kills the atomic defect.

No cycle representative for a nonalgebraic Hodge vector is assumed here.  The
new geometric obligation is entirely operator-theoretic: construct genuine
atomic-natural ambient operators and prove their Hodge restrictions.  The
arsenal non-circularity audit remains in force: the matrix-unit family itself
must come from independently constructed geometry, not be postulated as a
replacement for Hodge.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeAtomicDefectEquivariantIrreducibility

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeAtomicDefectDuality
open GSTClassicalHodgeGeneratorwiseAtomicStability
open GSTClassicalHodgeAtomicDefectOperatorDescent
open GSTClassicalHodgeRankFreeArsenalIrreducibility

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

abbrev Coh := RationalSingularCohomology H.analytification (2 * p)
abbrev HFiber := ClassicalHodgeFiber V H p
abbrev Defect := AtomicDefectSpace V H p

/-- One ambient operator with independently verified atomic naturality and an
exact Hodge-fiber restriction. -/
structure AtomicNaturalHodgeOperator
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) where
  ambient : Coh (H := H) p →ₗ[ℚ] Coh (H := H) p
  hodge : Module.End ℚ (HFiber (V := V) (H := H) p)
  atomicStable :
    AtomicSpanStable (p := p) (cl := H.cycleClass p) ambient
  restricts : ∀ alpha : HFiber (V := V) (H := H) p,
    ambient alpha.1 = (hodge alpha).1

namespace AtomicNaturalHodgeOperator

/-- The ambient operator descends canonically to the genuine atomic defect
quotient. -/
noncomputable def defectOperator
    (T : AtomicNaturalHodgeOperator V H p) :
    Defect (V := V) (H := H) p →ₗ[ℚ] Defect (V := V) (H := H) p :=
  atomicDefectOperator (V := V) T.ambient T.atomicStable

/-- **DEFECT EQUIVARIANCE.**  Applying the Hodge restriction and then taking
atomic defect is exactly the same as taking defect first and applying the
descended ambient operator. -/
theorem defect_equivariant
    (T : AtomicNaturalHodgeOperator V H p)
    (alpha : HFiber (V := V) (H := H) p) :
    atomicDefectLinearMap V H p (T.hodge alpha) =
      T.defectOperator (atomicDefectLinearMap V H p alpha) := by
  rw [atomicDefectLinearMap_apply, atomicDefectLinearMap_apply]
  unfold AtomicNaturalHodgeOperator.defectOperator
  rw [atomicDefectOperator_mk]
  rw [T.restricts]

/-- Atomic-natural Hodge operators preserve the algebraic Hodge kernel. -/
theorem preserves_algebraicHodge
    (T : AtomicNaturalHodgeOperator V H p)
    {alpha : HFiber (V := V) (H := H) p}
    (halpha : alpha ∈ AlgebraicHodgeSubspace V H p) :
    T.hodge alpha ∈ AlgebraicHodgeSubspace V H p := by
  change (T.hodge alpha).1 ∈ pointCycleClassSpan p (H.cycleClass p)
  rw [← T.restricts alpha]
  exact T.atomicStable alpha.1 halpha

/-- The identity is atomic-natural. -/
noncomputable def id : AtomicNaturalHodgeOperator V H p where
  ambient := LinearMap.id
  hodge := LinearMap.id
  atomicStable := by
    intro alpha halpha
    simpa using halpha
  restricts := by
    intro alpha
    rfl

/-- Rational scaling preserves atomic naturality. -/
noncomputable def smul
    (q : ℚ)
    (T : AtomicNaturalHodgeOperator V H p) :
    AtomicNaturalHodgeOperator V H p where
  ambient := q • T.ambient
  hodge := q • T.hodge
  atomicStable := by
    intro alpha halpha
    change q • T.ambient alpha ∈ pointCycleClassSpan p (H.cycleClass p)
    exact (pointCycleClassSpan p (H.cycleClass p)).smul_mem q
      (T.atomicStable alpha halpha)
  restricts := by
    intro alpha
    change q • T.ambient alpha.1 = (q • T.hodge alpha).1
    rw [T.restricts]
    rfl

/-- Sums preserve atomic naturality. -/
noncomputable def add
    (T U : AtomicNaturalHodgeOperator V H p) :
    AtomicNaturalHodgeOperator V H p where
  ambient := T.ambient + U.ambient
  hodge := T.hodge + U.hodge
  atomicStable := by
    intro alpha halpha
    change T.ambient alpha + U.ambient alpha ∈
      pointCycleClassSpan p (H.cycleClass p)
    exact (pointCycleClassSpan p (H.cycleClass p)).add_mem
      (T.atomicStable alpha halpha) (U.atomicStable alpha halpha)
  restricts := by
    intro alpha
    change T.ambient alpha.1 + U.ambient alpha.1 =
      ((T.hodge + U.hodge) alpha).1
    rw [T.restricts, U.restricts]
    rfl

/-- Compositions preserve atomic naturality. -/
noncomputable def comp
    (T U : AtomicNaturalHodgeOperator V H p) :
    AtomicNaturalHodgeOperator V H p where
  ambient := T.ambient.comp U.ambient
  hodge := T.hodge.comp U.hodge
  atomicStable := by
    intro alpha halpha
    exact T.atomicStable (U.ambient alpha) (U.atomicStable alpha halpha)
  restricts := by
    intro alpha
    change T.ambient (U.ambient alpha.1) =
      (T.hodge (U.hodge alpha)).1
    rw [U.restricts, T.restricts]

end AtomicNaturalHodgeOperator

/-- A geometric/ambient realization of the complete rank-free GST matrix-unit
arsenal.  This is an explicit reduction interface, not a field of the genuine
cycle-class semantics. -/
structure AtomicNaturalMatrixArsenal
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) where
  realize : ∀ i j : ClassicalHodgeBasisIndex V H p,
    AtomicNaturalHodgeOperator V H p
  hodge_action : ∀ i j,
    (realize i j).hodge = hodgeMatrixUnit i j

namespace AtomicNaturalMatrixArsenal

/-- The realized matrix-unit family makes the algebraic Hodge subspace
rank-free invariant. -/
theorem rankFreeInvariant
    (A : AtomicNaturalMatrixArsenal V H p) :
    RankFreeArsenalInvariant (AlgebraicHodgeSubspace V H p) := by
  intro i j alpha halpha
  have hpres := (A.realize i j).preserves_algebraicHodge halpha
  simpa [A.hodge_action i j] using hpres

/-- One nonzero algebraic seed plus an independently realized atomic-natural
matrix arsenal saturates the whole Hodge fiber. -/
theorem algebraicHodgeSubspace_eq_top
    (A : AtomicNaturalMatrixArsenal V H p)
    (hseed : AlgebraicHodgeSubspace V H p ≠ ⊥) :
    AlgebraicHodgeSubspace V H p = ⊤ :=
  rankFreeArsenalInvariant_eq_top
    (AlgebraicHodgeSubspace V H p) A.rankFreeInvariant hseed

/-- Equivalent atomic-defect extinction in one weight. -/
theorem atomicDefect_eq_zero
    (A : AtomicNaturalMatrixArsenal V H p)
    (hseed : AlgebraicHodgeSubspace V H p ≠ ⊥) :
    atomicDefectLinearMap V H p = 0 :=
  atomicDefect_eq_zero_of_seed_and_arsenal A.rankFreeInvariant hseed

end AtomicNaturalMatrixArsenal

/-- **EQUIVARIANT IRREDUCIBILITY CROWN.**  For every nontrivial Hodge weight,
one algebraic seed plus independently constructed atomic-natural realizations
of the rank-free GST matrix units implies the Stage-2G Hodge statement. -/
theorem bigradedBettiHodge_of_atomicNaturalMatrixArsenal
    (A : ∀ p : Nat,
      rationalHodgeSubspace (H.hodgeBigrading p) ≠ ⊥ →
        AtomicNaturalMatrixArsenal V H p)
    (hseed : ∀ p : Nat,
      rationalHodgeSubspace (H.hodgeBigrading p) ≠ ⊥ →
        AlgebraicHodgeSubspace V H p ≠ ⊥) :
    BigradedBettiHodgeStatement V H := by
  apply (bigradedBettiHodgeStatement_iff_atomicDefect_zero V H).2
  intro q
  by_cases hq : rationalHodgeSubspace (H.hodgeBigrading q) = ⊥
  · apply LinearMap.ext
    intro alpha
    have halpha : alpha = 0 := by
      apply Subtype.ext
      have hz : alpha.1 ∈
          (⊥ : Submodule ℚ
            (RationalSingularCohomology H.analytification (2 * q))) := by
        simpa [hq] using alpha.2
      simpa using hz
    subst alpha
    simp
  · exact (A q hq).atomicDefect_eq_zero (hseed q hq)

#check AtomicNaturalHodgeOperator
#check AtomicNaturalHodgeOperator.defectOperator
#check AtomicNaturalHodgeOperator.defect_equivariant
#check AtomicNaturalHodgeOperator.preserves_algebraicHodge
#check AtomicNaturalHodgeOperator.id
#check AtomicNaturalHodgeOperator.smul
#check AtomicNaturalHodgeOperator.add
#check AtomicNaturalHodgeOperator.comp
#check AtomicNaturalMatrixArsenal
#check AtomicNaturalMatrixArsenal.rankFreeInvariant
#check AtomicNaturalMatrixArsenal.algebraicHodgeSubspace_eq_top
#check AtomicNaturalMatrixArsenal.atomicDefect_eq_zero
#check bigradedBettiHodge_of_atomicNaturalMatrixArsenal

#print axioms AtomicNaturalHodgeOperator.defect_equivariant
#print axioms AtomicNaturalHodgeOperator.preserves_algebraicHodge
#print axioms AtomicNaturalMatrixArsenal.rankFreeInvariant
#print axioms AtomicNaturalMatrixArsenal.atomicDefect_eq_zero
#print axioms bigradedBettiHodge_of_atomicNaturalMatrixArsenal

end GSTClassicalHodgeAtomicDefectEquivariantIrreducibility
