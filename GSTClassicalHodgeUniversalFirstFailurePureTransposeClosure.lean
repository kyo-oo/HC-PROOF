import GSTClassicalHodgeFirstFailureBiFiniteTransposePureTransversality

/-!
# GST CLASSICAL HODGE — UNIVERSAL FIRST-FAILURE PURE-TRANSPOSE CLOSURE

The first-failure correspondence route has now reached a smaller geometric
interface than the earlier principal-cut, scalar, pairing, and mod-atomic
returns.

At a least bad successor weight `p+1`, choose one basis state whose atomic
defect is nonzero and its canonical atomic separator.  A single actual
bi-finite correspondence `K` is enough provided:

* its forward image of that one basis state remains Hodge at the good
  predecessor weight `p`;
* the canonical separator reads the genuine transpose round trip `K^t K` on
  that state nontrivially.

The predecessor is defect-free, so the forward Hodge state is algebraic.
Cycle-class naturality of the actual transpose then sends it back into the
successor atomic span, forcing every atomic separator read to vanish.  The
nonzero transverse read is therefore impossible.

This file globalizes that local collision at exactly the first failure.  The
closure no longer assumes a geometric cycle-class spine, degree trace,
primitive decomposition, perfect pairing, principal-cut matching, scalar
return, or matrix-unit realization.  The only geometric witness demanded at a
hypothetical first failure is one genuine bi-finite transpose-transverse
correspondence on one actually defective basis state.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeUniversalFirstFailurePureTransposeClosure

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicDefectDuality
open GSTClassicalHodgeSingleSheetCrown
open GSTClassicalHodgeFiniteClosedCorrespondenceTranspose
open GSTClassicalHodgeFirstPrimitiveProjectiveFailure
open GSTClassicalHodgeFirstFailurePoincareReadCollision
open GSTClassicalHodgeFirstFailureBiFiniteTransposePureTransversality

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- The minimal geometry needed at one possible least bad successor: select one
actually defective basis state and exhibit one genuine bi-finite
transpose-transverse correspondence for its canonical atomic separator. -/
def FirstFailurePureTransposeWitness
    (F : FirstAtomicDefectWeight V H) : Prop :=
  ∃ p : Nat,
  ∃ hp : F.weight = p + 1,
  ∃ i : ClassicalHodgeBasisIndex V H (p + 1),
  ∃ hi : atomicDefectLinearMap V H (p + 1)
      (classicalHodgeBasis V H (p + 1) i) ≠ 0,
  ∃ K : BiFiniteClosedCorrespondence V,
    Nonempty
      (FirstFailureBiFiniteTransposePureTransverse
        (V := V) (H := H) p i
        (basisSeparatorOfDefectNeZero i hi) K)

/-- **UNIVERSAL FIRST-FAILURE PURE-TRANSPOSE CLOSURE.**

If weight zero is defect-free and every possible least nonzero defect admits
one minimal pure-transpose witness, a Stage-2G Hodge counterexample is
impossible. -/
theorem bigradedBettiHodge_of_firstFailurePureTransposeWitness
    (hzero : atomicDefectLinearMap V H 0 = 0)
    (returns : ∀ F : FirstAtomicDefectWeight V H,
      FirstFailurePureTransposeWitness F) :
    BigradedBettiHodgeStatement V H := by
  by_contra hnot
  let F := firstAtomicDefectWeightOfFailure
    (V := V) (H := H) hzero hnot
  rcases returns F with ⟨p, hp, i, hi, K, hK⟩
  rcases hK with ⟨RK⟩
  exact RK.firstFailure_forbids_biFiniteTransposePureTransverse F hp

/-- A witness cannot exist for an actual first-failure packet.  This is the
pointwise contradiction form used by geometric constructors. -/
theorem no_FirstFailurePureTransposeWitness
    (F : FirstAtomicDefectWeight V H) :
    ¬ FirstFailurePureTransposeWitness F := by
  rintro ⟨p, hp, i, hi, K, hK⟩
  rcases hK with ⟨RK⟩
  exact RK.firstFailure_forbids_biFiniteTransposePureTransverse F hp

/-- Equivalent empty-witness formulation: once weight zero is good, proving
that the minimal geometric witness is forced for every putative first failure
closes the complete Hodge statement. -/
theorem firstFailurePureTransposeWitness_empty
    (F : FirstAtomicDefectWeight V H) :
    IsEmpty { _u : Unit // FirstFailurePureTransposeWitness F } := by
  refine ⟨?_⟩
  rintro ⟨_, hW⟩
  exact no_FirstFailurePureTransposeWitness F hW

#check FirstFailurePureTransposeWitness
#check bigradedBettiHodge_of_firstFailurePureTransposeWitness
#check no_FirstFailurePureTransposeWitness
#check firstFailurePureTransposeWitness_empty

#print axioms bigradedBettiHodge_of_firstFailurePureTransposeWitness
#print axioms no_FirstFailurePureTransposeWitness
#print axioms firstFailurePureTransposeWitness_empty

end GSTClassicalHodgeUniversalFirstFailurePureTransposeClosure
