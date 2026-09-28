import GSTClassicalHodgeZeroWeightLocalSeed
import GSTClassicalHodgeSuccessorSeedEscapeDichotomy
import GSTClassicalHodgePointwiseNativeCosmicClosure

/-!
# GST CLASSICAL HODGE — MINIMAL FRONTIER CROWN

This module packages the strongest reduction currently available from the
combined projective / limitless-GST architecture.

The closure is no longer phrased in terms of a global matrix-unit action on the
entire Hodge fiber.

* Weight zero has a canonical nonzero algebraic Hodge seed, supplied by a
  genuine codimension-zero component atom and projective degree trace.
* At weight p+1, one canonically graded separator successor gives either a
  nonzero algebraic Hodge seed or a concrete positive cosmic homology escape.
* Once one nonzero seed is available in a live Hodge weight, only
  source-to-target generatorwise native point lifts of the canonical limitless
  GST matrix units are needed to saturate that whole Hodge weight.

Hence the full Stage-2G statement follows from three sharply geometric laws:

1. one exact canonical separator successor in every nonzero live weight;
2. exclusion of positive-cosmic / Betti-zero homology escapes;
3. generatorwise native point lifts from whatever live source coordinate the
   resulting algebraic seed actually exposes.

No basis cycle representative, global native endomorphism, arbitrary matrix
unit naturality, or Hodge-surjectivity hypothesis is assumed here.
-/

set_option maxHeartbeats 90000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeMinimalFrontierCrown

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeSynchronizedDefectOrbit
open GSTClassicalHodgeSuccessorSeedEscapeDichotomy
open GSTClassicalHodgePointwiseNativeCosmicClosure
open GSTClassicalHodgeZeroWeightLocalSeed
open GSTClassicalHodgePointClosureRelativeCut
open GSTClassicalHodgeRelativeSuccessorNonempty

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Positive-weight geometric source package.  For weight p+1 it gives one
actual codimension-p source point whose distinguished separator successor lands
in the exact next ambient codimension. -/
structure PositiveWeightCanonicalSuccessor
    (p : Nat) where
  source : CodimensionPoint V.X p
  live : ProjectivelyLiveSource V.projective.n
    (V.projective.immersion source.1)
  ambient_exact :
    Order.coheight
      (ambientSuccessorPoint V source.1
        (relativeHeightOneSeparatorSuccessor V source.1 live)) = p + 1

/-- If positive cosmic homology escapes are impossible, every positive live
Hodge weight equipped with one exact canonical separator successor has a
nonzero native algebraic Hodge seed. -/
theorem positiveWeight_seed_of_successor_noEscape
    (G : GeometricCycleClassSpine V H)
    (hNoEscape : ∀ q : Nat,
      IsEmpty (PositiveCosmicHomologyEscape (V := V) (H := H) q))
    (p : Nat)
    (S : PositiveWeightCanonicalSuccessor (V := V) p) :
    Nonempty (NativeHodgeOrbitSeed (V := V) (H := H) (p := p + 1)) := by
  exact separator_successor_seed_of_no_escape
    G hNoEscape p S.source S.live S.ambient_exact

/-- Uniform seed selector assembled from the two genuinely different geometric
mechanisms: projective degree in weight zero and canonical separator survival
in positive weights. -/
noncomputable def frontierSeed
    [Nonempty V.X]
    (G : GeometricCycleClassSpine V H)
    (D : GSTClassicalHodgeProjectiveDegreeTrace.ProjectiveDegreeTraceSemantics V H)
    (hNoEscape : ∀ q : Nat,
      IsEmpty (PositiveCosmicHomologyEscape (V := V) (H := H) q))
    (positive : ∀ p : Nat,
      rationalHodgeSubspace (H.hodgeBigrading (p + 1)) ≠ ⊥ →
        PositiveWeightCanonicalSuccessor (V := V) p)
    (q : Nat)
    (hq : rationalHodgeSubspace (H.hodgeBigrading q) ≠ ⊥) :
    NativeHodgeOrbitSeed (V := V) (H := H) (p := q) := by
  cases q with
  | zero =>
      exact zeroWeightNativeHodgeSeed G D
  | succ p =>
      exact Classical.choice
        (positiveWeight_seed_of_successor_noEscape
          G hNoEscape p (positive p (by simpa using hq)))

/-- **MINIMAL GLOBAL FRONTIER CROWN.**
The full classical Stage-2G Hodge statement follows once:

* every positive live Hodge weight has one exact canonical projective
  separator successor;
* positive-cosmic / Betti-zero homology escapes are excluded; and
* for whichever source coordinate the resulting genuine algebraic seed
  exposes, every target cosmic matrix-unit image of every point generator has
  some native algebraic-cycle lift.

This is strictly weaker than global matrix-unit externalization: the point-lift
law is required only from the actually live seed source coordinate. -/
theorem bigradedBettiHodge_of_minimal_frontier
    [Nonempty V.X]
    (G : GeometricCycleClassSpine V H)
    (D : GSTClassicalHodgeProjectiveDegreeTrace.ProjectiveDegreeTraceSemantics V H)
    (hNoEscape : ∀ q : Nat,
      IsEmpty (PositiveCosmicHomologyEscape (V := V) (H := H) q))
    (positive : ∀ p : Nat,
      rationalHodgeSubspace (H.hodgeBigrading (p + 1)) ≠ ⊥ →
        PositiveWeightCanonicalSuccessor (V := V) p)
    (hLift : ∀ q : Nat,
      ∀ hq : rationalHodgeSubspace (H.hodgeBigrading q) ≠ ⊥,
      ∀ j : ClassicalHodgeBasisIndex V H q,
        CosmicNativePointLifts (V := V) (H := H)
          (frontierSeed G D hNoEscape positive q hq).sourceIndex j) :
    BigradedBettiHodgeStatement V H := by
  exact bigradedBettiHodge_of_liveSource_pointLifts
    (seed := fun q hq => frontierSeed G D hNoEscape positive q hq)
    hLift

/-- Contrapositive form: if Stage-2G fails, at least one of the three frontier
laws must fail.  This is the clean target for the next brute-force layer. -/
theorem failure_forces_frontier_break
    [Nonempty V.X]
    (G : GeometricCycleClassSpine V H)
    (D : GSTClassicalHodgeProjectiveDegreeTrace.ProjectiveDegreeTraceSemantics V H)
    (hnot : ¬ BigradedBettiHodgeStatement V H) :
    ¬ (
      (∃ hNoEscape : ∀ q : Nat,
          IsEmpty (PositiveCosmicHomologyEscape (V := V) (H := H) q),
       ∃ positive : ∀ p : Nat,
          rationalHodgeSubspace (H.hodgeBigrading (p + 1)) ≠ ⊥ →
            PositiveWeightCanonicalSuccessor (V := V) p,
       ∀ q : Nat,
       ∀ hq : rationalHodgeSubspace (H.hodgeBigrading q) ≠ ⊥,
       ∀ j : ClassicalHodgeBasisIndex V H q,
         CosmicNativePointLifts (V := V) (H := H)
           (frontierSeed G D hNoEscape positive q hq).sourceIndex j)) := by
  rintro ⟨hNoEscape, positive, hLift⟩
  exact hnot
    (bigradedBettiHodge_of_minimal_frontier
      G D hNoEscape positive hLift)

#check PositiveWeightCanonicalSuccessor
#check positiveWeight_seed_of_successor_noEscape
#check frontierSeed
#check bigradedBettiHodge_of_minimal_frontier
#check failure_forces_frontier_break

#print axioms positiveWeight_seed_of_successor_noEscape
#print axioms bigradedBettiHodge_of_minimal_frontier
#print axioms failure_forces_frontier_break

end GSTClassicalHodgeMinimalFrontierCrown
