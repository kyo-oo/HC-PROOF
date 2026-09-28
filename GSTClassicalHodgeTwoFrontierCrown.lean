import GSTClassicalHodgeZeroWeightLocalSeed
import GSTClassicalHodgeProjectiveDegreeTrace
import GSTClassicalHodgePointwiseNativeCosmicClosure

/-!
# GST CLASSICAL HODGE — TWO-FRONTIER CROWN

Projective degree eliminates the homology-escape branch for the canonical
separator successor.  Consequently the global Stage-2G closure now depends on
only two genuinely geometric frontiers:

1. in each positive live Hodge weight p+1, produce one codimension-p source
   whose canonical separator successor lands in exact ambient codimension p+1;
2. from the source coordinate selected by the resulting nonzero algebraic
   Hodge seed, realize each canonical limitless GST source-to-target matrix-unit
   image of every genuine point-cycle generator by some actual native cycle.

Weight zero is independent: projective degree already supplies a nonzero
codimension-zero algebraic Hodge seed from a generic component atom.

No global no-escape hypothesis remains.  No global native operator or global
matrix-unit naturality is assumed.
-/

set_option maxHeartbeats 90000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeTwoFrontierCrown

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeSynchronizedDefectOrbit
open GSTClassicalHodgePointwiseNativeCosmicClosure
open GSTClassicalHodgeZeroWeightLocalSeed
open GSTClassicalHodgeProjectiveDegreeTrace
open GSTClassicalHodgeProjectiveDegreeTrace.ProjectiveDegreeTraceSemantics
open GSTClassicalHodgePointClosureRelativeCut
open GSTClassicalHodgeRelativeSuccessorNonempty

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Positive-weight geometry packet: one source point and the exact ambient
next-stratum law for its canonical separator successor. -/
structure PositiveWeightCanonicalSuccessor
    (p : Nat) where
  source : CodimensionPoint V.X p
  live : ProjectivelyLiveSource V.projective.n
    (V.projective.immersion source.1)
  ambient_exact :
    Order.coheight
      (ambientSuccessorPoint V source.1
        (relativeHeightOneSeparatorSuccessor V source.1 live)) = p + 1

/-- Projective degree turns one exact canonical successor directly into a
nonzero native algebraic Hodge seed.  There is no escape branch. -/
noncomputable def positiveWeightSeed
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat)
    (S : PositiveWeightCanonicalSuccessor (V := V) p) :
    NativeHodgeOrbitSeed (V := V) (H := H) (p := p + 1) :=
  separator_successor_nativeHodgeSeed
    G D p S.source S.live S.ambient_exact

/-- Uniform seed selector: degree at weight zero, exact separator successor at
positive weights. -/
noncomputable def frontierSeed
    [Nonempty V.X]
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
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
      exact positiveWeightSeed G D p (positive p (by simpa using hq))

/-- **TWO-FRONTIER GLOBAL CROWN.**
One exact canonical successor in every positive live weight, together with only
live-source generatorwise native cosmic point lifts, implies the full classical
Stage-2G Hodge statement. -/
theorem bigradedBettiHodge_of_two_frontiers
    [Nonempty V.X]
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (positive : ∀ p : Nat,
      rationalHodgeSubspace (H.hodgeBigrading (p + 1)) ≠ ⊥ →
        PositiveWeightCanonicalSuccessor (V := V) p)
    (hLift : ∀ q : Nat,
      ∀ hq : rationalHodgeSubspace (H.hodgeBigrading q) ≠ ⊥,
      ∀ j : ClassicalHodgeBasisIndex V H q,
        CosmicNativePointLifts (V := V) (H := H)
          (frontierSeed G D positive q hq).sourceIndex j) :
    BigradedBettiHodgeStatement V H := by
  exact bigradedBettiHodge_of_liveSource_pointLifts
    (seed := fun q hq => frontierSeed G D positive q hq)
    hLift

/-- Contrapositive formulation: any genuine Hodge failure forces failure of at
least one of the two remaining geometric frontiers. -/
theorem failure_forces_two_frontier_break
    [Nonempty V.X]
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (hnot : ¬ BigradedBettiHodgeStatement V H) :
    ¬ (
      ∃ positive : ∀ p : Nat,
        rationalHodgeSubspace (H.hodgeBigrading (p + 1)) ≠ ⊥ →
          PositiveWeightCanonicalSuccessor (V := V) p,
      ∀ q : Nat,
      ∀ hq : rationalHodgeSubspace (H.hodgeBigrading q) ≠ ⊥,
      ∀ j : ClassicalHodgeBasisIndex V H q,
        CosmicNativePointLifts (V := V) (H := H)
          (frontierSeed G D positive q hq).sourceIndex j) := by
  rintro ⟨positive, hLift⟩
  exact hnot (bigradedBettiHodge_of_two_frontiers G D positive hLift)

#check PositiveWeightCanonicalSuccessor
#check positiveWeightSeed
#check frontierSeed
#check bigradedBettiHodge_of_two_frontiers
#check failure_forces_two_frontier_break

#print axioms positiveWeightSeed
#print axioms bigradedBettiHodge_of_two_frontiers
#print axioms failure_forces_two_frontier_break

end GSTClassicalHodgeTwoFrontierCrown
