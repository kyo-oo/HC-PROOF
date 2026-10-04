import GSTClassicalHodgeGSTExactFinale
import GSTClassicalHodgeProjectiveWordOrbit

/-!
# GST CLASSICAL HODGE — CANONICAL-SPINE PROJECTIVE-WORD EXACT FINALE

This file removes the last packaging gap between the genuine projective-word
operator algebra and the exact GST finale.

The canonical projective spine already supplies, in every weight, one actual
native algebraic cycle with a nonzero Hodge coordinate.  A projective operator
word is built only from genuine scheme self-maps by finite addition, rational
scaling and noncommutative composition; its cohomological action is forced by
cycle-class naturality.

Accordingly, to compile a source-to-target GST program we do not assume a
basis-cycle witness, a native matrix-unit lift, or target algebraicity.  We
supply only an actual projective word and prove its action on the single
canonical spine source.  `GSTSourceTargetProgram.ofProjectiveWord` then turns
that geometric word into the source-local GST program, and `GSTExactFinale`
returns the literal rational Hodge statement.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeGSTProjectiveWordExactFinale

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeLimitlessSpinePropagation
open GSTClassicalHodgeGSTSpineGlobalSource
open GSTClassicalHodgeProjectiveWordOrbit
open GSTClassicalHodgeGSTSourceProgramCompiler
open GSTClassicalHodgeGSTDefectExtinction
open GSTClassicalHodgeGSTExactFinale
open GSTClassicalHodgeExactClayStatement

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Compile an actual same-weight projective word into the source-specific GST
program used by the exact finale.  The only equation required is the word's
cohomological action on the already-constructed canonical algebraic spine
source. -/
noncomputable def canonicalSpineProgramOfProjectiveWord
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (p : Nat)
    (j : ClassicalHodgeBasisIndex V H p)
    (W : ProjectiveOperatorWord V p)
    (hW :
      (W.operatorPair G).cohomologyOperator
          (globalSpineOrbitSeed G M p).hodge.1 =
        (classicalHodgeBasis V H p).repr
            (globalSpineOrbitSeed G M p).hodge
            (globalSpineOrbitSeed G M p).sourceIndex •
          (classicalHodgeBasis V H p j).1) :
    CanonicalSpineGSTProgram G M p j :=
  GSTSourceTargetProgram.ofProjectiveWord
    G (globalSpineOrbitSeed G M p) j
    { word := W
      source_action := hW }

/-- The same genuine projective word already constructs an explicit native
cycle whose class is the requested Hodge basis sheet. -/
noncomputable def canonicalSpineTargetCycleOfProjectiveWord
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (p : Nat)
    (j : ClassicalHodgeBasisIndex V H p)
    (W : ProjectiveOperatorWord V p)
    (hW :
      (W.operatorPair G).cohomologyOperator
          (globalSpineOrbitSeed G M p).hodge.1 =
        (classicalHodgeBasis V H p).repr
            (globalSpineOrbitSeed G M p).hodge
            (globalSpineOrbitSeed G M p).sourceIndex •
          (classicalHodgeBasis V H p j).1) :
    GSTGeometricRealizationStage2D.codimensionCycles V.X p :=
  (canonicalSpineProgramOfProjectiveWord G M p j W hW).targetCycle

/-- Exact receipt for the cycle manufactured by the canonical-spine projective
word compiler. -/
theorem canonicalSpineTargetCycleOfProjectiveWord_spec
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (p : Nat)
    (j : ClassicalHodgeBasisIndex V H p)
    (W : ProjectiveOperatorWord V p)
    (hW :
      (W.operatorPair G).cohomologyOperator
          (globalSpineOrbitSeed G M p).hodge.1 =
        (classicalHodgeBasis V H p).repr
            (globalSpineOrbitSeed G M p).hodge
            (globalSpineOrbitSeed G M p).sourceIndex •
          (classicalHodgeBasis V H p j).1) :
    H.cycleClass p
        (canonicalSpineTargetCycleOfProjectiveWord G M p j W hW) =
      (classicalHodgeBasis V H p j).1 := by
  exact (canonicalSpineProgramOfProjectiveWord G M p j W hW).targetCycle_spec

/-- **PROJECTIVE-WORD GST EXACT FINALE — ALGEBRAIC-CYCLE FORM.**
If, for every weight and target sheet, an actual finite projective word has the
GST-predicted action on the single canonical spine source, every rational
Hodge class is the class of a genuine rational algebraic cycle. -/
theorem everyHodgeClassIsRationalAlgebraic_of_canonicalSpine_projectiveWords
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (W : ∀ p : Nat,
      ∀ j : ClassicalHodgeBasisIndex V H p,
        ProjectiveOperatorWord V p)
    (hW : ∀ p : Nat,
      ∀ j : ClassicalHodgeBasisIndex V H p,
        ((W p j).operatorPair G).cohomologyOperator
            (globalSpineOrbitSeed G M p).hodge.1 =
          (classicalHodgeBasis V H p).repr
              (globalSpineOrbitSeed G M p).hodge
              (globalSpineOrbitSeed G M p).sourceIndex •
            (classicalHodgeBasis V H p j).1) :
    EveryHodgeClassIsRationalAlgebraic H := by
  let R : CanonicalSpineGSTProgramFamily G M :=
    fun p j => canonicalSpineProgramOfProjectiveWord G M p j (W p j) (hW p j)
  exact gst_everyHodgeClassIsRationalAlgebraic G M R

/-- **LITERAL WORDING OF THE RATIONAL HODGE CONJECTURE.**
Under the same genuine projective-word source-action theorem, every rational
`(p,p)` Hodge class is a finite rational linear combination of genuine
codimension-p irreducible algebraic cycle classes. -/
theorem everyHodgeClassIsFiniteRationalCombination_of_canonicalSpine_projectiveWords
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (W : ∀ p : Nat,
      ∀ j : ClassicalHodgeBasisIndex V H p,
        ProjectiveOperatorWord V p)
    (hW : ∀ p : Nat,
      ∀ j : ClassicalHodgeBasisIndex V H p,
        ((W p j).operatorPair G).cohomologyOperator
            (globalSpineOrbitSeed G M p).hodge.1 =
          (classicalHodgeBasis V H p).repr
              (globalSpineOrbitSeed G M p).hodge
              (globalSpineOrbitSeed G M p).sourceIndex •
            (classicalHodgeBasis V H p j).1) :
    EveryHodgeClassIsFiniteRationalCombination H := by
  let R : CanonicalSpineGSTProgramFamily G M :=
    fun p j => canonicalSpineProgramOfProjectiveWord G M p j (W p j) (hW p j)
  exact gst_everyHodgeClassIsFiniteRationalCombination G M R

#check canonicalSpineProgramOfProjectiveWord
#check canonicalSpineTargetCycleOfProjectiveWord
#check canonicalSpineTargetCycleOfProjectiveWord_spec
#check everyHodgeClassIsRationalAlgebraic_of_canonicalSpine_projectiveWords
#check everyHodgeClassIsFiniteRationalCombination_of_canonicalSpine_projectiveWords

#print axioms canonicalSpineTargetCycleOfProjectiveWord_spec
#print axioms everyHodgeClassIsRationalAlgebraic_of_canonicalSpine_projectiveWords
#print axioms everyHodgeClassIsFiniteRationalCombination_of_canonicalSpine_projectiveWords

end GSTClassicalHodgeGSTProjectiveWordExactFinale
