import GSTClassicalHodgeProjectiveDegreeTrace

/-!
# GST CLASSICAL HODGE — PRINCIPAL-CUT NONVANISHING FORCES AN EXACT SUCCESSOR

The geometry-built principal-cut operator is defined by filtering the finite
relative codimension-one locus through the exact ambient codimension `p+1`
stratum.  Previously the seed route supplied one ambient-exact successor as an
external geometric input.

This file reverses that dependency.

If the genuine principal-cut cohomology action on one actual point-cycle class
is nonzero, then cycle-class naturality forces the corresponding native
principal-cut cycle to be nonzero.  But that native cycle is a finite sum of
only exact-stratum atoms with coefficient `+1`; therefore at least one actual
relative successor must lie in ambient codimension `p+1`.

Once projective degree/Betti trace semantics are available, the same exact
survivor gives positive Betti trace.  Hence the principal-cut image itself is a
nonzero algebraic Hodge class and supplies the synchronized native Hodge seed.

No catenary/height-additivity hypothesis, Hodge-basis representative, matrix
unit naturality, or Hodge-surjectivity premise occurs here.
-/

set_option maxHeartbeats 80000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgePrincipalCutNonzeroForcesExactSuccessor

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgePointClosureRelativeCut
open GSTClassicalHodgePrincipalCutSuccessorOperator
open GSTClassicalHodgeSingleExactSuccessorSurvival
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeProjectiveDegreeTrace
open GSTClassicalHodgeSynchronizedDefectOrbit
open GSTClassicalHodgeFiberedCosmology

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- **NATIVE NONVANISHING RECOVERS THE EXACT AMBIENT STRATUM.**

The principal-cut point image can only be nonzero if at least one relative
codimension-one successor survives the operator's exact ambient codimension
filter. -/
theorem exists_exact_relative_successor_of_native_point_nonzero
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hNative :
      successorNativeOperator V p (codimensionPointCycle V.X p x) ≠ 0) :
    ∃ y : {y : pointClosureScheme V x.1 // Order.coheight y = 1},
      y ∈ relativeCodimensionOneFinset V x.1 ∧
      Order.coheight (ambientSuccessorPoint V x.1 y) = p + 1 := by
  by_contra hEx
  have hbad :
      ∀ y : {y : pointClosureScheme V x.1 // Order.coheight y = 1},
        y ∈ relativeCodimensionOneFinset V x.1 →
        Order.coheight (ambientSuccessorPoint V x.1 y) ≠ p + 1 := by
    intro y hy hExact
    apply hEx
    exact ⟨y, hy, hExact⟩
  apply hNative
  rw [successorNativeOperator_point]
  have hpres : successorPresentation V p x = 0 := by
    classical
    unfold successorPresentation
    apply Finset.sum_eq_zero
    intro y hy
    exact successorAtomPresentation_eq_zero V p x y (hbad y hy)
  rw [hpres]
  simp

/-- **COHOMOLOGICAL NONVANISHING RECOVERS AN EXACT GEOMETRIC SUCCESSOR.**

Because the geometric cycle-class spine gives an exact commuting square for
the actual principal-cut operator, a nonzero cohomological point image forces
its native point image to be nonzero.  The preceding theorem then extracts an
actual ambient codimension-`p+1` successor. -/
theorem exists_exact_relative_successor_of_principalCut_point_nonzero
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hCoh :
      (G.principalCutPair p).cohomologyOperator
          (H.cycleClass p (codimensionPointCycle V.X p x)) ≠ 0) :
    ∃ y : {y : pointClosureScheme V x.1 // Order.coheight y = 1},
      y ∈ relativeCodimensionOneFinset V x.1 ∧
      Order.coheight (ambientSuccessorPoint V x.1 y) = p + 1 := by
  apply exists_exact_relative_successor_of_native_point_nonzero
    (V := V) p x
  intro hNative
  have hnat :=
    (G.principalCutPair p).cycleClass_natural
      (codimensionPointCycle V.X p x)
  rw [G.principalCutPair_native p, hNative, LinearMap.map_zero] at hnat
  exact hCoh hnat.symm

/-- **NONZERO PRINCIPAL-CUT ACTION PRODUCES A GENUINE ALGEBRAIC HODGE SEED.**

Projective degree converts the exact successor recovered from cohomological
nonvanishing into positive Betti trace.  Therefore the actual principal-cut
cycle has nonzero cycle class and is a nonzero algebraic Hodge state in weight
`p+1`. -/
noncomputable def nativeHodgeSeed_of_principalCut_point_nonzero
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hCoh :
      (G.principalCutPair p).cohomologyOperator
          (H.cycleClass p (codimensionPointCycle V.X p x)) ≠ 0) :
    NativeHodgeOrbitSeed (V := V) (H := H) (p := p + 1) := by
  obtain ⟨y, hyMem, hyExact⟩ :=
    exists_exact_relative_successor_of_principalCut_point_nonzero
      (V := V) (H := H) G p x hCoh
  let Z : codimensionCycles V.X (p + 1) :=
    successorNativeOperator V p (codimensionPointCycle V.X p x)
  have hclass : H.cycleClass (p + 1) Z ≠ 0 := by
    intro hzero
    have hpos := D.trace_successor_positive_of_one_exact
      p x y hyMem hyExact
    rw [show H.cycleClass (p + 1)
          (successorNativeOperator V p (codimensionPointCycle V.X p x)) = 0 by
          simpa [Z] using hzero,
        LinearMap.map_zero] at hpos
    exact (lt_irrefl 0 hpos)
  let alpha : ClassicalHodgeFiber V H (p + 1) :=
    ⟨H.cycleClass (p + 1) Z, G.algebraic_is_hodge (p + 1) Z⟩
  refine {
    cycle := Z
    hodge := alpha
    hodge_ne_zero := ?_
    class_eq := rfl
  }
  intro hz
  apply hclass
  exact congrArg Subtype.val hz

/-- Existential form consumed by orbit/closure arguments. -/
theorem principalCut_point_nonzero_gives_nativeHodgeSeed
    (G : GeometricCycleClassSpine V H)
    (D : ProjectiveDegreeTraceSemantics V H)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hCoh :
      (G.principalCutPair p).cohomologyOperator
          (H.cycleClass p (codimensionPointCycle V.X p x)) ≠ 0) :
    Nonempty (NativeHodgeOrbitSeed (V := V) (H := H) (p := p + 1)) :=
  ⟨nativeHodgeSeed_of_principalCut_point_nonzero G D p x hCoh⟩

#check exists_exact_relative_successor_of_native_point_nonzero
#check exists_exact_relative_successor_of_principalCut_point_nonzero
#check nativeHodgeSeed_of_principalCut_point_nonzero
#check principalCut_point_nonzero_gives_nativeHodgeSeed

#print axioms exists_exact_relative_successor_of_native_point_nonzero
#print axioms exists_exact_relative_successor_of_principalCut_point_nonzero
#print axioms principalCut_point_nonzero_gives_nativeHodgeSeed

end GSTClassicalHodgePrincipalCutNonzeroForcesExactSuccessor
