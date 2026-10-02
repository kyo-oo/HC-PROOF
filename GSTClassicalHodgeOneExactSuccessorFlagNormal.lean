import GSTClassicalHodgeSingleExactSuccessorSurvival
import GSTClassicalHodgePrincipalCutFlagNativeReturn
import GSTClassicalHodgePrincipalCutFlagNormalGeometryFirst
import GSTClassicalHodgeAtomicSpan

/-!
# GST CLASSICAL HODGE — ONE-EXACT-SUCCESSOR FLAG-NORMAL RETURN

The existing incidence-transpose crown asks for an exact ambient-codimension
law for every relative successor of a source point in order to obtain a
nonzero diagonal return coefficient.  That is stronger than necessary.

The later single-survivor theorem already proves that ONE relative successor
which survives the ambient codimension filter forces the native principal-cut
image of the source atom to be nonzero.  This file pushes that sharper fact
through the incidence Gram calculation and through the native flag normal.

Consequences:

* one exact successor makes the principal-cut presentation nonzero;
* hence its rational self-energy is strictly positive, in particular nonzero;
* the native flag normal has a nonzero diagonal return on the source atom;
* the correction is an actual native cycle, therefore its cycle class belongs
  to the complete atomic algebraic span;
* whenever an actual bi-finite flag correspondence and transpose naturality are
  supplied, the genuine geometric flag-normal cohomology operator has the same
  nonzero-scaled modulo-atomic return on that point class.

No all-successor exactness, Hodge surjectivity, or arbitrary operator
realization is used.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeOneExactSuccessorFlagNormal

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeSingleExactSuccessorSurvival
open GSTClassicalHodgePrincipalCutSuccessorOperator
open GSTClassicalHodgePrincipalCutIncidenceTransposeCosmology
open GSTClassicalHodgePrincipalCutFlagNativeReturn
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgePrincipalCutFlagCorrespondenceDescent
open GSTClassicalHodgePrincipalCutFlagCorrespondenceDescent.PrincipalCutFlagBiFiniteRealization
open GSTClassicalHodgePrincipalCutFlagNormalGeometryFirst
open GSTClassicalHodgeGradedFiniteClosedCorrespondence

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- One exact surviving relative successor already forces the finite
principal-cut presentation itself to be nonzero. -/
theorem successorPresentation_ne_zero_of_one_exact
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (y : {y : pointClosureScheme V x.1 // Order.coheight y = 1})
    (hyMem : y ∈ relativeCodimensionOneFinset V x.1)
    (hyExact : Order.coheight (ambientSuccessorPoint V x.1 y) = p + 1) :
    successorPresentation V p x ≠ 0 := by
  intro hzero
  have hnative :=
    successorNativeOperator_point_ne_zero_of_one_exact
      V p x y hyMem hyExact
  apply hnative
  rw [successorNativeOperator_point, hzero]
  simp

/-- Therefore ONE exact successor produces a strictly positive self-incidence
energy.  The old all-successor exact-stratum hypothesis is unnecessary for
nondegeneracy of the diagonal return. -/
theorem successorSelfEnergy_pos_of_one_exact
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (y : {y : pointClosureScheme V x.1 // Order.coheight y = 1})
    (hyMem : y ∈ relativeCodimensionOneFinset V x.1)
    (hyExact : Order.coheight (ambientSuccessorPoint V x.1 y) = p + 1) :
    0 < successorSelfEnergy V p x := by
  exact successorSelfEnergy_pos_of_presentation_ne_zero V p x
    (successorPresentation_ne_zero_of_one_exact V p x y hyMem hyExact)

/-- Nonzero form of the one-successor self-energy theorem. -/
theorem successorSelfEnergy_ne_zero_of_one_exact
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (y : {y : pointClosureScheme V x.1 // Order.coheight y = 1})
    (hyMem : y ∈ relativeCodimensionOneFinset V x.1)
    (hyExact : Order.coheight (ambientSuccessorPoint V x.1 y) = p + 1) :
    successorSelfEnergy V p x ≠ 0 :=
  ne_of_gt (successorSelfEnergy_pos_of_one_exact V p x y hyMem hyExact)

/-- **ONE-EXACT-SUCCESSOR INCIDENCE-TRANSPOSE CROWN.**
A chart containing the source has a nonzero diagonal Gram return as soon as
one exact successor survives. -/
theorem principalCut_incidenceTranspose_oneExact_crown
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (sigma : Finset (CodimensionPoint V.X p))
    (x : CodimensionPoint V.X p)
    (hx : x ∈ sigma)
    (y : {y : pointClosureScheme V x.1 // Order.coheight y = 1})
    (hyMem : y ∈ relativeCodimensionOneFinset V x.1)
    (hyExact : Order.coheight (ambientSuccessorPoint V x.1 y) = p + 1) :
    let lambda := successorSelfEnergy V p x
    lambda ≠ 0
      ∧ localSuccessorNormal V p sigma (Finsupp.single x (1 : ℚ)) =
          lambda • Finsupp.single x (1 : ℚ) + successorCrossTalk V p sigma x
      ∧ successorCrossTalk V p sigma x x = 0 := by
  dsimp
  exact ⟨
    successorSelfEnergy_ne_zero_of_one_exact V p x y hyMem hyExact,
    localSuccessorNormal_decomposition V p sigma x,
    successorCrossTalk_apply_self V p sigma x hx⟩

/-- **ONE-EXACT-SUCCESSOR NATIVE FLAG RETURN.**
The native flag normal therefore has a nonzero-scaled diagonal return plus an
actual native correction cycle. -/
theorem localFlagNormalNative_oneExact_crown
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (sigma : Finset (CodimensionPoint V.X p))
    (x : CodimensionPoint V.X p)
    (hx : x ∈ sigma)
    (y : {y : pointClosureScheme V x.1 // Order.coheight y = 1})
    (hyMem : y ∈ relativeCodimensionOneFinset V x.1)
    (hyExact : Order.coheight (ambientSuccessorPoint V x.1 y) = p + 1) :
    let lambda := successorSelfEnergy V p x
    lambda ≠ 0
      ∧ localFlagNormalNative V p sigma (codimensionPointCycle V.X p x) =
          lambda • codimensionPointCycle V.X p x +
            crossTalkCycle V p sigma x
      ∧ (letI : CompactSpace V.X := smoothProjectiveCompactSpace V
          presentationOfNativeCycle V.X p (crossTalkCycle V p sigma x) x = 0) := by
  dsimp
  exact ⟨
    successorSelfEnergy_ne_zero_of_one_exact V p x y hyMem hyExact,
    localFlagNormalNative_point_decomposition V p sigma x,
    crossTalkCycle_sourceCoefficient_zero V p sigma x hx⟩

/-- The cross-talk correction is not merely formal off-diagonal data: it is an
actual native cycle, so its genuine cycle class lies in the complete atomic
algebraic span. -/
theorem crossTalkCycle_cycleClass_mem_atomicSpan
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (sigma : Finset (CodimensionPoint V.X p))
    (x : CodimensionPoint V.X p) :
    H.cycleClass p (crossTalkCycle V p sigma x) ∈
      pointCycleClassSpan p (H.cycleClass p) := by
  rw [← smoothProjective_cycleClass_range_eq_atomic_span V H p]
  exact ⟨crossTalkCycle V p sigma x, rfl⟩

/-- Cycle-class form of the native normal decomposition.  The round-trip error
from the canonical diagonal scalar is an actual algebraic class. -/
theorem localFlagNormalNative_point_mod_atomic
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (sigma : Finset (CodimensionPoint V.X p))
    (x : CodimensionPoint V.X p) :
    H.cycleClass p
        (localFlagNormalNative V p sigma (codimensionPointCycle V.X p x)) -
      successorSelfEnergy V p x •
        H.cycleClass p (codimensionPointCycle V.X p x) ∈
      pointCycleClassSpan p (H.cycleClass p) := by
  have hdec := localFlagNormalNative_point_decomposition V p sigma x
  have heq :
      H.cycleClass p
          (localFlagNormalNative V p sigma (codimensionPointCycle V.X p x)) -
        successorSelfEnergy V p x •
          H.cycleClass p (codimensionPointCycle V.X p x) =
        H.cycleClass p (crossTalkCycle V p sigma x) := by
    rw [hdec, map_add, map_smul]
    abel
  rw [heq]
  exact crossTalkCycle_cycleClass_mem_atomicSpan V H p sigma x

/-- The geometry-first flag normal has exactly the incidence-built native normal
operator.  This is where an actual bi-finite correspondence, through its true
algebraic transpose, meets the one-successor native calculation. -/
theorem principalCutFlagNormalPair_cycleOperator_eq_localFlagNormalNative
    (G : GeometricCycleClassSpine V H)
    {sigma : Finset (CodimensionPoint V.X p)}
    (R : PrincipalCutFlagBiFiniteRealization V p sigma)
    (N : GradedCorrespondencePointNaturality
      R.correspondence.transpose H (p + 1) p) :
    (principalCutFlagNormalPair (G := G) R N).cycleOperator =
      localFlagNormalNative V p sigma := by
  rw [principalCutFlagNormalPair_cycleOperator]
  unfold localFlagNormalNative
  rw [G.principalCutPair_native p]

/-- **GENUINE CORRESPONDENCE POINT RETURN MODULO ATOMIC SPAN.**
Once the finite chart is represented by an actual bi-finite closed
correspondence and its algebraic transpose has ordinary Betti naturality, the
cohomological flag normal returns every chart point to the canonical
self-energy multiple modulo actual algebraic cycle classes. -/
theorem principalCutFlagNormal_point_mod_atomic
    (G : GeometricCycleClassSpine V H)
    {sigma : Finset (CodimensionPoint V.X p)}
    (R : PrincipalCutFlagBiFiniteRealization V p sigma)
    (N : GradedCorrespondencePointNaturality
      R.correspondence.transpose H (p + 1) p)
    (x : CodimensionPoint V.X p) :
    (principalCutFlagNormalPair (G := G) R N).cohomologyOperator
        (H.cycleClass p (codimensionPointCycle V.X p x)) -
      successorSelfEnergy V p x •
        H.cycleClass p (codimensionPointCycle V.X p x) ∈
      pointCycleClassSpan p (H.cycleClass p) := by
  let T := principalCutFlagNormalPair (G := G) R N
  have hnat := T.cycleClass_natural (codimensionPointCycle V.X p x)
  have hcycle :
      T.cycleOperator (codimensionPointCycle V.X p x) =
        localFlagNormalNative V p sigma (codimensionPointCycle V.X p x) := by
    rw [principalCutFlagNormalPair_cycleOperator_eq_localFlagNormalNative
      G R N]
  have hnative := localFlagNormalNative_point_mod_atomic V H p sigma x
  rw [hcycle] at hnat
  rw [← hnat] at hnative
  exact hnative

/-- Final one-successor geometric point packet: the return scalar is provably
nonzero and the genuine correspondence round trip is modulo the full atomic
span. -/
theorem principalCutFlagNormal_point_oneExact_modAtomic_crown
    (G : GeometricCycleClassSpine V H)
    {sigma : Finset (CodimensionPoint V.X p)}
    (R : PrincipalCutFlagBiFiniteRealization V p sigma)
    (N : GradedCorrespondencePointNaturality
      R.correspondence.transpose H (p + 1) p)
    (x : CodimensionPoint V.X p)
    (y : {y : pointClosureScheme V x.1 // Order.coheight y = 1})
    (hyMem : y ∈ relativeCodimensionOneFinset V x.1)
    (hyExact : Order.coheight (ambientSuccessorPoint V x.1 y) = p + 1) :
    let lambda := successorSelfEnergy V p x
    lambda ≠ 0 ∧
      (principalCutFlagNormalPair (G := G) R N).cohomologyOperator
          (H.cycleClass p (codimensionPointCycle V.X p x)) -
        lambda • H.cycleClass p (codimensionPointCycle V.X p x) ∈
          pointCycleClassSpan p (H.cycleClass p) := by
  dsimp
  exact ⟨
    successorSelfEnergy_ne_zero_of_one_exact V p x y hyMem hyExact,
    principalCutFlagNormal_point_mod_atomic G R N x⟩

#check successorPresentation_ne_zero_of_one_exact
#check successorSelfEnergy_ne_zero_of_one_exact
#check principalCut_incidenceTranspose_oneExact_crown
#check localFlagNormalNative_oneExact_crown
#check crossTalkCycle_cycleClass_mem_atomicSpan
#check localFlagNormalNative_point_mod_atomic
#check principalCutFlagNormalPair_cycleOperator_eq_localFlagNormalNative
#check principalCutFlagNormal_point_mod_atomic
#check principalCutFlagNormal_point_oneExact_modAtomic_crown

#print axioms successorSelfEnergy_ne_zero_of_one_exact
#print axioms localFlagNormalNative_point_mod_atomic
#print axioms principalCutFlagNormal_point_mod_atomic
#print axioms principalCutFlagNormal_point_oneExact_modAtomic_crown

end GSTClassicalHodgeOneExactSuccessorFlagNormal
