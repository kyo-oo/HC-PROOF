import GSTClassicalHodgeActualCommutatorRankGain

/-!
# GST single-correspondence charge-wedge rank gain

Unlike a nonzero geometric commutator, one arbitrary realized correspondence
suffices to manufacture a *charge-orthogonal* native algebraic cycle.

For the actual recursive projective spine Z, its Hodge class s = cl(Z),
a genuine realized correspondence T, and a conserved nonzero charge ell, set

  Delta_T = ell(s) * T_native(Z) - ell(T_Betti(s)) * Z.

This is an explicit native algebraic cycle. Its Betti charge is identically
zero; no assumption that ell is an eigenfunctional of T is needed.

If cl(Delta_T) is nonzero, this class and s are linearly independent.
Consequently, on a rank-two rational Hodge fiber they generate every Hodge
class as a rational algebraic cycle.

The independent geometric existence problem is to exhibit T for which the
constructed transverse class is nonzero. No universal nonvanishing or target
algebraicity is assumed here.
-/

set_option maxHeartbeats 20000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeLimitlessSpinePropagation
open GSTClassicalHodgeRealizedCorrespondenceExpressionAlgebra
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeActualCommutatorRankGain

namespace GSTClassicalHodgeSingleCorrespondenceRankTwo

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Wedge the already-realized spine with the image of one actual geometric
correspondence. Both scalar coefficients are genuine cohomological charges. -/
noncomputable def nativeChargeWedge
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge G)
    (E : RealizedCorrespondenceExpr V H p) :
    codimensionCycles V.X p :=
  (D.cohomologyRead p (spineHodgeSeed G p).1) •
      E.cycleOperator (spineNativeTower G p) -
    (D.cohomologyRead p
      (E.cohomologyOperator (spineHodgeSeed G p).1)) •
      spineNativeTower G p

/-- Its independently defined Betti-side charge wedge. -/
noncomputable def bettiChargeWedge
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge G)
    (E : RealizedCorrespondenceExpr V H p) :
    RationalSingularCohomology H.analytification (2 * p) :=
  (D.cohomologyRead p (spineHodgeSeed G p).1) •
      E.cohomologyOperator (spineHodgeSeed G p).1 -
    (D.cohomologyRead p
      (E.cohomologyOperator (spineHodgeSeed G p).1)) •
      (spineHodgeSeed G p).1

/-- The native charge wedge and the Betti charge wedge agree by actual
geometric cycle-class naturality, with no target-cycle lifting hypothesis. -/
theorem nativeChargeWedge_cycleClass
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge G)
    (E : RealizedCorrespondenceExpr V H p) :
    H.cycleClass p (nativeChargeWedge G D E) =
      bettiChargeWedge G D E := by
  simp only [nativeChargeWedge, bettiChargeWedge,
    map_sub, map_smul, E.cycleClass_natural,
    spineNativeTower_cycleClass]

/-- The constructed transverse class always has genuine Hodge type. -/
theorem bettiChargeWedge_is_hodge
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge G)
    (E : RealizedCorrespondenceExpr V H p) :
    bettiChargeWedge G D E ∈
      rationalHodgeSubspace (H.hodgeBigrading p) := by
  rw [← nativeChargeWedge_cycleClass G D E]
  exact G.algebraic_is_hodge p _

/-- Exact charge cancellation works for ANY realized correspondence,
not merely for a charge eigenoperator and not merely for commutators. -/
theorem bettiChargeWedge_charge_zero
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge G)
    (E : RealizedCorrespondenceExpr V H p) :
    D.cohomologyRead p (bettiChargeWedge G D E) = 0 := by
  unfold bettiChargeWedge
  simp only [map_sub, map_smul, smul_eq_mul]
  ring

/-- One nonzero transverse wedge supplies a second algebraic Hodge direction,
independent of the nonzero-charge native projective spine. -/
theorem spine_chargeWedge_linearIndependent
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge G)
    (E : RealizedCorrespondenceExpr V H p)
    (htransverse : bettiChargeWedge G D E ≠ 0) :
    LinearIndependent ℚ
      ![(spineHodgeSeed G p).1, bettiChargeWedge G D E] := by
  apply (LinearIndependent.pair_iff).2
  intro a b hab
  have hread :
      a * D.cohomologyRead p (spineHodgeSeed G p).1 +
        b * D.cohomologyRead p (bettiChargeWedge G D E) = 0 := by
    have h := congrArg (D.cohomologyRead p) hab
    simpa only [map_add, map_smul, map_zero, smul_eq_mul] using h
  have haMul :
      a * D.cohomologyRead p (spineHodgeSeed G p).1 = 0 := by
    simpa [bettiChargeWedge_charge_zero G D E] using hread
  have ha : a = 0 :=
    (mul_eq_zero.mp haMul).resolve_right
      (actualSpine_betti_charge_nonzero G D)
  subst a
  have hbSmul : b • bettiChargeWedge G D E = 0 := by
    simpa using hab
  have hb : b = 0 :=
    (smul_eq_zero.mp hbSmul).resolve_right htransverse
  exact ⟨rfl, hb⟩

/-- One genuine geometric correspondence with a nonzero charge wedge
closes every rational Hodge class in a two-dimensional fiber. This strengthens
the two-operator commutator criterion by removing charge-eigenoperator
hypotheses and requiring only one realized geometric action. -/
theorem every_rank_two_hodge_class_of_one_transverse_correspondence
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge G)
    (E : RealizedCorrespondenceExpr V H p)
    (htransverse : bettiChargeWedge G D E ≠ 0)
    [FiniteDimensional ℚ (ClassicalHodgeFiber V H p)]
    (hrank : Module.finrank ℚ (ClassicalHodgeFiber V H p) = 2)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p)) :
    ∃ Z : codimensionCycles V.X p, H.cycleClass p Z = alpha := by
  let t : ClassicalHodgeFiber V H p :=
    ⟨bettiChargeWedge G D E, bettiChargeWedge_is_hodge G D E⟩
  have hLI :
      LinearIndependent ℚ ![spineHodgeSeed G p, t] := by
    apply (LinearIndependent.pair_iff).2
    intro a b hab
    have hval : a • (spineHodgeSeed G p).1 +
        b • bettiChargeWedge G D E = 0 := by
      have h := congrArg Subtype.val hab
      simpa [t, Submodule.coe_add, Submodule.coe_smul_of_tower] using h
    exact (LinearIndependent.pair_iff.mp
      (spine_chargeWedge_linearIndependent G D E htransverse)) a b hval
  have hspan :
      Submodule.span ℚ
        (Set.range (![spineHodgeSeed G p, t] :
          Fin 2 → ClassicalHodgeFiber V H p)) = ⊤ :=
    hLI.span_eq_top_of_card_eq_finrank' (by simpa [hrank])
  let S := AlgebraicHodgeSubspace V H p
  have hseed : spineHodgeSeed G p ∈ S :=
    spineHodgeSeed_algebraic G p
  have htarget : t ∈ S := by
    change bettiChargeWedge G D E ∈
      pointCycleClassSpan p (H.cycleClass p)
    rw [← smoothProjective_cycleClass_range_eq_atomic_span V H p]
    exact ⟨nativeChargeWedge G D E,
      nativeChargeWedge_cycleClass G D E⟩
  have hS : S = ⊤ := by
    apply top_unique
    rw [← hspan]
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    fin_cases i
    · simpa using hseed
    · simpa using htarget
  have hmem : (⟨alpha, halpha⟩ :
      ClassicalHodgeFiber V H p) ∈ S := by
    rw [hS]
    trivial
  change alpha ∈ pointCycleClassSpan p (H.cycleClass p) at hmem
  rw [← smoothProjective_cycleClass_range_eq_atomic_span V H p] at hmem
  exact hmem

#check nativeChargeWedge
#check nativeChargeWedge_cycleClass
#check bettiChargeWedge_is_hodge
#check bettiChargeWedge_charge_zero
#check spine_chargeWedge_linearIndependent
#check every_rank_two_hodge_class_of_one_transverse_correspondence

#print axioms nativeChargeWedge_cycleClass
#print axioms bettiChargeWedge_charge_zero
#print axioms spine_chargeWedge_linearIndependent
#print axioms every_rank_two_hodge_class_of_one_transverse_correspondence

end GSTClassicalHodgeSingleCorrespondenceRankTwo
