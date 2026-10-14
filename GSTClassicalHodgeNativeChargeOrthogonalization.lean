import GSTClassicalHodgeActualCommutatorRankGain

/-!
# GST actual native-cycle charge orthogonalization

This replaces the restrictive "a NONZERO noncommutative commutator exists
and is killed by the charge" hypothesis with a source-agnostic construction
from ANY actual native algebraic cycle Z.

We explicitly subtract the measured projective-spine component of Z.
The resulting cycle has identically zero conserved charge. Whenever Z's
Betti class was not already on the spine line, the constructed class is
nonzero and a second algebraically realized Hodge direction.

The theorem DOES NOT assert existence of an outside-spine native cycle on
every smooth projective variety. That unconditional existence statement
would be a substantive part of the general rational Hodge conjecture.
-/

set_option maxHeartbeats 7000000

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
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeAtomicSpan

namespace GSTClassicalHodgeNativeChargeOrthogonalization

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- An ACTUAL algebraic cycle with its measured projective-spine component
removed. Uses only native cycle operations and the conserved geometric
charge. No target-cycle witness or commutator existence is an argument. -/
noncomputable def chargeOrthogonalNative
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge G)
    (p : Nat) (Z : codimensionCycles V.X p) :
    codimensionCycles V.X p :=
  Z - (D.nativeRead p Z / D.nativeRead p (spineNativeTower G p)) •
    spineNativeTower G p

/-- Exact native/Bettian orthogonalization identity. -/
theorem chargeOrthogonalNative_cycleClass
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge G)
    (p : Nat) (Z : codimensionCycles V.X p) :
    H.cycleClass p (chargeOrthogonalNative G D p Z) =
      H.cycleClass p Z -
        (D.nativeRead p Z / D.nativeRead p (spineNativeTower G p)) •
          (spineHodgeSeed G p).1 := by
  simp [chargeOrthogonalNative, map_sub, map_smul,
    spineNativeTower_cycleClass]

/-- The manufactured native cycle always has ZERO charge, even when the
initial cycle did not. This removes the charge-eigenoperator requirements of
the old commutator-based rank-two argument. -/
theorem chargeOrthogonalNative_charge_zero
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge G)
    (p : Nat) (Z : codimensionCycles V.X p) :
    D.cohomologyRead p
      (H.cycleClass p (chargeOrthogonalNative G D p Z)) = 0 := by
  rw [D.cycleClass_read p (chargeOrthogonalNative G D p Z)]
  change D.nativeRead p
    (Z - (D.nativeRead p Z / D.nativeRead p (spineNativeTower G p)) •
      spineNativeTower G p) = 0
  rw [map_sub, map_smul, smul_eq_mul]
  have hnonzero := D.nativeRead_spineNativeTower_ne_zero p
  field_simp [hnonzero]
  ring

/-- Any actual cycle outside the projective-spine line gives a genuinely
NONZERO new geometric Hodge direction after charge orthogonalization. -/
theorem chargeOrthogonalNative_nonzero_of_not_collinear
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge G)
    (p : Nat) (Z : codimensionCycles V.X p)
    (houtside : ∀ c : ℚ,
      H.cycleClass p Z ≠ c • (spineHodgeSeed G p).1) :
    H.cycleClass p (chargeOrthogonalNative G D p Z) ≠ 0 := by
  intro hz
  rw [chargeOrthogonalNative_cycleClass G D p Z] at hz
  exact houtside _ (sub_eq_zero.mp hz)

/-- Rank-two rational Hodge realization from ANY actual algebraic cycle
outside the GST spine line: no commutator or determinant is required.
In contrast to a supplied Hodge preimage, Z is an arbitrary genuine native
cycle which can be independently obtained from incidence/projective geometry.
The only geometric nondegeneracy obligation is its noncollinearity with the
constructed spine, now separated from the proof's linear-algebraic engine. -/
theorem rank_two_hodge_of_any_noncollinear_native_cycle
    (G : GeometricCycleClassSpine V H)
    (D : SpineTowerConservedCharge G)
    (p : Nat) (Z : codimensionCycles V.X p)
    (houtside : ∀ c : ℚ,
      H.cycleClass p Z ≠ c • (spineHodgeSeed G p).1)
    [FiniteDimensional ℚ (ClassicalHodgeFiber V H p)]
    (hrank : Module.finrank ℚ (ClassicalHodgeFiber V H p) = 2)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p)) :
    ∃ W : codimensionCycles V.X p, H.cycleClass p W = alpha := by
  let Zorth := chargeOrthogonalNative G D p Z
  let t : ClassicalHodgeFiber V H p :=
    ⟨H.cycleClass p Zorth, G.algebraic_is_hodge p Zorth⟩
  have hzero : D.cohomologyRead p t.1 = 0 :=
    chargeOrthogonalNative_charge_zero G D p Z
  have htne : t.1 ≠ 0 :=
    chargeOrthogonalNative_nonzero_of_not_collinear G D p Z houtside
  have hLI : LinearIndependent ℚ
      ![spineHodgeSeed G p, t] := by
    apply (LinearIndependent.pair_iff).2
    intro a b hab
    have hval : a • (spineHodgeSeed G p).1 + b • t.1 = 0 := by
      have h := congrArg Subtype.val hab
      simpa [Submodule.coe_add, Submodule.coe_smul_of_tower] using h
    have hread :
        a * D.cohomologyRead p (spineHodgeSeed G p).1 +
          b * D.cohomologyRead p t.1 = 0 := by
      have h := congrArg (D.cohomologyRead p) hval
      simpa only [map_add, map_smul, map_zero, smul_eq_mul] using h
    have hamul : a * D.cohomologyRead p (spineHodgeSeed G p).1 = 0 := by
      simpa [hzero] using hread
    have ha : a = 0 :=
      (mul_eq_zero.mp hamul).resolve_right
        (GSTClassicalHodgeActualCommutatorRankGain.actualSpine_betti_charge_nonzero G D)
    subst a
    have hbsmul : b • t.1 = 0 := by
      simpa using hval
    have hb : b = 0 := (smul_eq_zero.mp hbsmul).resolve_right htne
    exact ⟨rfl, hb⟩
  have hspan :
      Submodule.span ℚ
        (Set.range (![spineHodgeSeed G p, t] :
          Fin 2 → ClassicalHodgeFiber V H p)) = ⊤ :=
    hLI.span_eq_top_of_card_eq_finrank' (by simpa [hrank])
  let S := AlgebraicHodgeSubspace V H p
  have hseed : spineHodgeSeed G p ∈ S :=
    spineHodgeSeed_algebraic G p
  have htarget : t ∈ S := by
    change H.cycleClass p Zorth ∈ pointCycleClassSpan p (H.cycleClass p)
    rw [← smoothProjective_cycleClass_range_eq_atomic_span V H p]
    exact ⟨Zorth, rfl⟩
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

/-! ## The stronger rank-two theorem WITHOUT a global conserved charge

The global conserved charge in older GST files forces a nonzero spine in
EVERY weight, including those where the Hodge fiber can vanish. For genuine
finite-dimensional varieties that cannot be the universal requirement.

The right geometry requires a nonzero native spine only at the weight under
investigation, and an INDEPENDENT second genuine native cycle. The second
class need not arise as a commutator, preserve a charge, or satisfy a period
identity. -/

/-- In any zero Hodge fiber, the old global charge hypothesis is impossible:
it demands a nonzero element in this fiber. This is a formal *consistency
obstruction* to using that global hypothesis on ordinary bounded-degree
cohomology. -/
theorem global_spine_charge_impossible_of_zero_hodge_fiber
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    [Subsingleton (ClassicalHodgeFiber V H p)] :
    ¬ Nonempty (SpineTowerConservedCharge G) := by
  rintro ⟨D⟩
  exact D.spineHodgeSeed_ne_zero p
    (Subsingleton.elim (spineHodgeSeed G p) 0)

/-- Full rank-two realization from TWO genuinely native geometric cycles,
with NO global conserved-charge structure and NO commutator hypothesis.
The pre-existing native GST spine supplies the first vector. Any second
actual native cycle with a noncollinear class completes the weight-two
algebraic representation.

This is applicable in finite-dimensional projective geometry where a
global nonzero charge at every degree is not possible. -/
theorem rank_two_hodge_without_global_charge
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (hspine : spineHodgeSeed G p ≠ 0)
    (Z : codimensionCycles V.X p)
    (houtside : ∀ c : ℚ,
      H.cycleClass p Z ≠ c • (spineHodgeSeed G p).1)
    [FiniteDimensional ℚ (ClassicalHodgeFiber V H p)]
    (hrank : Module.finrank ℚ (ClassicalHodgeFiber V H p) = 2)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p)) :
    ∃ W : codimensionCycles V.X p, H.cycleClass p W = alpha := by
  let t : ClassicalHodgeFiber V H p :=
    ⟨H.cycleClass p Z, G.algebraic_is_hodge p Z⟩
  have hLI : LinearIndependent ℚ
      ![spineHodgeSeed G p, t] := by
    apply (LinearIndependent.pair_iff' hspine).2
    intro c hc
    have hcol : H.cycleClass p Z =
        c • (spineHodgeSeed G p).1 := by
      have h := congrArg Subtype.val hc
      simpa [t, Submodule.coe_smul_of_tower] using h.symm
    exact houtside c hcol
  have hspan :
      Submodule.span ℚ
        (Set.range (![spineHodgeSeed G p, t] :
          Fin 2 → ClassicalHodgeFiber V H p)) = ⊤ :=
    hLI.span_eq_top_of_card_eq_finrank' (by simpa [hrank])
  let S := AlgebraicHodgeSubspace V H p
  have hseed : spineHodgeSeed G p ∈ S :=
    spineHodgeSeed_algebraic G p
  have ht : t ∈ S := by
    change H.cycleClass p Z ∈ pointCycleClassSpan p (H.cycleClass p)
    rw [← smoothProjective_cycleClass_range_eq_atomic_span V H p]
    exact ⟨Z, rfl⟩
  have hS : S = ⊤ := by
    apply top_unique
    rw [← hspan]
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    fin_cases i
    · simpa using hseed
    · simpa using ht
  have hmem : (⟨alpha, halpha⟩ :
      ClassicalHodgeFiber V H p) ∈ S := by
    rw [hS]
    trivial
  change alpha ∈ pointCycleClassSpan p (H.cycleClass p) at hmem
  rw [← smoothProjective_cycleClass_range_eq_atomic_span V H p] at hmem
  exact hmem

#check chargeOrthogonalNative
#check chargeOrthogonalNative_cycleClass
#check chargeOrthogonalNative_charge_zero
#check chargeOrthogonalNative_nonzero_of_not_collinear
#check rank_two_hodge_of_any_noncollinear_native_cycle
#check global_spine_charge_impossible_of_zero_hodge_fiber
#check rank_two_hodge_without_global_charge

#print axioms chargeOrthogonalNative_charge_zero
#print axioms rank_two_hodge_of_any_noncollinear_native_cycle
#print axioms global_spine_charge_impossible_of_zero_hodge_fiber
#print axioms rank_two_hodge_without_global_charge

end GSTClassicalHodgeNativeChargeOrthogonalization
