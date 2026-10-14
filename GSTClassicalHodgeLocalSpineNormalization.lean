import GSTClassicalHodgeSpineRankOneGeometricRealization

/-!
# Local GST geometric normalization without an impossible global charge

Previous charge-normalized rank-one constructions used
SpineTowerConservedCharge G, a structure demanding a nonzero projective
spine in *every* codimension. That global requirement is impossible in
a bounded Hodge theory with zero higher-weight fibers.

This module constructs the needed rational detector LOCALLY from the
already-existing rational Hodge basis, using a nonzero coordinate of the
genuine geometric projective spine. Thus there is no global charge
assumption, no target-class cycle, no abstract geometric matrix unit, and
no nonvanishing determinant premise.

The formula constructs a native cycle and verifies its exact class for
any rank-one Hodge fiber with a nonzero native projective spine.
-/

set_option maxHeartbeats 9000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeLimitlessSpinePropagation
open GSTClassicalHodgeRankFreeArsenalIrreducibility

namespace GSTClassicalHodgeLocalSpineNormalization

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Choose one nonzero RATIONAL coordinate of the actual geometric spine.
Nonvanishing is proved from the spine and the basis, not postulated as
a global conserved functional. -/
noncomputable def localSpineIndex
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (hne : spineHodgeSeed G p ≠ 0) :
    ClassicalHodgeBasisIndex V H p :=
  Classical.choose (exists_nonzero_hodgeCoordinate hne)

/-- The chosen local detector really reads a nonzero spine coordinate. -/
theorem localSpineIndex_nonzero
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (hne : spineHodgeSeed G p ≠ 0) :
    hodgeCoordinate (localSpineIndex G p hne) (spineHodgeSeed G p) ≠ 0 :=
  Classical.choose_spec (exists_nonzero_hodgeCoordinate hne)

/-- An actual rational scalar determined by the Hodge coordinates of an
input class, not by any assumed native cycle representing that class. -/
noncomputable def localSpineCoefficient
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (hne : spineHodgeSeed G p ≠ 0)
    (alpha : ClassicalHodgeFiber V H p) : ℚ :=
  hodgeCoordinate (localSpineIndex G p hne) alpha /
    hodgeCoordinate (localSpineIndex G p hne) (spineHodgeSeed G p)

/-- Explicit native-cycle construction from a nonzero geometric spine. -/
noncomputable def localSpineCycle
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (hne : spineHodgeSeed G p ≠ 0)
    (alpha : ClassicalHodgeFiber V H p) :
    codimensionCycles V.X p :=
  localSpineCoefficient G p hne alpha • spineNativeTower G p

/-- The locally normalized native cycle realizes EVERY class of a rank-one
rational Hodge fiber. It removes the globally inconsistent conserved-charge
requirement from the earlier closed-form construction. -/
theorem localSpineCycle_cycleClass
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (hne : spineHodgeSeed G p ≠ 0)
    (hrank : Module.finrank ℚ (ClassicalHodgeFiber V H p) = 1)
    (alpha : ClassicalHodgeFiber V H p) :
    H.cycleClass p (localSpineCycle G p hne alpha) = alpha.1 := by
  obtain ⟨c, hc⟩ :=
    (finrank_eq_one_iff_of_nonzero' (spineHodgeSeed G p) hne).mp hrank alpha
  have hread :
      hodgeCoordinate (localSpineIndex G p hne) alpha =
        c * hodgeCoordinate (localSpineIndex G p hne) (spineHodgeSeed G p) := by
    have h := congrArg (hodgeCoordinate (localSpineIndex G p hne)) hc
    simpa only [map_smul, smul_eq_mul] using h.symm
  have hcoeff : localSpineCoefficient G p hne alpha = c := by
    unfold localSpineCoefficient
    rw [hread]
    exact mul_div_cancel_right₀ c (localSpineIndex_nonzero G p hne)
  unfold localSpineCycle
  rw [hcoeff, map_smul, spineNativeTower_cycleClass]
  exact congrArg Subtype.val hc

#check localSpineIndex_nonzero
#check localSpineCoefficient
#check localSpineCycle
#check localSpineCycle_cycleClass

#print axioms localSpineIndex_nonzero
#print axioms localSpineCycle_cycleClass

end GSTClassicalHodgeLocalSpineNormalization
