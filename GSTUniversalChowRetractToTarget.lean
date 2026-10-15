import GSTGeometricRealizationStage2G

/-!
# GST exact descent to an ARBITRARY TARGET VARIETY X

Target:
For every smooth projective complex X, p, and rational (p,p)
Hodge alpha, produce a genuine rational algebraic cycle Z on X.

This module constructs Z on X, not just a primitive on X x X.
It uses an independently geometric Chow correspondence from a source Y,
where the needed Hodge class has actually been represented.

For Y=X x X, a cohomological section is
  alpha |-> pr1^*(alpha) cup pr2^*(h^d)/deg(h^d)
and projection pr1_* is a left inverse.
Native proper pushforward and Betti Gysin must commute with cycleClass.
The source Hodge representatives need independent geometric proofs.
The known universal alternating product primitive alone does not supply them.

No arbitrary target-cycle selector is assumed, and no universal
Hodge theorem is claimed without the concrete geometric source theorem.
-/

set_option maxHeartbeats 5000000
noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G

namespace GSTUniversalChowRetractToTarget

/-- Actual native Chow and rational Betti correspondence for a
source Y and a target X. Every field is geometric input, and
NONE asserts a target Hodge class is algebraic. -/
structure NativeHodgeRetract
    (Y X : SmoothProjectiveComplexScheme)
    (D : HodgeBigradedBettiData Y)
    (H : HodgeBigradedBettiData X)
    (q p : Nat) where
  native :
    codimensionCycles Y.X q →ₗ[ℚ] codimensionCycles X.X p
  betti :
    RationalSingularCohomology D.analytification (2 * q) →ₗ[ℚ]
      RationalSingularCohomology H.analytification (2 * p)
  section :
    RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
      RationalSingularCohomology D.analytification (2 * q)
  section_is_hodge :
    ∀ alpha : RationalSingularCohomology H.analytification (2 * p),
      alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p) →
        section alpha ∈ rationalHodgeSubspace (D.hodgeBigrading q)
  betti_retract :
    ∀ alpha : RationalSingularCohomology H.analytification (2 * p),
      betti (section alpha) = alpha
  cycleClass_natural :
    ∀ Z : codimensionCycles Y.X q,
      H.cycleClass p (native Z) = betti (D.cycleClass q Z)

variable {Y X : SmoothProjectiveComplexScheme}
variable {D : HodgeBigradedBettiData Y}
variable {H : HodgeBigradedBettiData X}
variable {q p : Nat}

/-- Given a SOURCE native cycle for the cohomological section,
construct the actual TARGET rational algebraic cycle, through the
geometrically natural native correspondence. -/
theorem construct_target_cycle_from_source_hodge_lift
    (R : NativeHodgeRetract Y X D H q p)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (hsource :
      ∃ Z : codimensionCycles Y.X q,
        D.cycleClass q Z = R.section alpha) :
    ∃ Z : codimensionCycles X.X p,
      H.cycleClass p Z = alpha := by
  obtain ⟨Z, hZ⟩ := hsource
  refine ⟨R.native Z, ?_⟩
  calc
    H.cycleClass p (R.native Z) =
        R.betti (D.cycleClass q Z) := R.cycleClass_natural Z
    _ = R.betti (R.section alpha) := by rw [hZ]
    _ = alpha := R.betti_retract alpha

/-- Full Hodge on X is DERIVED if X is a true Chow motivic
retract of a source Y with previously established Hodge
algebraicity. There is no target algebraicity assumption. -/
theorem every_target_hodge_class_from_solved_source
    (R : NativeHodgeRetract Y X D H q p)
    (hY : ∀ beta : RationalSingularCohomology D.analytification (2 * q),
      beta ∈ rationalHodgeSubspace (D.hodgeBigrading q) →
        ∃ Z : codimensionCycles Y.X q,
          D.cycleClass q Z = beta) :
    ∀ alpha : RationalSingularCohomology H.analytification (2 * p),
      alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p) →
        ∃ Z : codimensionCycles X.X p,
          H.cycleClass p Z = alpha := by
  intro alpha hAlpha
  exact construct_target_cycle_from_source_hodge_lift R alpha
    (hY (R.section alpha) (R.section_is_hodge alpha hAlpha))

/-- Direct compatibility with the original omniversal GST ghost
separator: the actual target Hodge fiber lies in the native-cycle
range when the geometric retract source has been solved. -/
theorem target_hodge_subset_native_cycleClass_range
    (R : NativeHodgeRetract Y X D H q p)
    (hY : ∀ beta : RationalSingularCohomology D.analytification (2 * q),
      beta ∈ rationalHodgeSubspace (D.hodgeBigrading q) →
        ∃ Z : codimensionCycles Y.X q,
          D.cycleClass q Z = beta) :
    rationalHodgeSubspace (H.hodgeBigrading p) ≤
      LinearMap.range (H.cycleClass p) := by
  intro alpha hAlpha
  obtain ⟨Z, hZ⟩ :=
    every_target_hodge_class_from_solved_source R hY alpha hAlpha
  exact ⟨Z, hZ⟩

/-- Necessary source limitation:
the genuine target of an algebraic source cycle is again algebraic.
It cannot equal a hypothetical target class absent from the native
cycle-class range. A correspondence alone does not manufacture
unrepresented Hodge classes. -/
theorem no_unrepresented_target_from_algebraic_source
    (R : NativeHodgeRetract Y X D H q p)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (hmissing : alpha ∉ LinearMap.range (H.cycleClass p))
    (Z : codimensionCycles Y.X q) :
    R.betti (D.cycleClass q Z) ≠ alpha := by
  intro heq
  apply hmissing
  refine ⟨R.native Z, ?_⟩
  rw [R.cycleClass_natural]
  exact heq

#check construct_target_cycle_from_source_hodge_lift
#check every_target_hodge_class_from_solved_source
#check target_hodge_subset_native_cycleClass_range
#check no_unrepresented_target_from_algebraic_source
#print axioms every_target_hodge_class_from_solved_source
#print axioms no_unrepresented_target_from_algebraic_source

end GSTUniversalChowRetractToTarget
