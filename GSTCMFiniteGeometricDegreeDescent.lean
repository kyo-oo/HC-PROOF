import GSTClassicalHodgeCrossCarrierGeometricTransfer
import GSTClassicalHodgeExactClayStatement

/-!
# GST CM universal transfer: generically finite geometric descent

This is a legitimate non-circular source-to-target descent mechanism
for arbitrary target smooth projective complex varieties PROVIDED that
a genuine generically finite geometric morphism from a source
with algebraic rational Hodge classes is actually constructed.

A finite dominant morphism f : A -> X of degree d != 0 yields
  f_* f^* = d * identity
on rational cohomology, with both operators induced by actual
algebraic graphs. If every rational Hodge class on A is algebraic,
then every Hodge class on X is algebraic:
  alpha -> f^* alpha -> source algebraic cycle C
        -> d^{-1} f_* C -> target algebraic cycle of class alpha.

The code below types the geometric pullback on true Betti
cohomology, its Hodge-type compatibility, an actual cross-carrier
algebraic pushforward, and the geometric degree identity.
No Hodge target preimage or full-rank matrix is an input.

DO NOT MISREAD: this theorem does not manufacture f : A -> X for
an arbitrary X. That extra universal geometric dominance theorem
would be a major new claim; for fixed powers of E_i it is FALSE
that every projective variety admits such a generically finite
cover (there are projective varieties not dominated by abelian
varieties). This theorem gives a true geometric transfer route
without claiming a nonexistent universal CM dominance.
-/

set_option maxHeartbeats 20000000
noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeCrossCarrierGeometricTransfer

namespace GSTCMFiniteGeometricDegreeDescent

variable {A X : SmoothProjectiveComplexScheme}
variable {HA : HodgeBigradedBettiData A}
variable {HX : HodgeBigradedBettiData X}

/-- One degree-split genuine cycle correspondence transports the
rational Hodge statement from a verified source to its target.
This does NOT use a target-class algebraic preimage as a hypothesis. -/
theorem hodge_at_weight_of_geometric_degree_split
    (p : Nat)
    (R : CrossCarrierTransfer A X HA HX p p)
    (pull : RationalSingularCohomology HX.analytification (2*p) →ₗ[ℚ]
      RationalSingularCohomology HA.analytification (2*p))
    (hPull : ∀ alpha : RationalSingularCohomology HX.analytification (2*p),
      alpha ∈ rationalHodgeSubspace (HX.hodgeBigrading p) →
      pull alpha ∈ rationalHodgeSubspace (HA.hodgeBigrading p))
    (d : ℚ) (hd : d ≠ 0)
    (hDegree : ∀ alpha : RationalSingularCohomology HX.analytification (2*p),
      R.betti (pull alpha) = d • alpha)
    (hSource : BigradedBettiHodgeStatement A HA)
    (alpha : RationalSingularCohomology HX.analytification (2*p))
    (ha : alpha ∈ rationalHodgeSubspace (HX.hodgeBigrading p)) :
    ∃ C : codimensionCycles X.X p, HX.cycleClass p C = alpha := by
  obtain ⟨C,hC⟩ := hSource p (pull alpha) (hPull alpha ha)
  refine ⟨d⁻¹ • R.native C, ?_⟩
  calc
    HX.cycleClass p (d⁻¹ • R.native C) =
        d⁻¹ • HX.cycleClass p (R.native C) := by rw [map_smul]
    _ = d⁻¹ • R.betti (HA.cycleClass p C) := by rw [R.naturality]
    _ = d⁻¹ • R.betti (pull alpha) := by rw [hC]
    _ = d⁻¹ • (d • alpha) := by rw [hDegree]
    _ = alpha := by simp [smul_smul, hd]

/-- Every-weight version of the genuine finite-degree CM-source
transfer. A finite dominant algebraic morphism supplies the
geometric pullback/pushforward/naturality/degree data, not a free
Hodge-basis realization. -/
theorem full_hodge_of_geometrically_degree_split_CM_source
    (R : ∀ p : Nat, CrossCarrierTransfer A X HA HX p p)
    (pull : ∀ p : Nat,
      RationalSingularCohomology HX.analytification (2*p) →ₗ[ℚ]
        RationalSingularCohomology HA.analytification (2*p))
    (hPull : ∀ p : Nat,
      ∀ alpha : RationalSingularCohomology HX.analytification (2*p),
        alpha ∈ rationalHodgeSubspace (HX.hodgeBigrading p) →
        pull p alpha ∈ rationalHodgeSubspace (HA.hodgeBigrading p))
    (d : ℚ) (hd : d ≠ 0)
    (hDegree : ∀ p : Nat,
      ∀ alpha : RationalSingularCohomology HX.analytification (2*p),
        (R p).betti (pull p alpha) = d • alpha)
    (hSource : BigradedBettiHodgeStatement A HA) :
    BigradedBettiHodgeStatement X HX := by
  intro p alpha ha
  exact hodge_at_weight_of_geometric_degree_split
    p (R p) (pull p) (hPull p) d hd (hDegree p)
    hSource alpha ha

#check hodge_at_weight_of_geometric_degree_split
#check full_hodge_of_geometrically_degree_split_CM_source

#print axioms hodge_at_weight_of_geometric_degree_split
#print axioms full_hodge_of_geometrically_degree_split_CM_source

end GSTCMFiniteGeometricDegreeDescent
