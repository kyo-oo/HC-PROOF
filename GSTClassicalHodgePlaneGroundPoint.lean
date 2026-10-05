import GSTClassicalHodgeGeometricCycleClassPointRigidity
import GSTClassicalHodgePlaneSemanticIndependence
import GSTClassicalHodgeStrictPlaneCircularityAudit
import GSTClassicalHodgeStrictGraphBettiTrace

/-!
# GST CLASSICAL HODGE — THE PLANE GROUND POINT

This file fixes the endpoint of the GST-plane audit.

There are no more anonymous "plane completeness" assumptions to descend into.
The intrinsic GST plane is already a theorem.  Mechanical strict-graph trace
and injectivity are constructed from geometry.  Ghost-adaptive plane packages
are conclusion-equivalent and therefore barred as premises.

The only semantic datum not determined by the bare Stage-2G record is local and
generatorwise: the supplied cycle-class map must send each genuine
codimension-p point cycle to its geometric Betti point class.  Compact native
cycle normal form then forces the WHOLE cycle-class map.  Conversely equality
with the geometrically generated map forces exactly those point equations.

Thus the semantic ground point is an exact iff, not a new broad axiom.
The zero-cycle-class counterworld proves that bare intrinsic GST plane algebra
cannot imply this semantic identification: it keeps the full unbounded plane
while violating every nonzero geometric point assignment.
-/

set_option maxHeartbeats 180000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgePlaneGroundPoint

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeGeometricCycleClassPointRigidity
open GSTClassicalHodgeStage2GSemanticRigidity
open GSTClassicalHodgePlaneSemanticIndependence
open GSTClassicalHodgeStrictPlaneCircularityAudit
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeCommonClassPlaneRealization
open GSTClassicalHodgeOmniversalGhostPlaneStrike

variable {V : SmoothProjectiveComplexScheme}

/-- **THE EXACT SEMANTIC GROUND POINT.**
No global surjectivity or Hodge conclusion occurs here.  This says only that a
genuine codimension-p point cycle lands on the geometric Betti class assigned
to that same point. -/
def PointSemanticGround
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (pt : PointBettiClass (V := V) p H.analytification) : Prop :=
  ∀ x : CodimensionPoint V.X p,
    H.cycleClass p (codimensionPointCycle V.X p x) = pt x

/-- **GROUND-POINT EXACTNESS.**
The local point law is equivalent to equality of the ENTIRE Stage-2G cycle
class map with the map generated from point geometry.  Hence no further
cycle-class compatibility law can appear later without being redundant. -/
theorem pointSemanticGround_iff_full_geometric_cycleClass
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (pt : PointBettiClass (V := V) p H.analytification) :
    PointSemanticGround H p pt ↔
      H.cycleClass p =
        cycleClassFromPointGeometry (V := V) p H.analytification pt := by
  constructor
  · intro hground
    exact suppliedCycleClass_eq_geometric (V := V) p H pt hground
  · intro hmap x
    rw [hmap]
    exact cycleClassFromPointGeometry_point
      (V := V) p H.analytification pt x

/-- The local ground has a unique global extension.  This is the formal reason
that no second independent semantic bridge can legitimately be introduced
above it. -/
theorem pointSemanticGround_unique_extension
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (pt : PointBettiClass (V := V) p H.analytification)
    (F : codimensionCycles V.X p →ₗ[ℚ]
      RationalSingularCohomology H.analytification (2 * p))
    (hF : ∀ x : CodimensionPoint V.X p,
      F (codimensionPointCycle V.X p x) = pt x) :
    F = cycleClassFromPointGeometry (V := V) p H.analytification pt := by
  apply cycleClass_ext_points (V := V) p
  intro x
  rw [hF x]
  exact (cycleClassFromPointGeometry_point
    (V := V) p H.analytification pt x).symm

/-- Point-ground equality is therefore extensional: any two linear cycle-class
realizations with the same genuine point values are identical everywhere. -/
theorem cycleClass_realizations_unique_from_ground
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (pt : PointBettiClass (V := V) p H.analytification)
    (F G : codimensionCycles V.X p →ₗ[ℚ]
      RationalSingularCohomology H.analytification (2 * p))
    (hF : ∀ x : CodimensionPoint V.X p,
      F (codimensionPointCycle V.X p x) = pt x)
    (hG : ∀ x : CodimensionPoint V.X p,
      G (codimensionPointCycle V.X p x) = pt x) :
    F = G := by
  exact cycleClass_ext_points (V := V) p F G (fun x => (hF x).trans (hG x).symm)

/-- **ZERO-WORLD EXCLUSION AT ONE POINT.**
If even one geometric point class is nonzero, the arbitrary zero-cycle-class
copy of Stage 2G cannot satisfy the semantic ground. -/
theorem zeroCycleClass_violates_nonzero_point_ground
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (pt : PointBettiClass (V := V) p H.analytification)
    (x : CodimensionPoint V.X p)
    (hx : pt x ≠ 0) :
    ¬ PointSemanticGround (zeroCycleClassData H) p pt := by
  intro hground
  have hz := hground x
  have hz' : (0 : RationalSingularCohomology H.analytification (2 * p)) = pt x := by
    simpa [zeroCycleClassData] using hz
  exact hx hz'.symm

/-- **FULL INTRINSIC PLANE DOES NOT SYNTHESIZE SEMANTIC GROUND.**
The same explicit zero-cycle world simultaneously has a live fixed-source GST
plane and violates any nonzero geometric point assignment.  This prevents a
future proof from silently replacing semantic geometry by stronger intrinsic
plane algebra. -/
theorem full_GST_plane_can_coexist_with_ground_failure
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0)
    (pt : PointBettiClass (V := V) p H.analytification)
    (x : CodimensionPoint V.X p)
    (hx : pt x ≠ 0) :
    (Nonempty
      { i : HodgeSupportIndex (zeroCycleClassHodgeState H alpha) //
        hodgeCoordinate i.1 (zeroCycleClassHodgeState H alpha) ≠ 0 })
      ∧ ¬ PointSemanticGround (zeroCycleClassData H) p pt := by
  constructor
  · obtain ⟨i, hi, _hevent, _hreach, _htower, _hL2, _hcollapse⟩ :=
      zeroCycleClass_full_GST_plane H alpha halpha
    exact ⟨⟨i, hi⟩⟩
  · exact zeroCycleClass_violates_nonzero_point_ground H p pt x hx

/-- **NO CONCLUSION-SHAPED PLANE PREMISE.**
The two historical ghost-adaptive plane packages are exactly Hodge itself, so
neither belongs below the ground point. -/
theorem ghostAdaptive_plane_packages_are_not_ground_axioms
    {H : HodgeBigradedBettiData V}
    (G : GeometricCycleClassSpine V H) :
    (GhostAdaptiveStrictPlaneCompleteness G ↔
      BigradedBettiHodgeStatement V H)
      ∧
    (GhostAdaptiveCommonClassPlaneCompleteness G ↔
      BigradedBettiHodgeStatement V H) :=
  all_ghostAdaptive_plane_packages_iff_hodge G

/-- **GROUND-POINT ENDPOINT.**
For a fixed geometric point assignment, the local semantic law, the complete
cycle-class equality, and uniqueness of the global extension are one and the
same mathematical datum.  This is the semantic endpoint below the GST-plane
proof: intrinsic plane algebra is theorem-level; mechanical graph trace is
constructed; ghost-adaptive completeness is circular; and the only semantic
choice left by raw Stage 2G is fixed here generatorwise. -/
theorem plane_ground_point_endpoint
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (pt : PointBettiClass (V := V) p H.analytification) :
    PointSemanticGround H p pt ↔
      H.cycleClass p =
        cycleClassFromPointGeometry (V := V) p H.analytification pt :=
  pointSemanticGround_iff_full_geometric_cycleClass H p pt

#check PointSemanticGround
#check pointSemanticGround_iff_full_geometric_cycleClass
#check pointSemanticGround_unique_extension
#check cycleClass_realizations_unique_from_ground
#check zeroCycleClass_violates_nonzero_point_ground
#check full_GST_plane_can_coexist_with_ground_failure
#check ghostAdaptive_plane_packages_are_not_ground_axioms
#check plane_ground_point_endpoint

#print axioms pointSemanticGround_iff_full_geometric_cycleClass
#print axioms pointSemanticGround_unique_extension
#print axioms zeroCycleClass_violates_nonzero_point_ground
#print axioms full_GST_plane_can_coexist_with_ground_failure
#print axioms ghostAdaptive_plane_packages_are_not_ground_axioms
#print axioms plane_ground_point_endpoint

end GSTClassicalHodgePlaneGroundPoint
