import GSTBlowupSchemeNativeBridge
import GSTBlowupThreeCycleIntersectionRank

/-!
# GST primitive intersection-rank landing in actual Stage-2G Hodge geometry

This closes the formal type gap between a generic algebraic Gram inverse and
the repository's native rational codimension-two cycles on actual smooth
projective complex schemes. The target is the ACTUAL Stage-2G Hodge fiber in
the rational singular cohomology of a supplied analytification.

No target algebraicity, target class preimage, or arbitrary full-rank matrix
is assumed. Instead, three genuine native algebraic cycles are supplied,
their exact geometric intersection readings must be established from
projective bundle/Gysin intersection geometry, and the readouts must
separate the target Hodge fiber. The last fact follows independently from
b4=3 plus Poincare duality for Bl_C(P4), which remains to be connected
to the current Mathlib scheme Betti implementation.
-/

set_option maxHeartbeats 10000000
noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTBlowupThreeCycleIntersectionRank
open GSTBlowupSchemeNativeBridge

namespace GSTBlowupRankActualHodgeLanding

theorem real_scheme_three_intersection_cycles_cover_middle_hodge
    {Y : SmoothProjectiveComplexScheme}
    {HY : HodgeBigradedBettiData Y}
    (G : AlgebraicCycleHodgeSemantics Y HY 2)
    (Z0 Z1 Z2 : codimensionCycles Y.X 2)
    (ell0 ell1 ell2 : ClassicalHodgeFiber Y HY 2 →ₗ[ℚ] ℚ)
    (normalDegree : ℚ)
    (h00 : ell0 (G.toHodge Z0) = 1)
    (h01 : ell0 (G.toHodge Z1) = 0)
    (h02 : ell0 (G.toHodge Z2) = 0)
    (h10 : ell1 (G.toHodge Z0) = 0)
    (h11 : ell1 (G.toHodge Z1) = 0)
    (h12 : ell1 (G.toHodge Z2) = -1)
    (h20 : ell2 (G.toHodge Z0) = 0)
    (h21 : ell2 (G.toHodge Z1) = -1)
    (h22 : ell2 (G.toHodge Z2) = -normalDegree)
    (hsep : Function.Injective
      (fun x : ClassicalHodgeFiber Y HY 2 => (ell0 x, ell1 x, ell2 x)))
    (alpha : ClassicalHodgeFiber Y HY 2) :
    ∃ Z : codimensionCycles Y.X 2, HY.cycleClass 2 Z = alpha.1 := by
  let cl := G.toHodge
  let Z := nativeCycleFromIntersection cl ell0 ell1 ell2
    Z0 Z1 Z2 normalDegree alpha
  have hExact : cl Z = alpha := by
    exact three_native_cycles_represent_every_hodge_class cl
      ell0 ell1 ell2 Z0 Z1 Z2 normalDegree
      h00 h01 h02 h10 h11 h12 h20 h21 h22 hsep alpha
  exact ⟨Z, congrArg Subtype.val hExact⟩

#check real_scheme_three_intersection_cycles_cover_middle_hodge
#print axioms real_scheme_three_intersection_cycles_cover_middle_hodge

end GSTBlowupRankActualHodgeLanding
