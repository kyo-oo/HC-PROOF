import GSTMathboxCMGeometricComplexStructure
import GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra
import GSTCMNumberManipulationTrace

/-!
# GST CM quadratic minimal polynomial forces actual native Hodge geometry

The user's proposed NM+CM mechanism now has a geometric action:
a GENUINE realized finite-closed algebraic correspondence on a
smooth projective complex scheme whose rational Hodge action satisfies
the quadratic imaginary CM polynomial
      T² - 2a T + (a²+b²)I = 0,   b != 0.
The rational polynomial has discriminant -4b² < 0.
Therefore NO nonzero rational Hodge vector can be an eigenvector
with rational eigenvalue. In particular any nonzero native cycle Z
is taken to a rationally independent Hodge direction.

Unlike older GST rank-two statements, the complex-structure J is
NOT independently supplied with a postulated equality to movement:
it is the actual Hodge operator of R, and its movement equals the
algebraic cycle class of R's native finite-closed correspondence.

This produces a rank-2 geometric Hodge realization from one nonzero
actual native source and the exact imaginary-CM polynomial.
A further theorem replaces an assumed nonzero source by a FIXED
CM NM trace measurement at one legal complex index.

The universal existence of such actual CM correspondences on
arbitrary Hodge fibers, and the canonical cup/Gysin period readout,
are still independent geometric construction tasks. CM on H¹ of
abelian varieties does not automatically yield this polynomial on
all rational (p,p) fibers of arbitrary projective varieties.
-/

set_option maxHeartbeats 20000000
noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeLimitlessSpinePropagation
open GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra
open GSTClassicalHodgeRealizedCorrespondenceExpressionAlgebra
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeSingleCorrespondenceRankTwo
open GSTMathboxCMGeometricComplexStructure
open GSTCMNumberManipulationTrace

namespace GSTCMQuadraticNativeRankForcing

variable {W : Type*} [AddCommGroup W] [Module ℚ W]

/-- Imaginary quadratic CM arithmetic eliminates all rational
eigenlines. This is true for arbitrary rational modules, not only
a chosen 2x2 matrix example. -/
theorem imaginary_quadratic_CM_no_rational_eigenline
    (T : Module.End ℚ W)
    (a b : ℚ) (hb : b ≠ 0)
    (hMin : ∀ z : W,
      T (T z) - (2*a) • T z + (a^2+b^2) • z = 0)
    (z : W) (hz : z ≠ 0)
    (c : ℚ) (heigen : T z = c • z) : False := by
  have hh := hMin z
  rw [heigen, map_smul, heigen] at hh
  have hscalar :
      (c*c - (2*a)*c + (a^2+b^2)) • z = 0 := by
    simpa only [sub_smul, add_smul, smul_smul] using hh
  have hc : c*c - (2*a)*c + (a^2+b^2) = 0 :=
    (smul_eq_zero.mp hscalar).resolve_right hz
  have hpoly : (c-a)^2+b^2=0 := by nlinarith [hc]
  have hzero : b=0 := by nlinarith [sq_nonneg (c-a)]
  exact hb hzero

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Actual finite-closed correspondence with imaginary-CM quadratic
action forces independent *native algebraic* Hodge direction.
The J action is the actual R.hodgeOperator, not an abstract matrix
unit with no geometric realization. -/
theorem CM_actual_correspondence_spine_transverse
    (G : GeometricCycleClassSpine V H)
    (hnz : spineHodgeSeed G p ≠ 0)
    (R : RealizedFiniteClosedCorrespondence V H p)
    (hR : R.HodgeCompatible)
    (a b : ℚ) (hb : b ≠ 0)
    (hMin : ∀ z : ClassicalHodgeFiber V H p,
      R.hodgeOperator hR (R.hodgeOperator hR z) -
        (2*a) • R.hodgeOperator hR z +
        (a^2+b^2) • z = 0) :
    ∀ c : ℚ,
      movedSpine G (.atom R) ≠ c • spineHodgeSeed G p := by
  intro c hc
  apply imaginary_quadratic_CM_no_rational_eigenline
    (R.hodgeOperator hR) a b hb hMin
    (spineHodgeSeed G p) hnz c
  calc
    R.hodgeOperator hR (spineHodgeSeed G p) =
      movedSpine G (.atom R) := by
        apply Subtype.ext
        rfl
    _ = c • spineHodgeSeed G p := hc

/-- A genuine imaginary-CM correspondence, not a freely selected
Hodge-fiber matrix, gives actual algebraic representatives of every
rational (p,p) class in a rank-2 fiber. The rank-2 limitation is
mathematical and explicit; this theorem does not substitute for
constructing all higher-dimensional abelian CM tensor cycles. -/
theorem CM_quadratic_forces_native_rank_two_hodge
    (G : GeometricCycleClassSpine V H)
    (hnz : spineHodgeSeed G p ≠ 0)
    (R : RealizedFiniteClosedCorrespondence V H p)
    (hR : R.HodgeCompatible)
    (a b : ℚ) (hb : b ≠ 0)
    (hMin : ∀ z : ClassicalHodgeFiber V H p,
      R.hodgeOperator hR (R.hodgeOperator hR z) -
        (2*a) • R.hodgeOperator hR z +
        (a^2+b^2) • z = 0)
    [FiniteDimensional ℚ (ClassicalHodgeFiber V H p)]
    (hrank : Module.finrank ℚ (ClassicalHodgeFiber V H p) = 2)
    (alpha : RationalSingularCohomology H.analytification (2*p))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p)) :
    ∃ Z : codimensionCycles V.X p, H.cycleClass p Z = alpha := by
  obtain ⟨ell, hread⟩ := exists_nonzero_spine_readout G hnz
  exact every_rank_two_hodge_class_of_nonproportional_geometric_action
    G ell hread (.atom R)
    (CM_actual_correspondence_spine_transverse
      G hnz R hR a b hb hMin) hrank alpha halpha

/-- CM NUMBER MANIPULATION certifies the initial native Hodge
source from a specific Gaussian-index period identity. There is
no independently supplied nonzero native class and no adjustable
zetaAtS coefficient. The existence of a canonical *geometric*
readout matching this CM number is still an explicit prerequisite. -/
theorem CM_NM_complex_readout_forces_nonzero_native_source
    (G : GeometricCycleClassSpine V H)
    (x y : CMQ) (m : ℕ)
    (hreal : (cmIndexedDenominator x y m).1 ≠ 0)
    (read : ClassicalHodgeFiber V H p →ₗ[ℚ] ℚ)
    (hPeriod : read (spineHodgeSeed G p) =
      cmIndexedNMTrace x y m) :
    spineHodgeSeed G p ≠ 0 := by
  have htrace := cmIndexedNMTrace_ne_zero_of_real_ne_zero
    x y m hreal
  intro hz
  have hreadzero : read (spineHodgeSeed G p) = 0 := by
    rw [hz]
    exact map_zero read
  exact htrace (hPeriod.symm.trans hreadzero)

/-! ## Actual scheme-endomorphism graph construction

A CM endomorphism f of a smooth projective complex scheme is genuine
geometry. The existing projective-spine graph naturality theorem
CONSTRUCTS a verified finite-closed correspondence from f. Therefore
a separate arbitrary RealizedFiniteClosedCorrespondence witness is
not necessary: the graph is constructed from f, and its Hodge action
is checked on the actual cycle-class image. -/

/-- Build the *actual* algebraic closed correspondence graph of f,
with its verified native/Betti naturality, rather than selecting
a rational endomorphism matrix unrelated to a projective map. -/
noncomputable def actualCMGraphOfEndomorphism
    (G : GeometricCycleClassSpine V H)
    (f : GSTClassicalHodgeAnalytificationFunctoriality.ComplexSchemeEndomorphism V) :
    RealizedFiniteClosedCorrespondence V H p :=
  RealizedFiniteClosedCorrespondence.graphRealized G f

/-- CM number theory + TRUE endomorphism-graph geometry jointly
force the rank-two Hodge target; no independently chosen
correspondence realization or scalar transversality witness. -/
theorem CM_graph_endomorphism_rank_two_hodge
    (G : GeometricCycleClassSpine V H)
    (hnz : spineHodgeSeed G p ≠ 0)
    (f : GSTClassicalHodgeAnalytificationFunctoriality.ComplexSchemeEndomorphism V)
    (hR : (actualCMGraphOfEndomorphism (p := p) G f).HodgeCompatible)
    (a b : ℚ) (hb : b ≠ 0)
    (hMin : ∀ z : ClassicalHodgeFiber V H p,
      (actualCMGraphOfEndomorphism (p := p) G f).hodgeOperator hR
        ((actualCMGraphOfEndomorphism (p := p) G f).hodgeOperator hR z) -
      (2*a) •
        (actualCMGraphOfEndomorphism (p := p) G f).hodgeOperator hR z +
      (a^2+b^2) • z = 0)
    [FiniteDimensional ℚ (ClassicalHodgeFiber V H p)]
    (hrank : Module.finrank ℚ (ClassicalHodgeFiber V H p) = 2)
    (alpha : RationalSingularCohomology H.analytification (2*p))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p)) :
    ∃ Z : codimensionCycles V.X p, H.cycleClass p Z = alpha := by
  exact CM_quadratic_forces_native_rank_two_hodge
    G hnz (actualCMGraphOfEndomorphism (p := p) G f)
    hR a b hb hMin hrank alpha halpha

/-- The strongest current fixed-period CM+NM bridge:
* the initial nonzero native source is DERIVED from the genuine
  corrected CM number-manipulation trace measurement;
* the algebraic graph correspondence is CONSTRUCTED from the
  actual projective scheme endomorphism f;
* the imaginary quadratic CM polynomial PROVES independence;
* rational rank two finishes the native algebraic Hodge target.

The unproved ingredient is a *canonical* geometric period
comparison hPeriod plus the genuinely induced hMin/Hodge type
of a concrete CM abelian endomorphism. These are separate,
non-circular mathematical existence obligations. -/
theorem CM_NM_period_graph_rank_two_hodge
    (G : GeometricCycleClassSpine V H)
    (x y : CMQ) (m : ℕ)
    (hreal : (cmIndexedDenominator x y m).1 ≠ 0)
    (read : ClassicalHodgeFiber V H p →ₗ[ℚ] ℚ)
    (hPeriod : read (spineHodgeSeed G p) =
      cmIndexedNMTrace x y m)
    (f : GSTClassicalHodgeAnalytificationFunctoriality.ComplexSchemeEndomorphism V)
    (hR : (actualCMGraphOfEndomorphism (p := p) G f).HodgeCompatible)
    (a b : ℚ) (hb : b ≠ 0)
    (hMin : ∀ z : ClassicalHodgeFiber V H p,
      (actualCMGraphOfEndomorphism (p := p) G f).hodgeOperator hR
        ((actualCMGraphOfEndomorphism (p := p) G f).hodgeOperator hR z) -
      (2*a) •
        (actualCMGraphOfEndomorphism (p := p) G f).hodgeOperator hR z +
      (a^2+b^2) • z = 0)
    [FiniteDimensional ℚ (ClassicalHodgeFiber V H p)]
    (hrank : Module.finrank ℚ (ClassicalHodgeFiber V H p) = 2)
    (alpha : RationalSingularCohomology H.analytification (2*p))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p)) :
    ∃ Z : codimensionCycles V.X p, H.cycleClass p Z = alpha := by
  have hnz : spineHodgeSeed G p ≠ 0 :=
    CM_NM_complex_readout_forces_nonzero_native_source
      G x y m hreal read hPeriod
  exact CM_graph_endomorphism_rank_two_hodge
    G hnz f hR a b hb hMin hrank alpha halpha

#check actualCMGraphOfEndomorphism
#check CM_graph_endomorphism_rank_two_hodge
#check CM_NM_period_graph_rank_two_hodge

#print axioms CM_graph_endomorphism_rank_two_hodge
#print axioms CM_NM_period_graph_rank_two_hodge

#check imaginary_quadratic_CM_no_rational_eigenline
#check CM_actual_correspondence_spine_transverse
#check CM_quadratic_forces_native_rank_two_hodge
#check CM_NM_complex_readout_forces_nonzero_native_source

#print axioms imaginary_quadratic_CM_no_rational_eigenline
#print axioms CM_quadratic_forces_native_rank_two_hodge
#print axioms CM_NM_complex_readout_forces_nonzero_native_source

end GSTCMQuadraticNativeRankForcing
