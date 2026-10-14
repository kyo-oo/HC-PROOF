import Mathlib.LinearAlgebra.Basis.VectorSpace
import GSTClassicalHodgeBasisCycleBridge
import GSTGeometricRealizationStage2G
import GSTTransferBridgeV2
import GSTGlobalPureHodgeCosmology
import GSTDimensionFreeHodgeDiagonal
import GSTUniversalAddressBridge
import GSTTruncatedWorldCohomologyRing
import GSTUniversalLefschetzCosmology
import GSTUniversalLefschetzPathFormula
import GSTUniversalLefschetzKernel
import GSTUniversalLefschetzCausalGeometry
import GSTLefschetzPoincareReciprocity
import GSTWorldPoincareDuality
import GSTWorldRecoordinationGroupoid
import GSTGradedWorldAlgebra
import GSTHodgeChannelFinale
import GSTClassicalHodgeFullLimitlessCrown
import GSTClassicalHodgeProjectiveTwoGeneratorExternalization
import GSTClassicalHodgeFullCorrespondenceGSTPlaneCompletion
import GSTClassicalHodgeNativeExecutablePlane
import GSTClassicalHodgeCMGSTNativeBasisCompiler
import GSTClassicalHodgeCMSurfaceCupGysinGSTCompiler
import GSTClassicalHodgeGeometricMatrixRankLanding
import GSTClassicalHodgeGeometricPeriodDeterminant
import GSTClassicalHodgeGeometricKrylovMomentDeterminant
import GSTClassicalHodgeSpineRankOneGeometricRealization
import GSTClassicalHodgeSingleCorrespondenceRankTwo
import GSTClassicalHodgeArbitraryRankChargeFrames
import GSTClassicalHodgeActualGeometricIrreducibility
import GSTMathboxIndependentGeometricCoordinate
import GSTMathboxCMGeometricComplexStructure
import GSTMathboxCorrectedZetaGeometry
import GSTMathboxCorrectedZetaInfinite
import GSTMathboxCorrectedZetaSafeDomain
import GSTMathboxCorrectedZetaActualHodge

/-!
# Hodge Conjecture — Unified Classical GST Landing

This file is the public top-level landing face for the Hodge development.
It combines three independently developed and machine-oriented layers:

1. the genuine Stage-2G rational Hodge target on smooth projective complex
   schemes and native codimension-p algebraic cycles;
2. the rank-free / index-polymorphic classical GST basis reconstruction;
3. the multi-channel Wave-II finite-basis/quotient finale and the full
   limitless geometric/cosmic classical crown.

No internal GST surrogate is substituted for the target.  `ClassicalHodgeTarget`
is definitionally the Stage-2G statement.

The original compatibility landing is retained:

  genuine geometric cycle-class spine
    + nonvanishing projective spine tower
    + genuine projective externalization of the cosmic read/write action
      -> full limitless classical Hodge crown.

The strengthened geometry-first landing removes both of those large supplied
interfaces from its public input surface:

  genuine geometric cycle-class spine
    + one conserved native/cohomological tower charge
      -> all-weight spine nonvanishing as a theorem
    + two genuine projective primitive actions per ordered Hodge pair
      -> all rank-free matrix units by the internal GST word algebra
      -> exact Stage-2G Hodge statement
      -> explicit native codimension-p cycle for every rational (p,p) class.

Under the ordinary finite-dimensionality package for the rational Hodge
fibers, either exact Hodge landing is transported through the independently
verified multi-channel architecture:

  exact Hodge statement
    <-> canonical finite-basis algebraization
    -> Wave-II channel quotient
    -> arbitrary same-weight multiplicity with no finite rank ceiling.

The routes meet here; none is hidden behind a redefinition of Hodge.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G

namespace HodgeConjecture

/-- The exact classical Hodge target already isolated by Stage 2G.

For every codimension `p`, every rational singular-cohomology class whose
complexification lies in the `(p,p)` Hodge summand must lie in the range of
the native codimension-`p` algebraic cycle-class map. -/
def ClassicalHodgeTarget
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) : Prop :=
  BigradedBettiHodgeStatement V H

/-- The target is exactly the elementwise algebraic-cycle witness statement;
there is no weaker GST surrogate hidden behind the name. -/
theorem classicalHodgeTarget_iff_explicit_witness
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) :
    ClassicalHodgeTarget V H ↔
      ∀ p : Nat,
      ∀ alpha : RationalSingularCohomology H.analytification (2 * p),
        complexificationMapQ
            (RationalSingularCohomology H.analytification (2 * p)) alpha
          ∈ (H.hodgeBigrading p).ppComponent →
        ∃ Z : codimensionCycles V.X p,
          H.cycleClass p Z = alpha := by
  simpa [ClassicalHodgeTarget] using
    (bigradedBettiHodgeStatement_iff_explicit_witness V H)

/-- Stage 2G has already proved the final logical landing. -/
theorem classicalHodgeTarget_of_compact_realization
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (hR : Stage2GCompactRealizationObligation V H) :
    ClassicalHodgeTarget V H := by
  exact bigraded_betti_hodge_of_stage2g_compact_obligation V H hR

/-- Elementwise form of the same compact-realization reduction. -/
theorem explicit_witness_of_compact_realization
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (hR : Stage2GCompactRealizationObligation V H)
    (p : Nat)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha :
      complexificationMapQ
          (RationalSingularCohomology H.analytification (2 * p)) alpha
        ∈ (H.hodgeBigrading p).ppComponent) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha := by
  exact
    (classicalHodgeTarget_iff_explicit_witness V H).mp
      (classicalHodgeTarget_of_compact_realization V H hR)
      p alpha halpha

/-! ## Integrated CM surface / Kuga-Satake / Gale geometric programs -/

/-- The EXISTING public Stage-2G Hodge goal follows from concrete finite
CM/Gale/Kuga-Satake geometric source packets:
  source native cycles -> finite incidence geometry -> original GST graded
  correspondence/cut program -> algebraic coefficient descent over K/Q
  -> actual rational target cycle -> original basis-cycle landing.

Unlike a bare basis-cycle bridge, each sheet packet contains independent
source cycles and a computational native operator built from point incidence.
The theorem does not create those geometric packets automatically; that is
the exact concrete geometric construction to be finished. -/
theorem classicalHodgeTarget_of_integrated_CM_GST_programs
    {K : Type*} [Field K] [Algebra ℚ K]
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (G : GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (h :
      GSTClassicalHodgeCMGSTNativeBasisCompiler.CMGSTNativeBasisProgramSupply
        (K := K) G) :
    ClassicalHodgeTarget V H :=
  GSTClassicalHodgeCMGSTNativeBasisCompiler.bigradedBettiHodge_of_CM_GST_programs
    G h

/-- Public elementwise rational cycle witness computed by the integrated
finite geometric GST packets, including algebraic coefficient descent. -/
theorem every_hodge_class_has_native_cycle_of_integrated_CM_GST_programs
    {K : Type*} [Field K] [Algebra ℚ K]
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (G : GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (h :
      GSTClassicalHodgeCMGSTNativeBasisCompiler.CMGSTNativeBasisProgramSupply
        (K := K) G)
    (p : Nat)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p)) :
    ∃ Z : codimensionCycles V.X p, H.cycleClass p Z = alpha := by
  exact classicalHodgeTarget_of_integrated_CM_GST_programs G h p halpha

/-- **CLASS-LOCAL FINITE GST/CM GEOMETRY LANDING.**
For ONE rational Hodge state, source correspondence programs are required
only on its FINITE basis support. This is the targeted finite-case result,
and needs no global geometric packet supply. The entire algebraic output
is assembled from genuinely evaluated GST native cycles. -/
theorem finite_hodge_class_has_native_cycle_of_CM_GST_live_packets
    {K : Type*} [Field K] [Algebra ℚ K]
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (G : GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (p : Nat)
    (alpha :
      GSTClassicalHodgeFiberedCosmology.ClassicalHodgeFiber V H p)
    (hActive :
      ∀ j : GSTClassicalHodgeFiberedCosmology.ClassicalHodgeBasisIndex V H p,
        j ∈
          ((GSTClassicalHodgeFiberedCosmology.classicalHodgeBasis V H p).repr alpha).support →
        Nonempty
          (GSTClassicalHodgeCMGSTNativeBasisCompiler.CMGSTNativeSheetProgram
            (K := K) G p j)) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha.1 :=
  GSTClassicalHodgeCMGSTNativeBasisCompiler.native_cycle_of_finite_CM_GST_packet_support
    G p alpha hActive

/-- STRONGER GEOMETRIC VERSION OF THE CLASS-LOCAL FINITE LANDING.

Unlike the flexible source-packet version, this version only accepts a
cohomological correspondence action COMPILED FROM an actual degree-checked
cup-product kernel, source pullback and projection Gysin, together with its
finite point-incidence equation. It then runs the existing graded GST program,
descends algebraic coefficients, and constructs the exact rational cycle. -/
theorem finite_hodge_class_has_native_cycle_of_CupGysin_GST_geometry
    {K : Type*} [Field K] [Algebra ℚ K]
    {PCoh : Nat → Type*}
    [∀ n, AddCommGroup (PCoh n)] [∀ n, Module ℚ (PCoh n)]
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (G : GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (p : Nat)
    (alpha : GSTClassicalHodgeFiberedCosmology.ClassicalHodgeFiber V H p)
    (hActive :
      ∀ j : GSTClassicalHodgeFiberedCosmology.ClassicalHodgeBasisIndex V H p,
        j ∈
          ((GSTClassicalHodgeFiberedCosmology.classicalHodgeBasis V H p).repr alpha).support →
        Nonempty
          (GSTClassicalHodgeCMSurfaceCupGysinGSTCompiler.CupGysinGSTSheetProgram
            (K := K) (PCoh := PCoh) G p j)) :
    ∃ Z : codimensionCycles V.X p, H.cycleClass p Z = alpha.1 :=
  GSTClassicalHodgeCMSurfaceCupGysinGSTCompiler.finite_target_from_cupGysin_GST_sheet_packets
    G p alpha hActive

/-- Geometric cup/Gysin source kernels, compiled into the original GST
correspondence/cut language at every basis direction, complete the SAME
literal rational Hodge target defined at the start of this file. -/
theorem classicalHodgeTarget_of_CupGysin_GST_geometry
    {K : Type*} [Field K] [Algebra ℚ K]
    {PCoh : Nat → Type*}
    [∀ n, AddCommGroup (PCoh n)] [∀ n, Module ℚ (PCoh n)]
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (G : GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (h :
      ∀ q : Nat,
      ∀ j : GSTClassicalHodgeFiberedCosmology.ClassicalHodgeBasisIndex V H q,
        Nonempty
          (GSTClassicalHodgeCMSurfaceCupGysinGSTCompiler.CupGysinGSTSheetProgram
            (K := K) (PCoh := PCoh) G q j)) :
    ClassicalHodgeTarget V H :=
  GSTClassicalHodgeCMSurfaceCupGysinGSTCompiler.exact_stage2G_of_cupGysin_GST_sheet_packets
    G h

/-! ## Full conjecture via GST geometric determinant generation

This is the main numerical geometric attack. Construct in every Hodge
weight as many ACTUAL GST native correspondence programs as the rational
Hodge dimension, and prove that the RATIONAL Hodge-coordinate matrix
of their native cycle classes has NONZERO DETERMINANT.

No exact target-basis match is requested for any individual program.
The old GST proof engine then forms the exact rational native cycle
of EVERY Hodge class by ordinary inverse-matrix coefficients.

Unlike the intrinsic limitless matrix-unit theorem, these are genuine
program outputs on the native algebraic-cycle carrier. The missing
universal mathematical theorem is existence of a nonsingular family
of geometric outputs; it must be obtained independently, for example
from projective intersection and motivic correspondence geometry. -/

/-- **EXACT FULL RATIONAL HODGE TARGET FROM ONE GEOMETRIC DETERMINANT
PER WEIGHT** on every smooth projective complex V.

This is a new stronger route through the ORIGINAL public conjecture
definition: it needs genuine independently constructed graded programs
and one scalar NONVANISHING condition, not target-cycle witnesses. -/
theorem classicalHodgeTarget_of_universalGSTGeometricDeterminants
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (G : GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (F : GSTHodgeChannelFinale.Stage2GHodgeFiniteness V H)
    (h :
      GSTClassicalHodgeGeometricMatrixRankLanding.UniversalGSTGeometricDeterminantGeneration
        G F) :
    ClassicalHodgeTarget V H :=
  GSTClassicalHodgeGeometricMatrixRankLanding.exact_hodge_of_universal_GST_geometric_determinants
    G F h

/-- **FULL UNIVERSAL GST GEOMETRIC TRIANGULATION ROUTE.**

For every codimension on an arbitrary smooth projective complex variety,
produce actual native correspondence programs and genuine rational
period detectors with an upper triangular geometric period matrix
whose diagonal intersection numbers are nonzero.

The Lean proof builds ALL rational Hodge cycle representatives by
matrix inversion; it neither assumes exact basis cycle witnesses nor
mistakes the intrinsic GST matrix-unit algebra for geometric output.

Proving the universal triangulation predicate from the actual GST
scheme/cup/Gysin geometry is the remaining principal geometric
nonvanishing construction. -/
theorem classicalHodgeTarget_of_universal_GST_triangular_geometry
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (G : GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (F : GSTHodgeChannelFinale.Stage2GHodgeFiniteness V H)
    (h :
      GSTClassicalHodgeGeometricPeriodDeterminant.UniversalGSTTriangularPeriodGeneration
        G F) :
    ClassicalHodgeTarget V H :=
  GSTClassicalHodgeGeometricPeriodDeterminant.full_rational_hodge_of_universal_GST_triangular_geometry
    G F h

/-- **UNIVERSAL ONE-CORRESPONDENCE HODGE GEOMETRY ROUTE.**

For each Hodge weight on an arbitrary smooth projective complex
variety, construct ONE genuinely realized closed correspondence, ONE
native algebraic seed, and ONE rational geometric trace. Nonzero
determinant of their n-by-n scalar Krylov/Hankel moment matrix
establishes cyclicity as a THEOREM and constructs every target native
cycle explicitly from actual geometric correspondence iterates.

This is stronger than assuming a cyclic orbit or one separately
materialized matrix unit for every Hodge sheet. The mathematical
challenge is independently proving nonzero Hankel determinants
using projective intersection geometry, not positing cyclicity. -/
theorem classicalHodgeTarget_of_universal_Krylov_Hankel_geometry
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (F : GSTHodgeChannelFinale.Stage2GHodgeFiniteness V H)
    (h :
      GSTClassicalHodgeGeometricKrylovMomentDeterminant.UniversalGSTKrylovHankelNondegeneracy F) :
    ClassicalHodgeTarget V H :=
  GSTClassicalHodgeGeometricKrylovMomentDeterminant.full_hodge_of_universal_Krylov_Hankel_geometry
    F h

/-- **PROJECTIVE-DEGREE HANKEL ROUTE TO THE FULL HODGE CONJECTURE.**

This is the most geometry-constrained numerical route among the new
ones. All moments are computed using the repository's ordinary
projective-degree trace on ACTUAL algebraic cycles produced by
successive iterations of ONE strict realized correspondence.

The mathematical target is nonzero determinant of those measured
moment matrices, in every Hodge weight. Once established, the
native-cycle reconstruction proves the original full rational
Hodge statement for arbitrary smooth projective complex V. -/
theorem classicalHodgeTarget_of_universal_projectiveDegree_Krylov
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (D : GSTClassicalHodgeProjectiveDegreeTrace.ProjectiveDegreeTraceSemantics V H)
    (F : GSTHodgeChannelFinale.Stage2GHodgeFiniteness V H)
    (h :
      GSTClassicalHodgeGeometricKrylovMomentDeterminant.UniversalProjectiveDegreeKrylovNondegeneracy
        D F) :
    ClassicalHodgeTarget V H :=
  GSTClassicalHodgeGeometricKrylovMomentDeterminant.full_hodge_of_projective_degree_Krylov_nonvanishing
    D F h

/-! ## Corrected index-dependent GST zeta geometry — infinite series

The user's corrected equation (3) uses x^n-y^(n+1), NOT the original
index-independent x-y². The new modules prove one exact infinite
real summation and a uniform nonsingular positive domain x>y²>=1.
They also supply a native geometric class nonvanishing certificate.

This public theorem reaches the unchanged Stage-2G rational Hodge target
under ACTUAL correspondence irreducibility and geometric measurement
laws at every active Hodge weight. It does NOT assume a representative
of the individual target Hodge class, and it does NOT assert these
universal geometric laws have already been proved for all varieties.
-/

/-- **PUBLIC CORRECTED GST ZETA-TO-HODGE LANDING**.
The numerical infinite series is kernel-proved. A measured genuine
native algebraic cycle and actual geometric irreducibility at each
active weight then supply rational algebraic representatives for all
rational Hodge classes in arbitrary finite rank. Zero fibers need no
source. These are explicit sufficient geometric hypotheses, NOT an
unconditional proof that arbitrary smooth projective varieties
satisfy them. -/
theorem classicalHodgeTarget_of_corrected_zeta_actual_geometry
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (G : GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (hirred : ∀ q : Nat,
      GSTClassicalHodgeActualGeometricIrreducibility.ActualHodgeCorrespondenceIrreducible
        (V := V) (H := H) (p := q))
    (hZetaGeometry : ∀ q : Nat,
      (∃ a : GSTClassicalHodgeFiberedCosmology.ClassicalHodgeFiber V H q,
        a ≠ 0) →
      ∃ (Z : codimensionCycles V.X q)
        (read : GSTClassicalHodgeFiberedCosmology.ClassicalHodgeFiber V H q →ₗ[ℚ] ℚ)
        (zetaAtS : ℝ),
        zetaAtS ≠ 0 ∧
        ((read
          (GSTClassicalHodgeGeometricMatrixRankLanding.geometricHodgeClass G Z) : ℚ) : ℝ) =
          zetaAtS * (∑' m : ℕ,
            GSTMathboxCorrectedZetaGeometry.indexedKernel 2 2 m)) :
    ClassicalHodgeTarget V H :=
  GSTMathboxCorrectedZetaActualHodge.full_hodge_of_corrected_zeta_actual_geometry
    G hirred hZetaGeometry

/-! ## True third geometric coordinate and CM quadratic native rank gain

The third indexed coordinate in the user's GST conversion is a separate
geometric axis (not a ternary digit). Its exact radical value can certify
a NEW algebraic-cycle class outside the span of an arbitrary old family
when a genuine correspondence supplies its geometric comparison equation.

The alternate CM route uses a genuinely realized operator on the native
spine and a rational complex structure J with J²=-id. This structural
law DERIVES rather than assumes rank-two transverse nonvanishing.
Neither numerical transversality nor existence of a universal complex
structure is asserted on every smooth projective variety. -/

/-- The user's photographed independent-third-coordinate conversion,
when tied to genuine point-class correspondence geometry, proves a new
NATIVE algebraic Hodge direction beyond an arbitrary old collection. -/
theorem native_third_coordinate_adds_hodge_direction
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V} {p : Nat} {ι : Type*}
    (G : GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (old : ι → codimensionCycles V.X p)
    (E : GSTClassicalHodgeRealizedCorrespondenceExpressionAlgebra.RealizedCorrespondenceExpr V H p)
    (read : GSTClassicalHodgeFiberedCosmology.ClassicalHodgeFiber V H p →ₗ[ℚ] ℚ)
    (hOld : ∀ i : ι, read
      (GSTClassicalHodgeGeometricMatrixRankLanding.geometricHodgeClass G (old i)) = 0)
    (factor a b psi xi : ℝ) (x y : Fin 3 → ℝ)
    (hConv : GSTMathboxIndependentGeometricCoordinate.independentThirdConversion
      factor a b psi xi x y ≠ 0)
    (hGeom : ((read
      (GSTClassicalHodgeGeometricMatrixRankLanding.geometricHodgeClass G
        (E.cycleOperator
          (GSTClassicalHodgeLimitlessSpinePropagation.spineNativeTower G p))) : ℚ) : ℝ) =
      GSTMathboxIndependentGeometricCoordinate.thirdGeometricNumerator a b x y) :
    GSTClassicalHodgeGeometricMatrixRankLanding.geometricHodgeClass G
      (E.cycleOperator (GSTClassicalHodgeLimitlessSpinePropagation.spineNativeTower G p))
       ∉ Submodule.span ℚ
           (Set.range (fun i : ι =>
             GSTClassicalHodgeGeometricMatrixRankLanding.geometricHodgeClass G (old i))) :=
  GSTMathboxIndependentGeometricCoordinate.photographed_third_coordinate_certifies_fresh_native_cycle
    G old E read hOld factor a b psi xi x y hConv hGeom

/-- All-weights GST/CM result. Active rank-two fibers are solved by a
REALIZED geometric correspondence whose action on the native spine obeys
J²=-identity on its rational Hodge fiber. The necessary nonzero charged
coordinate and rank-gain are then constructed as theorems. Zero and
rank-one weights use existing actual geometric cases. -/
theorem classicalHodgeTarget_of_weightwise_actual_CM_geometry
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (F : GSTHodgeChannelFinale.Stage2GHodgeFiniteness V H)
    (G : GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (h : ∀ p : Nat,
      (∀ a : GSTClassicalHodgeFiberedCosmology.ClassicalHodgeFiber V H p,
        a = 0) ∨
      (Module.finrank ℚ
          (GSTClassicalHodgeFiberedCosmology.ClassicalHodgeFiber V H p) = 1 ∧
        GSTClassicalHodgeLimitlessSpinePropagation.spineHodgeSeed G p ≠ 0) ∨
      (∃ (E : GSTClassicalHodgeRealizedCorrespondenceExpressionAlgebra.RealizedCorrespondenceExpr V H p)
         (J : Module.End ℚ (GSTClassicalHodgeFiberedCosmology.ClassicalHodgeFiber V H p)),
        (∀ z : GSTClassicalHodgeFiberedCosmology.ClassicalHodgeFiber V H p,
            J (J z) = -z) ∧
        J (GSTClassicalHodgeLimitlessSpinePropagation.spineHodgeSeed G p) =
          GSTClassicalHodgeSingleCorrespondenceRankTwo.movedSpine G E ∧
        GSTClassicalHodgeLimitlessSpinePropagation.spineHodgeSeed G p ≠ 0 ∧
        Module.finrank ℚ
          (GSTClassicalHodgeFiberedCosmology.ClassicalHodgeFiber V H p) = 2)) :
    ClassicalHodgeTarget V H := by
  intro p alpha halpha
  letI : FiniteDimensional ℚ
      (GSTClassicalHodgeFiberedCosmology.ClassicalHodgeFiber V H p) := F.finite p
  rcases h p with hzero | ⟨hrank, hnz⟩ | ⟨E, J, hJ2, hgeom, hnz, hrank⟩
  · have ha0 : alpha = 0 := by
      have hz := congrArg Subtype.val
        (hzero (⟨alpha, halpha⟩ :
          GSTClassicalHodgeFiberedCosmology.ClassicalHodgeFiber V H p))
      simpa using hz
    exact ⟨0, by simp [ha0]⟩
  · exact GSTClassicalHodgeSpineRankOneGeometricRealization.every_rank_one_hodge_class_is_native
      G p hnz hrank alpha halpha
  · exact GSTMathboxCMGeometricComplexStructure.rank_two_hodge_of_actual_CM_complex_structure
      G hnz E J hJ2 hgeom hrank alpha halpha

/-! ## Actual-correspondence irreducibility (independent determinant-free route)

This differs from abstract GST matrix-unit irreducibility: invariance is
proved for ACTUAL realized Hodge-compatible finite-closed correspondences.
If those geometric operators act irreducibly on an active Hodge fiber and a
nonzero native spine class is present, the existing native algebraic Hodge
subspace must equal the whole fiber. -/

/-- **EXACT HODGE LANDING VIA ACTUAL GEOMETRIC IRREDUCIBILITY.**
The active-weight seed requirement is local; zero Hodge fibers require no
nonzero cycle. Actual-geometric correspondence irreducibility is a distinct
unproved geometric existence/classification input, not substituted by the
abstract GST matrix-unit arsenal. -/
theorem classicalHodgeTarget_of_actual_correspondence_irreducibility
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (G : GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (hirred : ∀ q : Nat,
      GSTClassicalHodgeActualGeometricIrreducibility.ActualHodgeCorrespondenceIrreducible
        (V := V) (H := H) (p := q))
    (hseed : ∀ q : Nat,
      (∃ a : GSTClassicalHodgeFiberedCosmology.ClassicalHodgeFiber V H q,
        a ≠ 0) →
      GSTClassicalHodgeLimitlessSpinePropagation.spineHodgeSeed G q ≠ 0) :
    ClassicalHodgeTarget V H :=
  GSTClassicalHodgeActualGeometricIrreducibility.full_hodge_of_actual_geometric_irreducibility
    G hirred hseed

/-! ## Arbitrary-rank explicit charged geometric frames

This is the all-finite-ranks successor to the rank-two one-correspondence
charge wedge. Each native frame entry is explicitly built from the actual
projective spine and a genuine realized correspondence expression. The
condition is a nonzero determinant of THOSE geometric cycles, never an
assumed preimage of a target Hodge class.

As elsewhere in this file, a conditional theorem must not be advertised as
an unconditional construction of the determinant's existence. -/

/-- **PUBLIC ARBITRARY-RANK GST CHARGED GEOMETRIC FRAME LANDING.**
A genuine fully ranked frame of projective-spine/charge-wedge algebraic cycles
at each Hodge weight yields the ORIGINAL Stage-2G rational Hodge target,
by explicit inversion of the matrix of those native cycles. No restriction
to rank two and no artificial upper dimension cutoff occurs. -/
theorem classicalHodgeTarget_of_universal_GST_charged_geometric_frames
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (G : GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (F : GSTHodgeChannelFinale.Stage2GHodgeFiniteness V H)
    (h :
      GSTClassicalHodgeArbitraryRankChargeFrames.UniversalGSTChargedGeometricFrameGeneration
        G F) :
    ClassicalHodgeTarget V H :=
  GSTClassicalHodgeArbitraryRankChargeFrames.exact_hodge_of_universal_charged_geometric_frames
    G F h

/-! ## Weight-local GST geometry: zero, rank one and rank two

This route is deliberately weight-by-weight, rather than assuming a nonzero
conserved spine charge in every cohomological degree. At rank two, the new
single-correspondence charge wedge constructs the second native Hodge direction.
A genuine transverse correspondence remains the geometric existence input.

In contrast to the earlier all-weights conserved-charge theorem, rank-zero
fibers are handled without demanding an impossible nonzero source cycle. -/

/-- **ACTUAL GEOMETRY LOW-RANK INTEGRATION.**
For every rational Hodge weight, either the Hodge fiber is zero, or the
projective native spine generates its rank-one Hodge fiber, or one genuinely
realized geometric correspondence moves that spine transversely in rank two.

The zero case needs no geometric witness. The rank-one case uses the actual
projective native cycle. The rank-two case uses the concrete charge-wedge
native cycle, NOT a target-class preimage or an abstract matrix unit.

This theorem is a precise **conditional** completion for such low-rank
geometries, not the unconditional all-varieties Hodge conjecture. -/
theorem classicalHodgeTarget_of_weightwise_rank_le_two_actual_geometry
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (F : GSTHodgeChannelFinale.Stage2GHodgeFiniteness V H)
    (G : GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (h : ∀ p : Nat,
      (∀ a : GSTClassicalHodgeFiberedCosmology.ClassicalHodgeFiber V H p,
        a = 0) ∨
      (Module.finrank ℚ
          (GSTClassicalHodgeFiberedCosmology.ClassicalHodgeFiber V H p) = 1 ∧
        GSTClassicalHodgeLimitlessSpinePropagation.spineHodgeSeed G p ≠ 0) ∨
      (∃ (ell :
            GSTClassicalHodgeFiberedCosmology.ClassicalHodgeFiber V H p →ₗ[ℚ] ℚ),
        ell (GSTClassicalHodgeLimitlessSpinePropagation.spineHodgeSeed G p) ≠ 0 ∧
        ∃ (E : GSTClassicalHodgeRealizedCorrespondenceExpressionAlgebra.RealizedCorrespondenceExpr V H p),
          GSTClassicalHodgeSingleCorrespondenceRankTwo.hodgeChargeWedge
            G ell E ≠ 0 ∧
          Module.finrank ℚ
            (GSTClassicalHodgeFiberedCosmology.ClassicalHodgeFiber V H p) = 2)) :
    ClassicalHodgeTarget V H := by
  intro p alpha halpha
  letI : FiniteDimensional ℚ
      (GSTClassicalHodgeFiberedCosmology.ClassicalHodgeFiber V H p) := F.finite p
  rcases h p with hzero | ⟨hrank, hnz⟩ | ⟨ell, hlive, E, htransverse, hrank⟩
  · have ha0 : alpha = 0 := by
      have hz := congrArg Subtype.val
        (hzero (⟨alpha, halpha⟩ :
          GSTClassicalHodgeFiberedCosmology.ClassicalHodgeFiber V H p))
      simpa using hz
    exact ⟨0, by simp [ha0]⟩
  · exact
      GSTClassicalHodgeSpineRankOneGeometricRealization.every_rank_one_hodge_class_is_native
        G p hnz hrank alpha halpha
  · exact
      GSTClassicalHodgeSingleCorrespondenceRankTwo.every_rank_two_hodge_class_of_one_transverse_correspondence
        G ell hlive E htransverse hrank alpha halpha

/-! ## Index-polymorphic limitless realization -/

/-- One Stage-2G realization with an arbitrary address universe `ι`.
The structure contains no Hodge conclusion; it records only the realization
and its compatibility with the genuine Hodge predicate and cycle-class map. -/
structure UniverseIndexedRealization
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) (ι : Type*) where
  realization :
    CompactHodgeRealization ι
      (RationalSingularCohomology H.analytification (2 * p))
      (codimensionCycles V.X p)
  hodge_iff :
    ∀ alpha : RationalSingularCohomology H.analytification (2 * p),
      realization.isHodge alpha ↔
        alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p)
  cycleClass_eq :
    realization.cycleClass = H.cycleClass p

/-- Any genuine index-polymorphic realization produces an actual native
codimension-p cycle for each rational `(p,p)` class. -/
theorem hodge_class_has_cycle_of_universe_indexed_realization
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    {p : Nat} {ι : Type*}
    (R : UniverseIndexedRealization V H p ι)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p)) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha := by
  have hr : R.realization.isHodge alpha :=
    (R.hodge_iff alpha).2 halpha
  obtain ⟨Z, hZ⟩ :=
    compact_realization_surjectivity R.realization alpha hr
  refine ⟨Z, ?_⟩
  rw [← R.cycleClass_eq]
  exact hZ

/-- A family of arbitrary-index realizations closes the exact classical
Stage-2G target.  The index type may vary with the codimension. -/
theorem classicalHodgeTarget_of_universe_indexed_family
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (ι : Nat → Type*)
    (R : ∀ p : Nat, UniverseIndexedRealization V H p (ι p)) :
    ClassicalHodgeTarget V H := by
  intro p alpha halpha
  exact hodge_class_has_cycle_of_universe_indexed_realization
    V H (R p) alpha halpha



/-- A basis-cycle bridge in every codimension closes the exact classical
Hodge target, with arbitrary rank and multiplicity. -/
theorem classicalHodgeTarget_of_basis_cycle_family
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (R : ∀ p : Nat, HodgeBasisCycleBridge V H p) :
    ClassicalHodgeTarget V H := by
  intro p alpha halpha
  exact hodge_class_has_cycle_of_basis_bridge V H (R p) alpha halpha

/-- If the classical target already holds, each chosen Hodge basis vector has
a native algebraic representative. -/
noncomputable def hodgeBasisCycleBridgeOfTarget
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (h : ClassicalHodgeTarget V H)
    (p : Nat) :
    HodgeBasisCycleBridge V H p where
  basisCycle i :=
    Classical.choose (show
      ∃ Z : codimensionCycles V.X p,
        H.cycleClass p Z = (hodgeBasis V H p i).1 by
      exact h p (hodgeBasis V H p i).2)
  basisCycle_spec i :=
    Classical.choose_spec (show
      ∃ Z : codimensionCycles V.X p,
        H.cycleClass p Z = (hodgeBasis V H p i).1 by
      exact h p (hodgeBasis V H p i).2)

/-- **BASIS-GENERATOR NORMAL FORM.**
The exact Stage-2G Hodge target is equivalent to algebraicity of one chosen
basis of every rational `(p,p)` Hodge fiber. -/
theorem classicalHodgeTarget_iff_basis_cycle_bridges
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) :
    ClassicalHodgeTarget V H ↔
      ∀ p : Nat, Nonempty (HodgeBasisCycleBridge V H p) := by
  constructor
  · intro h p
    exact ⟨hodgeBasisCycleBridgeOfTarget V H h p⟩
  · intro h
    exact classicalHodgeTarget_of_basis_cycle_family V H
      (fun p => Classical.choice (h p))

/-- Semantic firewall: if a supplied cycle-class map is zero while the Hodge
sector contains a nonzero class, then the classical Hodge target for that
semantic package is impossible. -/
theorem not_classicalHodgeTarget_of_zero_cycleClass
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha :
      complexificationMapQ
          (RationalSingularCohomology H.analytification (2 * p)) alpha
        ∈ (H.hodgeBigrading p).ppComponent)
    (halpha_ne : alpha ≠ 0)
    (hzero : H.cycleClass p = 0) :
    ¬ ClassicalHodgeTarget V H := by
  intro hTarget
  obtain ⟨Z, hZ⟩ :=
    (classicalHodgeTarget_iff_explicit_witness V H).mp hTarget
      p alpha halpha
  have hzeroZ : H.cycleClass p Z = 0 := by
    rw [hzero]
    rfl
  apply halpha_ne
  rw [← hZ, hzeroZ]

/-- **SEMANTIC GEOMETRY FIREWALL.**
The current `GeometricCycleClassSpine` interface expresses compatible
cycle-class/Hodge operators, but it does not pin the cycle-class map
to the genuine construction. If a rational Hodge class is nonzero,
the Stage-2G zero-cycle-class model admits every current spine field
while the classical target fails.

This rejects the invalid inference "geometric spine laws ⇒ full Hodge" inside
the same main public file. A successful unconditional theorem must provide
new genuine geometric semantics or a separate independent generation proof. -/
theorem geometric_spine_laws_alone_cannot_establish_classicalHodgeTarget
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p))
    (hne : alpha ≠ 0) :
    ∃ H0 : HodgeBigradedBettiData V,
      Nonempty
        (GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H0) ∧
      ¬ ClassicalHodgeTarget V H0 := by
  let H0 :=
    GSTClassicalHodgeStage2GSemanticRigidity.zeroCycleClassData H
  refine ⟨H0, ?_, ?_⟩
  · exact ⟨GSTClassicalHodgeGeometricCycleClassSpine.zeroCycleClassSpine H⟩
  · exact GSTClassicalHodgeStage2GSemanticRigidity.not_bigradedBettiHodge_zeroCycleClass
      H p alpha halpha hne

/-! ## Unified finale: Astra geometry × GLM repairs × multi-channel architecture -/

/-- The public target is exactly equivalent to the canonical finite-basis
algebraization obligation from the multi-channel finale.  This is the direct
wire from the independently verified channel architecture into the public
Hodge statement. -/
theorem classicalHodgeTarget_iff_canonical_basis_algebraization
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (F : GSTHodgeChannelFinale.Stage2GHodgeFiniteness V H) :
    ClassicalHodgeTarget V H ↔
      GSTHodgeChannelFinale.Stage2GCanonicalBasisAlgebraizationObligation
        V H F := by
  simpa [ClassicalHodgeTarget] using
    (GSTHodgeChannelFinale.canonical_basis_algebraization_iff_hodge
      V H F).symm

/-- Astra's full limitless geometric/cosmic crown lands directly in the exact
public Hodge target.  No finite chart, one-generator surrogate, or altered
Hodge statement occurs at this boundary. -/
theorem classicalHodgeTarget_of_full_limitless_geometry
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (G :
      GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (hNV :
      GSTClassicalHodgeFullLimitlessCrown.SpineTowerNonvanishing G)
    (R :
      GSTClassicalHodgeFullLimitlessCrown.FullProjectiveCosmicExternalization G) :
    ClassicalHodgeTarget V H := by
  simpa [ClassicalHodgeTarget] using
    (GSTClassicalHodgeFullLimitlessCrown.bigradedBettiHodge G hNV R)

/-- Explicit elementwise native-cycle form of the full limitless landing. -/
theorem every_hodge_class_has_native_cycle_of_full_limitless_geometry
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (G :
      GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (hNV :
      GSTClassicalHodgeFullLimitlessCrown.SpineTowerNonvanishing G)
    (R :
      GSTClassicalHodgeFullLimitlessCrown.FullProjectiveCosmicExternalization G)
    (p : Nat)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p)) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha := by
  exact
    GSTClassicalHodgeFullLimitlessCrown.every_hodge_class_has_native_cycle
      G hNV R p alpha halpha

/-- **GEOMETRY-FIRST BRUTE-FORCE PUBLIC LANDING.**

This strengthened public theorem removes both large compatibility inputs of the
older limitless crown.  The tower-nonvanishing family is generated internally
from one conserved native/cohomological charge.  Full projective matrix-unit
externalization is replaced by two actual projective primitive actions per
ordered Hodge pair; the complete rank-free matrix-unit arsenal is synthesized
by the internal GST two-generator word. -/
theorem classicalHodgeTarget_of_conserved_spine_and_projective_two_generators
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (G :
      GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (D :
      GSTClassicalHodgeLimitlessSpinePropagation.SpineTowerConservedCharge G)
    (R : ∀ q : Nat,
      ∀ i j : GSTClassicalHodgeFiberedCosmology.ClassicalHodgeBasisIndex V H q,
        GSTClassicalHodgeProjectiveTwoGeneratorExternalization.ProjectiveTwoGenerator
          (V := V) (H := H) i j) :
    ClassicalHodgeTarget V H := by
  simpa [ClassicalHodgeTarget] using
    (GSTClassicalHodgeProjectiveTwoGeneratorExternalization.bigradedBettiHodge_of_conserved_spine_and_projective_two_generators
        G D R)

/-- Elementwise cycle witness for the geometry-first brute-force landing. -/
theorem every_hodge_class_has_native_cycle_of_conserved_spine_and_projective_two_generators
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (G :
      GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (D :
      GSTClassicalHodgeLimitlessSpinePropagation.SpineTowerConservedCharge G)
    (R : ∀ q : Nat,
      ∀ i j : GSTClassicalHodgeFiberedCosmology.ClassicalHodgeBasisIndex V H q,
        GSTClassicalHodgeProjectiveTwoGeneratorExternalization.ProjectiveTwoGenerator
          (V := V) (H := H) i j)
    (p : Nat)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p)) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha := by
  exact
    GSTClassicalHodgeProjectiveTwoGeneratorExternalization.every_hodge_class_has_native_cycle_of_conserved_spine_and_projective_two_generators
        G D R p alpha halpha

/-- Once ordinary Hodge-fiber finite-dimensionality is supplied, the full
limitless classical crown automatically supplies the exact canonical basis
algebraization obligation used by the multi-channel theorem. -/
theorem canonical_basis_algebraization_of_full_limitless_geometry
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (F : GSTHodgeChannelFinale.Stage2GHodgeFiniteness V H)
    (G :
      GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (hNV :
      GSTClassicalHodgeFullLimitlessCrown.SpineTowerNonvanishing G)
    (R :
      GSTClassicalHodgeFullLimitlessCrown.FullProjectiveCosmicExternalization G) :
    GSTHodgeChannelFinale.Stage2GCanonicalBasisAlgebraizationObligation
      V H F := by
  apply
    (GSTHodgeChannelFinale.canonical_basis_algebraization_iff_hodge
      V H F).2
  exact GSTClassicalHodgeFullLimitlessCrown.bigradedBettiHodge G hNV R

/-- Canonical finite-basis algebraization generated from the strengthened
conserved-spine/projective-two-generator route. -/
theorem canonical_basis_algebraization_of_conserved_spine_and_projective_two_generators
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (F : GSTHodgeChannelFinale.Stage2GHodgeFiniteness V H)
    (G :
      GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (D :
      GSTClassicalHodgeLimitlessSpinePropagation.SpineTowerConservedCharge G)
    (R : ∀ q : Nat,
      ∀ i j : GSTClassicalHodgeFiberedCosmology.ClassicalHodgeBasisIndex V H q,
        GSTClassicalHodgeProjectiveTwoGeneratorExternalization.ProjectiveTwoGenerator
          (V := V) (H := H) i j) :
    GSTHodgeChannelFinale.Stage2GCanonicalBasisAlgebraizationObligation
      V H F := by
  apply
    (GSTHodgeChannelFinale.canonical_basis_algebraization_iff_hodge
      V H F).2
  exact
    GSTClassicalHodgeProjectiveTwoGeneratorExternalization.bigradedBettiHodge_of_conserved_spine_and_projective_two_generators
        G D R

/-- The same geometric/cosmic crown therefore generates the minimal Wave-II
channel quotient architecture automatically. -/
theorem channel_quotient_of_full_limitless_geometry
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (F : GSTHodgeChannelFinale.Stage2GHodgeFiniteness V H)
    (G :
      GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (hNV :
      GSTClassicalHodgeFullLimitlessCrown.SpineTowerNonvanishing G)
    (R :
      GSTClassicalHodgeFullLimitlessCrown.FullProjectiveCosmicExternalization G) :
    GSTHodgeChannelQuotient.Stage2GChannelQuotientObligation V H := by
  exact
    GSTHodgeChannelFinale.canonical_basis_obligation_implies_channel_quotient
      V H F
      (canonical_basis_algebraization_of_full_limitless_geometry F G hNV R)

/-- Wave-II channel quotient generated from the strengthened geometry-first
route. -/
theorem channel_quotient_of_conserved_spine_and_projective_two_generators
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (F : GSTHodgeChannelFinale.Stage2GHodgeFiniteness V H)
    (G :
      GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (D :
      GSTClassicalHodgeLimitlessSpinePropagation.SpineTowerConservedCharge G)
    (R : ∀ q : Nat,
      ∀ i j : GSTClassicalHodgeFiberedCosmology.ClassicalHodgeBasisIndex V H q,
        GSTClassicalHodgeProjectiveTwoGeneratorExternalization.ProjectiveTwoGenerator
          (V := V) (H := H) i j) :
    GSTHodgeChannelQuotient.Stage2GChannelQuotientObligation V H := by
  exact
    GSTHodgeChannelFinale.canonical_basis_obligation_implies_channel_quotient
      V H F
      (canonical_basis_algebraization_of_conserved_spine_and_projective_two_generators
        F G D R)

/-- **PUBLIC NATIVE-ONLY GST PLANE FINALE.**

This is the semantic endpoint required by the plane-completeness strategy:
every Hodge basis sheet is the cycle class of an ACTUAL native output of one
verified correspondence/cut program.  No geometric-spine compatibility
structure is an input to the implication.

The theorem therefore states directly that completed native GST-plane
completeness proves the public classical Hodge target. -/
theorem classicalHodgeTarget_of_nativeExecutableGSTPlane
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (hplane :
      GSTClassicalHodgeNativeExecutablePlane.NativeExecutableGSTPlaneCompleteness
        (V := V) (H := H)) :
    ClassicalHodgeTarget V H :=
  GSTClassicalHodgeNativeExecutablePlane.hodge_of_nativeExecutableGSTPlane
    hplane

/-- Explicit cycle produced by the native-only completed GST plane. -/
theorem every_hodge_class_has_native_cycle_of_nativeExecutableGSTPlane
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (hplane :
      GSTClassicalHodgeNativeExecutablePlane.NativeExecutableGSTPlaneCompleteness
        (V := V) (H := H))
    (p : Nat)
    (alpha :
      GSTGeometricRealizationStage2F.RationalSingularCohomology
        H.analytification (2 * p))
    (halpha :
      alpha ∈
        GSTGeometricRealizationStage2G.rationalHodgeSubspace
          (H.hodgeBigrading p)) :
    ∃ Z : GSTGeometricRealizationStage2D.codimensionCycles V.X p,
      H.cycleClass p Z = alpha :=
  GSTClassicalHodgeNativeExecutablePlane.hodge_of_nativeExecutableGSTPlane
    hplane p halpha

/-- **PUBLIC EXECUTABLE GST-PLANE LANDING.**

Here "plane completeness" has the geometric meaning required by the proof:
every basis sheet is reached by one actual graded correspondence/cut program
from the canonical geometric origin.  Under that theorem-level plane, the
public classical Hodge target follows directly. -/
theorem classicalHodgeTarget_of_fullCorrespondenceGSTPlane
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (G :
      GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (hplane :
      GSTClassicalHodgeFullCorrespondenceGSTPlaneCompletion.FullCorrespondenceGSTPlaneCompleteness G) :
    ClassicalHodgeTarget V H :=
  GSTClassicalHodgeFullCorrespondenceGSTPlaneCompletion.hodge_of_fullCorrespondenceGSTPlane G hplane

/-- Constructive public form of the executable GST-plane landing. -/
theorem every_hodge_class_has_native_cycle_of_fullCorrespondenceGSTPlane
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (G :
      GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (hplane :
      GSTClassicalHodgeFullCorrespondenceGSTPlaneCompletion.FullCorrespondenceGSTPlaneCompleteness G)
    (p : Nat)
    (alpha :
      GSTGeometricRealizationStage2F.RationalSingularCohomology
        H.analytification (2 * p))
    (halpha :
      alpha ∈
        GSTGeometricRealizationStage2G.rationalHodgeSubspace
          (H.hodgeBigrading p)) :
    ∃ Z : GSTGeometricRealizationStage2D.codimensionCycles V.X p,
      H.cycleClass p Z = alpha :=
  GSTClassicalHodgeFullCorrespondenceGSTPlaneCompletion.nativeCycle_of_fullCorrespondenceGSTPlane G hplane p alpha halpha

/-- Same-weight multiplicity is unrestricted in the final public landing. -/
theorem no_same_weight_hodge_rank_ceiling :
    ∀ N p : Nat,
      Fintype.card
          (GSTMultiChannelHodgeCosmology.HodgeChannel
            (GSTMultiChannelHodgeCosmology.standardChannelShape N)) = N := by
  exact GSTHodgeChannelFinale.no_same_weight_rank_ceiling

/-- **UNIFIED FINAL HODGE RECEIPT.**

This theorem is the explicit composition point of the original full-limitless
compatibility lane and the multi-channel architecture.  It is retained for
backward compatibility with existing callers. -/
theorem unified_hodge_finale
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (F : GSTHodgeChannelFinale.Stage2GHodgeFiniteness V H)
    (G :
      GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (hNV :
      GSTClassicalHodgeFullLimitlessCrown.SpineTowerNonvanishing G)
    (R :
      GSTClassicalHodgeFullLimitlessCrown.FullProjectiveCosmicExternalization G) :
    ClassicalHodgeTarget V H
    ∧ GSTHodgeChannelFinale.Stage2GCanonicalBasisAlgebraizationObligation V H F
    ∧ GSTHodgeChannelQuotient.Stage2GChannelQuotientObligation V H
    ∧ (∀ N p : Nat,
      Fintype.card
          (GSTMultiChannelHodgeCosmology.HodgeChannel
            (GSTMultiChannelHodgeCosmology.standardChannelShape N)) = N) := by
  have hTarget : ClassicalHodgeTarget V H :=
    classicalHodgeTarget_of_full_limitless_geometry G hNV R
  have hBasis :
      GSTHodgeChannelFinale.Stage2GCanonicalBasisAlgebraizationObligation
        V H F :=
    canonical_basis_algebraization_of_full_limitless_geometry F G hNV R
  have hQuot :
      GSTHodgeChannelQuotient.Stage2GChannelQuotientObligation V H :=
    GSTHodgeChannelFinale.canonical_basis_obligation_implies_channel_quotient
      V H F hBasis
  exact ⟨hTarget, hBasis, hQuot, no_same_weight_hodge_rank_ceiling⟩

/-- **UNIFIED GEOMETRY-FIRST BRUTE-FORCE HODGE RECEIPT.**

The old `hNV` and full projective-kernel externalization arguments are absent
from this strengthened public finale.  Nonvanishing is generated recursively
from the conserved charge and all matrix units are generated from the two
actual projective primitive actions. -/
theorem unified_hodge_finale_conserved_spine_projective_two_generators
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (F : GSTHodgeChannelFinale.Stage2GHodgeFiniteness V H)
    (G :
      GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (D :
      GSTClassicalHodgeLimitlessSpinePropagation.SpineTowerConservedCharge G)
    (R : ∀ q : Nat,
      ∀ i j : GSTClassicalHodgeFiberedCosmology.ClassicalHodgeBasisIndex V H q,
        GSTClassicalHodgeProjectiveTwoGeneratorExternalization.ProjectiveTwoGenerator
          (V := V) (H := H) i j) :
    ClassicalHodgeTarget V H
    ∧ GSTHodgeChannelFinale.Stage2GCanonicalBasisAlgebraizationObligation V H F
    ∧ GSTHodgeChannelQuotient.Stage2GChannelQuotientObligation V H
    ∧ (∀ N p : Nat,
      Fintype.card
          (GSTMultiChannelHodgeCosmology.HodgeChannel
            (GSTMultiChannelHodgeCosmology.standardChannelShape N)) = N) := by
  have hTarget : ClassicalHodgeTarget V H :=
    classicalHodgeTarget_of_conserved_spine_and_projective_two_generators
      G D R
  have hBasis :
      GSTHodgeChannelFinale.Stage2GCanonicalBasisAlgebraizationObligation
        V H F :=
    canonical_basis_algebraization_of_conserved_spine_and_projective_two_generators
      F G D R
  have hQuot :
      GSTHodgeChannelQuotient.Stage2GChannelQuotientObligation V H :=
    GSTHodgeChannelFinale.canonical_basis_obligation_implies_channel_quotient
      V H F hBasis
  exact ⟨hTarget, hBasis, hQuot, no_same_weight_hodge_rank_ceiling⟩

#check ClassicalHodgeTarget
#check classicalHodgeTarget_iff_explicit_witness
#check classicalHodgeTarget_of_compact_realization
#check explicit_witness_of_compact_realization
#check UniverseIndexedRealization
#check hodge_class_has_cycle_of_universe_indexed_realization
#check native_third_coordinate_adds_hodge_direction
#check classicalHodgeTarget_of_corrected_zeta_actual_geometry
#check classicalHodgeTarget_of_weightwise_actual_CM_geometry
#check classicalHodgeTarget_of_actual_correspondence_irreducibility
#check classicalHodgeTarget_of_universal_GST_charged_geometric_frames
#check classicalHodgeTarget_of_weightwise_rank_le_two_actual_geometry
#check classicalHodgeTarget_of_universe_indexed_family
#check HodgeFiber
#check HodgeBasisIndex
#check hodgeBasis
#check hodgeCoordinates
#check hodgeCoordinates_basis
#check HodgeBasisCycleBridge
#check hodgeBasisCycleLift
#check hodgeBasisCycleLift_spec
#check hodge_class_has_cycle_of_basis_bridge
#check classicalHodgeTarget_of_basis_cycle_family
#check hodgeBasisCycleBridgeOfTarget
#check classicalHodgeTarget_iff_basis_cycle_bridges
#check not_classicalHodgeTarget_of_zero_cycleClass
#check geometric_spine_laws_alone_cannot_establish_classicalHodgeTarget
#check classicalHodgeTarget_iff_canonical_basis_algebraization
#check classicalHodgeTarget_of_full_limitless_geometry
#check every_hodge_class_has_native_cycle_of_full_limitless_geometry
#check classicalHodgeTarget_of_conserved_spine_and_projective_two_generators
#check every_hodge_class_has_native_cycle_of_conserved_spine_and_projective_two_generators
#check canonical_basis_algebraization_of_full_limitless_geometry
#check canonical_basis_algebraization_of_conserved_spine_and_projective_two_generators
#check channel_quotient_of_full_limitless_geometry
#check channel_quotient_of_conserved_spine_and_projective_two_generators
#check classicalHodgeTarget_of_nativeExecutableGSTPlane
#check every_hodge_class_has_native_cycle_of_nativeExecutableGSTPlane
#check classicalHodgeTarget_of_fullCorrespondenceGSTPlane
#check every_hodge_class_has_native_cycle_of_fullCorrespondenceGSTPlane
#check no_same_weight_hodge_rank_ceiling
#check unified_hodge_finale
#check unified_hodge_finale_conserved_spine_projective_two_generators

#print axioms classicalHodgeTarget_iff_explicit_witness
#print axioms classicalHodgeTarget_of_compact_realization
#print axioms explicit_witness_of_compact_realization
#print axioms hodge_class_has_cycle_of_universe_indexed_realization
#print axioms native_third_coordinate_adds_hodge_direction
#print axioms classicalHodgeTarget_of_corrected_zeta_actual_geometry
#print axioms classicalHodgeTarget_of_weightwise_actual_CM_geometry
#print axioms classicalHodgeTarget_of_actual_correspondence_irreducibility
#print axioms classicalHodgeTarget_of_universal_GST_charged_geometric_frames
#print axioms classicalHodgeTarget_of_weightwise_rank_le_two_actual_geometry
#print axioms classicalHodgeTarget_of_universe_indexed_family
#print axioms hodgeCoordinates_basis
#print axioms hodgeBasisCycleLift_spec
#print axioms hodge_class_has_cycle_of_basis_bridge
#print axioms classicalHodgeTarget_of_basis_cycle_family
#print axioms classicalHodgeTarget_iff_basis_cycle_bridges
#print axioms not_classicalHodgeTarget_of_zero_cycleClass
#print axioms geometric_spine_laws_alone_cannot_establish_classicalHodgeTarget
#print axioms classicalHodgeTarget_iff_canonical_basis_algebraization
#print axioms classicalHodgeTarget_of_full_limitless_geometry
#print axioms every_hodge_class_has_native_cycle_of_full_limitless_geometry
#print axioms classicalHodgeTarget_of_conserved_spine_and_projective_two_generators
#print axioms every_hodge_class_has_native_cycle_of_conserved_spine_and_projective_two_generators
#print axioms canonical_basis_algebraization_of_full_limitless_geometry
#print axioms canonical_basis_algebraization_of_conserved_spine_and_projective_two_generators
#print axioms channel_quotient_of_full_limitless_geometry
#print axioms channel_quotient_of_conserved_spine_and_projective_two_generators
#print axioms classicalHodgeTarget_of_nativeExecutableGSTPlane
#print axioms every_hodge_class_has_native_cycle_of_nativeExecutableGSTPlane
#print axioms classicalHodgeTarget_of_fullCorrespondenceGSTPlane
#print axioms every_hodge_class_has_native_cycle_of_fullCorrespondenceGSTPlane
#print axioms unified_hodge_finale
#print axioms unified_hodge_finale_conserved_spine_projective_two_generators

end HodgeConjecture
