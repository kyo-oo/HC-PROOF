import GSTFoldRotation
import GSTFoldPolarization
import GSTCausalFoldDefect
import GSTVariableFoldIntegrability
import GSTGraphV2GeneralSpaceRealization
import GSTLawStackRound51
import GSTCMFiniteGeometricDegreeDescent
import GSTSpectralBoundaryDefect
import GSTFoldPeriodDescent
import GSTCausalPairingGraphs
import GSTGraphV2UnboundedHigherCausality
import GSTGradedWorldAlgebra
import waves.GSTNCohomologyV3

/-!
GST spatial-fold continuation, 2026-11-02. Algebraic proof drafts, with the
constant-torus, divisor, and integrability geometry in the companion LaTeX.
The native CM coefficient-descent theorem below remains scheme-conditional;
its geometric input is not silently manufactured for an arbitrary original X.
-/

#check GSTFoldRotation.doubled_door_witness
#check GSTFoldRotation.integral_door_iff
#check GSTFoldPolarization.polarization_positive
#check GSTCausalFoldDefect.word_defect_exact
#check GSTCausalFoldDefect.endpoint_break_has_bad_edge
#check GSTCausalFoldDefect.nativeCycleTower_class
#check GSTCausalFoldDefect.nativeCycleCombination_class
#check GSTCausalFoldDefect.rational_range_saturated
#check GSTLawStackRound51Actual.rides_always_gives_constructively
#check GSTLawStackRound51Actual.rides_branching_constructively
#check GSTLawStackRound51Actual.labeled_rulings_reconstruct
#check GSTLawStackRound51Actual.rational_control_break_survives_scale
#check GSTSpectralBoundaryDefect.cyclic_cubic_orientation_numerator
#check GSTSpectralBoundaryDefect.orientation_square_zero
#check GSTGraphV2GeneralSpaceRealization.forward_pair_defect
#check GSTVariableFoldIntegrability.variableFold_square
#check GSTVariableFoldIntegrability.nijenhuisCoefficient_zero_iff
#check GSTCMFiniteGeometricDegreeDescent.native_rational_cm_cycle_of_geometric_field_expansion
#check GSTFoldPeriodDescent.affine_period_coefficients
#check GSTFoldPeriodDescent.fixed_balanced_period
#check GSTFoldPeriodDescent.three_charge_kernels
#check GSTCausalPairingGraphs.graph_special_linear_invariant
#check GSTCausalPairingGraphs.normalize_handle_return

-- Actual custom-module central-fold continuation; uncompiled drafts.
#check GSTGraphV2UnboundedHigherCausality.CentralCausalFold.cocycle_coherence
#check GSTGraphV2UnboundedHigherCausality.CentralCausalFold.centralMul_assoc
#check GSTGraphV2GeneralSpaceRealization.causalWordSpace
#check GSTGraphV2GeneralSpaceRealization.restored_endpoint_can_have_broken_prefix
#check GSTCausalFoldDefect.pure_split_iff_missing_mode_zero
#check GSTNCohomologyV3.all_channels_closed_iff_zero_curvature
#check GSTGradedWorldAlgebra.centralFold_opposedness_defect

namespace GSTSpatialFoldResearch
open GSTNCohomology GSTNCohomologyV3

/-- Instantiates the split law on the actual N-channel curvature matrix. -/
theorem central_N_channels_pure_split_iff (s t : NShape)
    (K : Fin s.holes → Fin t.holes → ℚ) (u v : Fin s.holes → ℂ)
    (hu : complexCurvatureLinear s t K u=0) :
    (∃ a b : Fin s.holes → ℂ,
      complexCurvatureLinear s t K a=0 ∧ complexCurvatureLinear s t K b=0 ∧
      u=a+b ∧ v=Complex.I • (a-b)) ↔ complexCurvatureLinear s t K v=0 := by
  exact GSTCausalFoldDefect.pure_split_iff_missing_mode_zero
    (complexCurvatureLinear s t K) u v hu

#print axioms central_N_channels_pure_split_iff
end GSTSpatialFoldResearch
