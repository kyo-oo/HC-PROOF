import GSTFoldRotation
import GSTFoldPolarization
import GSTCausalFoldDefect
import GSTVariableFoldIntegrability
import GSTGraphV2GeneralSpaceRealization
import GSTLawStackRound51
import GSTCMFiniteGeometricDegreeDescent

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
#check GSTLawStackRound51Actual.rides_always_gives_constructively
#check GSTGraphV2GeneralSpaceRealization.forward_pair_defect
#check GSTVariableFoldIntegrability.variableFold_square
#check GSTVariableFoldIntegrability.nijenhuisCoefficient_zero_iff
#check GSTCMFiniteGeometricDegreeDescent.native_rational_cm_cycle_of_geometric_field_expansion
