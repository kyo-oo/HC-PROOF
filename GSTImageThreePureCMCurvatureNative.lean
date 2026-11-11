import GSTGraphV2CMWaveFusion
import GSTImageThreeCompanionSourceTransport

/-!
# GST Image 3 — PURE ORIGINAL CM CURVATURE GLOBAL N-WAVE
All U,J,M are the author's ACTUAL original 12-cell physical GST
operators. The only source used here is their derived CM curvature
C = J M - M J, never a freely chosen rank-forcing matrix.

Our new companion N-wave has zero diagonal source coefficients:
every CM-curvature source is transported BETWEEN independent Wave-II
worlds, while each local world's F is source-free U+J. In particular,
the physical local Navigation charge can remain OFF in every world.

The mathematical ALL-finite-r cyclicity proof and rank-r rational
quotient derivation are in companion research/derivations file.
The identity C J = -J C is proved here directly for the original
rational CM complex structure J²=-I, with no new geometry axiom.
-/

set_option maxHeartbeats 5000000
noncomputable section

namespace GSTImageThreePureCMCurvatureNative

open GSTGraphV2CMWaveFusion
open GSTImageThreeCompanionSourceTransport

/-- The TRUE original Wave-I source's CM curvature, not an artificial
independent matrix or a guessed Hodge-cycle operator. -/
def originalCMCurvature (u : WaveSignal) : WaveSignal :=
  J (M u) - M (J u)

theorem originalJ_sub (a b : WaveSignal) :
    J (a - b) = J a - J b := by
  funext s
  simp [J, mul_sub]

theorem originalM_neg (a : WaveSignal) :
    M (-a) = - M a := by
  funext s
  simp [M]

/-- STRONG CM-ODD LAW: the true derived original CM curvature
anti-commutes with the TRUE original complex structure J.
This is an exact identity at every original physical cell. -/
theorem originalCMCurvature_anticommutes (u : WaveSignal) :
    J (originalCMCurvature u) +
      originalCMCurvature (J u) = 0 := by
  simp only [originalCMCurvature, originalJ_sub,
    J_square, originalM_neg]
  abel_nf

/-- The original physical fixed-cell curvature remains nonzero TWO
at the exact original mixed seed, even if local SURVIVE is gated off. -/
theorem originalCMCurvature_seed_fixed :
    originalCMCurvature seed
      ((3 : Fin 4), (2 : Fin 3)) = 2 := by
  simpa only [originalCMCurvature, Pi.sub_apply] using
    wave_source_CM_curvature_nonzero

/-- Entirely original N-cohomology global F: local U+J wave;
the ONLY source is derived original CM curvature exchanged between
independent Wave-II holes by the source matrix C_N. -/
def curvatureGlobalF (N : Nat)
    (source address : Matrix (Fin N) (Fin N) ℚ)
    (v : Fin N → WaveSignal) : Fin N → WaveSignal :=
  fun i =>
    U (v i) + J (v i) +
      (∑ j : Fin N, source i j • originalCMCurvature (v j)) +
      (∑ j : Fin N, address i j • v j)

/-- Exact original rational CM companion construction, no new local
12-cell source. -/
def curvatureCompanionF (N : Nat)
    (coeff : Nat → ℚ)
    (address : Matrix (Fin N) (Fin N) ℚ)
    (v : Fin N → WaveSignal) : Fin N → WaveSignal :=
  curvatureGlobalF N (companionSource N coeff) address v

/-- The source is purely CROSS-WORLD when the original companion has
zero trace, so every local curvature coefficient vanishes EXACTLY. -/
theorem curvatureCompanion_zero_local_source
    (N : Nat) (coeff : Nat → ℚ)
    (htrace : coeff (N-1) = 0) (i : Fin N) :
    companionSource N coeff i i = 0 :=
  companionSource_zero_diagonal N coeff htrace i

#check originalCMCurvature
#check originalCMCurvature_anticommutes
#check originalCMCurvature_seed_fixed
#check curvatureGlobalF
#check curvatureCompanionF
#check curvatureCompanion_zero_local_source
#print axioms originalCMCurvature_anticommutes
#print axioms curvatureCompanion_zero_local_source

end GSTImageThreePureCMCurvatureNative
