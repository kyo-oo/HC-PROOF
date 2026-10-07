import Mathlib

/-!
# GST CLASSICAL HODGE — REPAIR TOOLKIT

Distilled from the SB repair waves (SB-98 … SB-109): the lemma shapes that
recurred in every broken round of the classical Hodge lane.

* the nonzero-scalar endomorphism normalization (the two-slot Lefschetz
  firing pattern `c⁻¹ • (c • F) = F`), which raw `simp` leaves as the
  `c⁻¹ * c` residual on the pointwise form;
* the pointwise smul/comp transport shapes that `rw` misses on
  `Module.End` but `exact` closes by default-transparency defeq.

These lemmas are universe-polymorphic in the carrier and require only the
ℚ-module structure, so every classical-Hodge file can import this toolkit
without pulling any scheme-level data.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 500000

namespace GSTClassicalHodgeRepairToolkit

variable {M : Type*} [AddCommGroup M] [Module ℚ M]

/-- **THE TWO-SLOT NORMALIZATION LAW.**
A nonzero scalar prefactor cancels on endomorphism words:
`c⁻¹ • (c • F) = F`.  This is the exact shape of the bare-Lefschetz
matrix-unit equation, and closes the residual that `simp` leaves behind
(`(c⁻¹ * c) • x` on the elementwise form). -/
theorem inv_smul_smul_End {c : ℚ} (hc : c ≠ 0) (F : M →ₗ[ℚ] M) :
    c⁻¹ • (c • F) = F := by
  rw [smul_smul, inv_mul_cancel₀ hc, one_smul]

/-- Mirror direction of the normalization law:
`c • (c⁻¹ • F) = F` for nonzero `c`. -/
theorem smul_inv_smul_End {c : ℚ} (hc : c ≠ 0) (F : M →ₗ[ℚ] M) :
    c • (c⁻¹ • F) = F := by
  rw [smul_smul, mul_inv_cancel₀ hc, one_smul]

/-- **POINTWISE SMUL TRANSPORT.**  `(c • F) x = c • (F x)` by reflexivity —
the application-level bridge that raw `rw [LinearMap.smul_apply]` misses
when the coercion head is hidden behind a `Module.End` abbreviation. -/
theorem smul_End_apply (c : ℚ) (F : M →ₗ[ℚ] M) (x : M) :
    (c • F) x = c • (F x) :=
  rfl

/-- **COMP-SMUL WORD TRANSPORT.**  Scaling the middle of a composed word
equals scaling the composite — the shape the arsenal-word reductions need
when the smul sits between two applications. -/
theorem smul_comp_middle (c : ℚ) (F G : M →ₗ[ℚ] M) :
    (c • F).comp G = c • (F.comp G) := by
  ext x
  simp [smul_End_apply]

/-- **DOUBLE-SMUL COMPOSE.**  `(c • F).comp (c • G)` on a module where the
scalar already lives — the geometry-first word re-association shape. -/
theorem smul_comp_smul (c : ℚ) (F G : M →ₗ[ℚ] M) :
    ((c • F).comp (c • G)) = (c * c) • (F.comp G) := by
  ext x
  simp [smul_End_apply, smul_smul]

end GSTClassicalHodgeRepairToolkit

#check GSTClassicalHodgeRepairToolkit.inv_smul_smul_End
#check GSTClassicalHodgeRepairToolkit.smul_inv_smul_End
#check GSTClassicalHodgeRepairToolkit.smul_End_apply
#check GSTClassicalHodgeRepairToolkit.smul_comp_middle
#check GSTClassicalHodgeRepairToolkit.smul_comp_smul
