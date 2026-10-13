import Mathlib

/-!
# Surface-period push/pull extraction: the independent linear-algebra core

Formalization of the *valid formal implication* used in
OpenAI's 2026-09-30 CM Hodge preprint, build/sections/03-surface.tex,
Equation 'surface-to-tensor':

  p'_* (p^* Z ∪ K) = k t_beta,    k ≠ 0.

If the left-hand side is the Betti image of a genuine algebraic
correspondence applied to a genuine algebraic source cycle, rational
normalization constructs the exact target cycle.

The linear-algebra lemma below does not construct the geometric
correspondence or prove its cup/Gysin formula. Those are the remaining
independent geometric tasks in HC-PROOF. No Hodge hypothesis, target
cycle representative, or custom axiom is assumed.
-/

noncomputable section
namespace GSTClassicalHodgeSurfacePeriodCycleTransfer

variable {C H : Type*}
variable [AddCommGroup C] [Module ℚ C]
variable [AddCommGroup H] [Module ℚ H]

/-- Explicit extraction of a target native cycle from an actual geometric
correspondence and nonzero Betti-period identity. This gives a CONCRETE
witness, rather than postulating algebraicity of the target. -/
noncomputable def extractedCycle
    (native : Module.End ℚ C) (Z : C) (k : ℚ) : C :=
  k⁻¹ • native Z

theorem extractedCycle_spec
    (cl : C →ₗ[ℚ] H)
    (native : Module.End ℚ C)
    (betti : Module.End ℚ H)
    (hincidence : ∀ Z : C, cl (native Z) = betti (cl Z))
    (Z : C) (beta : H) (k : ℚ)
    (hk : k ≠ 0)
    (hperiod : betti (cl Z) = k • beta) :
    cl (extractedCycle native Z k) = beta := by
  unfold extractedCycle
  calc
    cl (k⁻¹ • native Z) = k⁻¹ • cl (native Z) := map_smul cl _ _
    _ = k⁻¹ • betti (cl Z) := by rw [hincidence Z]
    _ = k⁻¹ • (k • beta) := by rw [hperiod]
    _ = beta := by simp [smul_smul, hk]

theorem exists_native_cycle_of_geometric_period
    (cl : C →ₗ[ℚ] H)
    (native : Module.End ℚ C)
    (betti : Module.End ℚ H)
    (hincidence : ∀ Z : C, cl (native Z) = betti (cl Z))
    (Z : C) (beta : H) (k : ℚ)
    (hk : k ≠ 0)
    (hperiod : betti (cl Z) = k • beta) :
    ∃ Y : C, cl Y = beta :=
  ⟨extractedCycle native Z k,
    extractedCycle_spec cl native betti hincidence Z beta k hk hperiod⟩

/-- Composition of two separately geometrically realized correspondences
preserves the exact native/Betti cycle-class square. The composed native
word is an actual composition of native operators, not an arbitrary
cohomological matrix unit. -/
theorem composed_geometric_incidence
    (cl : C →ₗ[ℚ] H)
    (native1 native2 : Module.End ℚ C)
    (betti1 betti2 : Module.End ℚ H)
    (h1 : ∀ Z : C, cl (native1 Z) = betti1 (cl Z))
    (h2 : ∀ Z : C, cl (native2 Z) = betti2 (cl Z)) :
    ∀ Z : C,
      cl ((native2.comp native1) Z) =
        (betti2.comp betti1) (cl Z) := by
  intro Z
  simp only [LinearMap.comp_apply]
  rw [h2, h1]

/-- Finite geometric source paths can be composed first and only then
normalized by the nonzero period. Both native steps are required to
commute with the actual cycle-class map. -/
theorem exists_native_cycle_of_two_step_geometric_period
    (cl : C →ₗ[ℚ] H)
    (native1 native2 : Module.End ℚ C)
    (betti1 betti2 : Module.End ℚ H)
    (h1 : ∀ Z : C, cl (native1 Z) = betti1 (cl Z))
    (h2 : ∀ Z : C, cl (native2 Z) = betti2 (cl Z))
    (Z : C) (beta : H) (k : ℚ)
    (hk : k ≠ 0)
    (hperiod : (betti2.comp betti1) (cl Z) = k • beta) :
    ∃ Y : C, cl Y = beta := by
  exact exists_native_cycle_of_geometric_period cl
    (native2.comp native1) (betti2.comp betti1)
    (composed_geometric_incidence cl native1 native2 betti1 betti2 h1 h2)
    Z beta k hk hperiod

end GSTClassicalHodgeSurfacePeriodCycleTransfer
