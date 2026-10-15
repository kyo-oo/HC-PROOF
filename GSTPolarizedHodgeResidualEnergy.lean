import GSTUniversalHodgeResidualProjection

/-!
# GST polarized primitive Hodge residual — exact Pythagorean identity

The Hodge–Riemann bilinear relations supply a rational polarization Q
with positive-definite signed primitive (p,p) intersection pairing
on an arbitrary smooth projective complex variety X.

For a finite genuine native algebraic primitive basis z_i with
a rational Gram-dual detector ell_i(x)=Q(x,cl(z_i)),
our universal native projection Z_alpha gives exact orthogonality:
  Q(r_alpha, cl(Z_alpha)) = 0.

Consequently:
  Q(alpha,alpha)=Q(cl(Z_alpha),cl(Z_alpha))+Q(r_alpha,r_alpha).

In the TRUE positive-definite primitive Hodge fiber, a hypothetical
missing Hodge class has strictly POSITIVE residual square, whereas
algebraic targets have zero residual once the full algebraic primitive
subspace has been used as source basis.

This is a sharp numerical invariant for the ORIGINAL GST
omniversal ghost question. It does not independently prove that
the residual vanishes, and does not smuggle in such a premise.
-/

set_option maxHeartbeats 3500000
noncomputable section

open GSTUniversalHodgeResidualProjection

namespace GSTPolarizedHodgeResidualEnergy

variable {ι N V : Type*}
  [Fintype ι] [DecidableEq ι]
  [AddCommGroup N] [Module ℚ N]
  [AddCommGroup V] [Module ℚ V]

/-- The class of the native projection is orthogonal to the true
Hodge residual, provided the probes are actual polarization
intersection readouts. This identity has NO target-preimage premise. -/
theorem residual_orthogonal_to_algebraic_projection
    (P : GeometricDualCyclePacket ι N V)
    (Q : V →ₗ[ℚ] V →ₗ[ℚ] ℚ)
    (hGeometricPairing :
      ∀ (i : ι) (x : V),
        P.detectors i x = (Q x) (P.cycleClass (P.cycles i)))
    (alpha : V) :
    (Q (residualClass P alpha))
      (P.cycleClass (projectedNativeCycle P alpha)) = 0 := by
  classical
  have hzero (i : ι) :
      (Q (residualClass P alpha))
        (P.cycleClass (P.cycles i)) = 0 := by
    rw [← hGeometricPairing i (residualClass P alpha)]
    exact residual_orthogonal_to_all_geometric_cycles P alpha i
  calc
    (Q (residualClass P alpha))
        (P.cycleClass (projectedNativeCycle P alpha)) =
      ∑ i, (P.detectors i alpha) *
          ((Q (residualClass P alpha))
            (P.cycleClass (P.cycles i))) := by
          simp [projectedNativeCycle, map_sum, map_smul]
    _ = 0 := by simp [hzero]

/-- Polarized primitive Hodge-PYTHAGORAS with a genuine native
algebraic projection on the ORIGINAL target carrier. -/
theorem primitive_polarization_pythagoras
    (P : GeometricDualCyclePacket ι N V)
    (Q : V →ₗ[ℚ] V →ₗ[ℚ] ℚ)
    (hSym : ∀ x y : V, (Q x) y = (Q y) x)
    (hGeometricPairing :
      ∀ (i : ι) (x : V),
        P.detectors i x = (Q x) (P.cycleClass (P.cycles i)))
    (alpha : V) :
    (Q alpha) alpha =
      (Q (P.cycleClass (projectedNativeCycle P alpha)))
        (P.cycleClass (projectedNativeCycle P alpha)) +
      (Q (residualClass P alpha)) (residualClass P alpha) := by
  let a := P.cycleClass (projectedNativeCycle P alpha)
  let r := residualClass P alpha
  have hsum : a + r = alpha :=
    actual_cycle_plus_residual_equals_target P alpha
  have hcross : (Q r) a = 0 :=
    residual_orthogonal_to_algebraic_projection
      P Q hGeometricPairing alpha
  have hcross' : (Q a) r = 0 := by
    rw [hSym a r]
    exact hcross
  change (Q alpha) alpha = (Q a) a + (Q r) r
  calc
    (Q alpha) alpha = (Q (a+r)) (a+r) := by rw [hsum]
    _ = (Q a) a + (Q a) r + (Q r) a + (Q r) r := by
      simp only [map_add, LinearMap.add_apply]
      ring
    _ = (Q a) a + (Q r) r := by rw [hcross, hcross']; ring

/-- If alpha is NOT algebraically representable, its canonical
residual has strictly POSITIVE polarization energy whenever
Q is genuinely positive definite on the primitive Hodge fiber.
This is a real obstruction certificate, not a universal
vanishing theorem. -/
theorem nonalgebraic_primitive_forces_positive_residual_energy
    (P : GeometricDualCyclePacket ι N V)
    (Q : V →ₗ[ℚ] V →ₗ[ℚ] ℚ)
    (hPositive : ∀ v : V, v ≠ 0 → 0 < (Q v) v)
    (alpha : V)
    (hmissing : alpha ∉ LinearMap.range P.cycleClass) :
    0 < (Q (residualClass P alpha)) (residualClass P alpha) := by
  exact hPositive _ (any_unrepresented_target_has_nonzero_residual
    P alpha hmissing)

#check residual_orthogonal_to_algebraic_projection
#check primitive_polarization_pythagoras
#check nonalgebraic_primitive_forces_positive_residual_energy
#print axioms primitive_polarization_pythagoras
#print axioms nonalgebraic_primitive_forces_positive_residual_energy

end GSTPolarizedHodgeResidualEnergy
