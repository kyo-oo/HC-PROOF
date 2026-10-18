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


/-! ## GST automatic independent geometric readout from POLARIZED residual energy

The old arbitrary-rank native coordinate theorem required an externally chosen
linear readout vanishing on all old classes and nonzero on a born class.
Here we construct that readout **from the actual polarized Hodge pairing**
and the canonical finite native residual.

For an independently constructed native fresh cycle, the residual r of its
real cycle class v after subtracting the known geometric dual basis defines
a native, canonically computed readout Q(r, -). Geometric polarization forces
this readout to vanish on all old cycle classes; a nonzero (positive) residual
energy Q(r,r) forces it to detect the fresh cycle class. Thus the GST birth
increases actual algebraic Hodge rank, with no free readout-choice premise.

The input fresh remains an ACTUAL native cycle, and the geometric pairing and
positivity must be independently verified on the original X. This theorem
does not manufacture an arbitrary requested primitive Chow representative.
-/

/-- GST builds the independent coordinate readout DIRECTLY from its
polarized residual. For every old genuine native generator, it is zero. -/
theorem native_residual_builds_geometric_readout
    (P : GeometricDualCyclePacket ι N V)
    (Q : V →ₗ[ℚ] V →ₗ[ℚ] ℚ)
    (hPair :
      ∀ (i : ι) (x : V),
        P.detectors i x = (Q x) (P.cycleClass (P.cycles i)))
    (fresh : N) (i : ι) :
    (Q (residualClass P (P.cycleClass fresh)))
      (P.cycleClass (P.cycles i)) = 0 := by
  rw [← hPair i (residualClass P (P.cycleClass fresh))]
  exact residual_orthogonal_to_all_geometric_cycles P
    (P.cycleClass fresh) i

/-- The same CANONICAL residual readout evaluates on the fresh native
cycle to exactly its polarized energy, no arbitrary readout parameter. -/
theorem native_residual_readout_fresh_eq_energy
    (P : GeometricDualCyclePacket ι N V)
    (Q : V →ₗ[ℚ] V →ₗ[ℚ] ℚ)
    (hPair :
      ∀ (i : ι) (x : V),
        P.detectors i x = (Q x) (P.cycleClass (P.cycles i)))
    (fresh : N) :
    (Q (residualClass P (P.cycleClass fresh)))
      (P.cycleClass fresh) =
    (Q (residualClass P (P.cycleClass fresh)))
      (residualClass P (P.cycleClass fresh)) := by
  let v := P.cycleClass fresh
  have hsum := actual_cycle_plus_residual_equals_target P v
  have hcross := residual_orthogonal_to_algebraic_projection P Q hPair v
  calc
    (Q (residualClass P v)) v =
        (Q (residualClass P v))
          (P.cycleClass (projectedNativeCycle P v) +
            residualClass P v) := by rw [hsum]
    _ = (Q (residualClass P v))
          (P.cycleClass (projectedNativeCycle P v)) +
        (Q (residualClass P v)) (residualClass P v) := by
          rw [map_add]
    _ = (Q (residualClass P v)) (residualClass P v) := by
      rw [hcross]
      ring

/-- A new GST geometric cycle with strictly positive measured residual
energy **automatically increases the ACTUAL native algebraic Hodge span**.
The complete readout is Q(r,-), constructed from old native cycles
and their canonical Hodge intersection values. No hFresh readout premise. -/
theorem positive_residual_energy_forces_strict_native_rank_birth
    (P : GeometricDualCyclePacket ι N V)
    (Q : V →ₗ[ℚ] V →ₗ[ℚ] ℚ)
    (hPair :
      ∀ (i : ι) (x : V),
        P.detectors i x = (Q x) (P.cycleClass (P.cycles i)))
    (fresh : N)
    (hEnergy :
      0 < (Q (residualClass P (P.cycleClass fresh)))
        (residualClass P (P.cycleClass fresh))) :
    Submodule.span ℚ (Set.range (fun i : ι => P.cycleClass (P.cycles i))) <
      Submodule.span ℚ
        (Set.insert (P.cycleClass fresh)
          (Set.range (fun i : ι => P.cycleClass (P.cycles i)))) := by
  let readout : V →ₗ[ℚ] ℚ :=
    Q (residualClass P (P.cycleClass fresh))
  have hOld : ∀ i : ι, readout (P.cycleClass (P.cycles i)) = 0 :=
    native_residual_builds_geometric_readout P Q hPair fresh
  have hFresh : readout (P.cycleClass fresh) ≠ 0 := by
    rw [native_residual_readout_fresh_eq_energy P Q hPair fresh]
    exact ne_of_gt hEnergy
  have hnot :
      P.cycleClass fresh ∉
        Submodule.span ℚ (Set.range (fun i : ι => P.cycleClass (P.cycles i))) := by
    intro hspan
    have hker :
        Submodule.span ℚ
          (Set.range (fun i : ι => P.cycleClass (P.cycles i))) ≤
        LinearMap.ker readout := by
      apply Submodule.span_le.mpr
      rintro x ⟨i, rfl⟩
      exact LinearMap.mem_ker.mpr (hOld i)
    exact hFresh (LinearMap.mem_ker.mp (hker hspan))
  apply lt_of_le_of_ne
  · exact Submodule.span_mono (Set.subset_insert _ _)
  · intro heq
    have hnew :
      P.cycleClass fresh ∈
        Submodule.span ℚ
          (Set.insert (P.cycleClass fresh)
            (Set.range (fun i : ι => P.cycleClass (P.cycles i)))) :=
      Submodule.subset_span (Set.mem_insert _ _)
    rw [← heq] at hnew
    exact hnot hnew


/-- **GST geometric Gram-surplus rank birth.** The independent source
coordinate is certified directly by comparing only two genuine
intersection measurements: the fresh cycle's self-intersection and
the self-intersection of its exact already-algebraic projection.
No externally supplied `thirdRead` or `hFresh` hypothesis occurs;
the strict surplus is a geometric quantity measurable on the original
projective variety from actual algebraic source cycles. -/
theorem native_geometric_gram_surplus_forces_strict_rank_birth
    (P : GeometricDualCyclePacket ι N V)
    (Q : V →ₗ[ℚ] V →ₗ[ℚ] ℚ)
    (hSym : ∀ x y : V, (Q x) y = (Q y) x)
    (hPair :
      ∀ (i : ι) (x : V),
        P.detectors i x = (Q x) (P.cycleClass (P.cycles i)))
    (fresh : N)
    (hGram :
      (Q (P.cycleClass fresh)) (P.cycleClass fresh) >
      (Q (P.cycleClass (projectedNativeCycle P (P.cycleClass fresh))))
        (P.cycleClass (projectedNativeCycle P (P.cycleClass fresh)))) :
    Submodule.span ℚ
        (Set.range (fun i : ι => P.cycleClass (P.cycles i))) <
      Submodule.span ℚ
        (Set.insert (P.cycleClass fresh)
          (Set.range (fun i : ι => P.cycleClass (P.cycles i)))) := by
  have hPythagoras :=
    primitive_polarization_pythagoras P Q hSym hPair
      (P.cycleClass fresh)
  have hEnergy :
      0 < (Q (residualClass P (P.cycleClass fresh)))
        (residualClass P (P.cycleClass fresh)) := by
    linarith
  exact positive_residual_energy_forces_strict_native_rank_birth
    P Q hPair fresh hEnergy

#check native_geometric_gram_surplus_forces_strict_rank_birth
#print axioms native_geometric_gram_surplus_forces_strict_rank_birth

#check native_residual_builds_geometric_readout
#check native_residual_readout_fresh_eq_energy
#check positive_residual_energy_forces_strict_native_rank_birth
#print axioms positive_residual_energy_forces_strict_native_rank_birth

#check residual_orthogonal_to_algebraic_projection
#check primitive_polarization_pythagoras
#check nonalgebraic_primitive_forces_positive_residual_energy
#print axioms primitive_polarization_pythagoras
#print axioms nonalgebraic_primitive_forces_positive_residual_energy

end GSTPolarizedHodgeResidualEnergy
