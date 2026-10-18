import GSTUniversalHodgeResidualProjection
import GSTGraphV2SelfExpandingCosmology

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


/-! ## GST geometric world birth + native residual energy: INTEGRATED upgrade

Combine the user's ORIGINAL arbitrary-source self-expanding geometric birth,
the old independently constructed native cycles, and the polarized Hodge
intersection coordinate. The proof constructs the born native cycle using the
actual world birth, not a function from arbitrary Hodge classes to cycles;
then measures strict algebraic-rank growth by the COMPLETELY COMPUTED
two-term intersection Gram surplus, with no externally chosen third readout.

This is an effective bridge BETWEEN GST ontological birth and GST
polarized energy, over arbitrary original target-world cycle carrier.
The remaining geometric input is an independently constructed
birth on that world whose real Gram surplus is positive.
-/

universe uWorld uState uLaw uSort

/-- A genuine dependent GST geometric world-birth supplies a new
native geometric coordinate as soon as its intersection Gram
surplus is verified positive. The output class is the CANONICAL
cycle class of the BORN native object, not a free Hodge inverse. -/
theorem gst_world_birth_gram_surplus_constructs_fresh_native_class
    (C : GSTGraphV2SelfExpandingCosmology.SelfExpandingCosmos.{uWorld,uState,uLaw,uSort})
    (R : GSTGraphV2SelfExpandingCosmology.NativeGeometryBirth.GeometricCycleBirthRealization C)
    {I : Type uWorld} {src : I → C.World} {target : C.World}
    (e : C.Birth src target)
    [AddCommGroup (C.State target)] [Module ℚ (C.State target)]
    [AddCommGroup (C.Law target)] [Module ℚ (C.Law target)]
    (P : GeometricDualCyclePacket ι (C.State target) (C.Law target))
    (hCanonical :
      ∀ Z : C.State target,
        P.cycleClass Z = R.cycleClass target Z)
    (Q : C.Law target →ₗ[ℚ] C.Law target →ₗ[ℚ] ℚ)
    (hSym : ∀ x y : C.Law target, (Q x) y = (Q y) x)
    (hPair : ∀ (i : ι) (x : C.Law target),
      P.detectors i x = (Q x) (P.cycleClass (P.cycles i)))
    (sources : (i : I) → C.State (src i))
    (hGram :
      (Q (P.cycleClass (R.assembleNative e sources)))
        (P.cycleClass (R.assembleNative e sources)) >
      (Q (P.cycleClass (projectedNativeCycle P
        (P.cycleClass (R.assembleNative e sources)))))
        (P.cycleClass (projectedNativeCycle P
          (P.cycleClass (R.assembleNative e sources))))) :
    Submodule.span ℚ (Set.range
        (fun i : ι => R.cycleClass target (P.cycles i))) <
      Submodule.span ℚ
        (Set.insert
          (R.cycleClass target (R.assembleNative e sources))
          (Set.range (fun i : ι =>
            R.cycleClass target (P.cycles i)))) := by
  have hBorn :
      P.cycleClass (R.assembleNative e sources) =
        R.assembleHodge e (fun i => R.cycleClass (src i) (sources i)) :=
    (hCanonical _).trans (R.compatible e sources)
  have hRank :=
    native_geometric_gram_surplus_forces_strict_rank_birth
      P Q hSym hPair (R.assembleNative e sources) hGram
  simpa only [hCanonical] using hRank

#check gst_world_birth_gram_surplus_constructs_fresh_native_class
#print axioms gst_world_birth_gram_surplus_constructs_fresh_native_class


/-! ## GST FULL GRAM-DUAL POLARIZED BIRTH — no orthonormality shortcut

The old hPair hypothesis assumed that the normalized independent
native cycles were orthonormal for Q. On a cubic fourfold, the ACTUAL
hyperplane-square native class has intersection self-pairing THREE,
so that restriction would falsely reject honest native geometry.

A correct rational native detector is a GRAM-DUAL coordinate.
If old_i denote actual independent native cycle classes, the
only required Gram law is:
  Q(x,old_j) = Σ_i detector_i(x) Q(old_i,old_j).
It is derived, for a nondegenerate rational intersection Gram,
by multiplying the geometric intersection row by its inverse.
No square-root rational orthonormalization is required.

The following GST theorem constructs the missing-coordinate detector
Q(r,-) from that law and proves strict native rank gain using only
a POSITIVE geometric intersection Gram surplus. This handles
arbitrary positive rational Gram forms on original X.
-/

/-- GST rational Gram-dual geometry makes its TRUE native Hodge
residual orthogonal to EVERY old native cycle without requiring
that the native cycle intersection Gram is the identity matrix. -/
theorem gram_dual_residual_orthogonal_to_old_native
    (P : GeometricDualCyclePacket ι N V)
    (Q : V →ₗ[ℚ] V →ₗ[ℚ] ℚ)
    (hGramDual : ∀ (j : ι) (x : V),
      (Q x) (P.cycleClass (P.cycles j)) =
        ∑ i, (P.detectors i x) *
          (Q (P.cycleClass (P.cycles i)))
            (P.cycleClass (P.cycles j)))
    (alpha : V) (j : ι) :
    (Q (residualClass P alpha))
      (P.cycleClass (P.cycles j)) = 0 := by
  rw [hGramDual j (residualClass P alpha)]
  simp [residual_orthogonal_to_all_geometric_cycles P alpha]

/-- UNRESTRICTED RATIONAL GRAM GST NATIVE BIRTH.
The geometric Gram surplus is the primitive residual energy
and it is STRICTLY POSITIVE exactly when the new native direction
has positive residual energy. This suffices to construct the
actual native Hodge rank extension without any selected readout,
orthonormal basis, abstract Hodge inverse, or target preimage. -/
theorem arbitrary_rational_gram_surplus_constructs_native_rank_birth
    (P : GeometricDualCyclePacket ι N V)
    (Q : V →ₗ[ℚ] V →ₗ[ℚ] ℚ)
    (hSym : ∀ x y : V, (Q x) y = (Q y) x)
    (hGramDual : ∀ (j : ι) (x : V),
      (Q x) (P.cycleClass (P.cycles j)) =
        ∑ i, (P.detectors i x) *
          (Q (P.cycleClass (P.cycles i)))
            (P.cycleClass (P.cycles j)))
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
  let v : V := P.cycleClass fresh
  let a : V := P.cycleClass (projectedNativeCycle P v)
  let r : V := residualClass P v
  have hOld (i : ι) : (Q r) (P.cycleClass (P.cycles i)) = 0 :=
    gram_dual_residual_orthogonal_to_old_native P Q hGramDual v i
  have hcross : (Q r) a = 0 := by
    calc
      (Q r) a = ∑ i, (P.detectors i v) *
          ((Q r) (P.cycleClass (P.cycles i))) := by
            simp [a, projectedNativeCycle, map_sum, map_smul]
      _ = 0 := by simp [hOld]
  have hcross' : (Q a) r = 0 := by
    rw [hSym a r]
    exact hcross
  have hsum : a + r = v :=
    actual_cycle_plus_residual_equals_target P v
  have hpyth :
      (Q v) v = (Q a) a + (Q r) r := by
    calc
      (Q v) v = (Q (a+r)) (a+r) := by rw [hsum]
      _ = (Q a) a + (Q a) r + (Q r) a + (Q r) r := by
        simp only [map_add, LinearMap.add_apply]
        ring
      _ = (Q a) a + (Q r) r := by rw [hcross,hcross']; ring
  have hEnergy : 0 < (Q r) r := by
    have hge : (Q v) v > (Q a) a := hGram
    linarith
  have hRead : (Q r) v = (Q r) r := by
    calc
      (Q r) v = (Q r) (a+r) := by rw [hsum]
      _ = (Q r) a + (Q r) r := by rw [map_add]
      _ = (Q r) r := by rw [hcross]; ring
  have hFresh : (Q r) (P.cycleClass fresh) ≠ 0 := by
    change (Q r) v ≠ 0
    rw [hRead]
    exact ne_of_gt hEnergy
  have hnot :
      P.cycleClass fresh ∉
        Submodule.span ℚ
          (Set.range (fun i : ι => P.cycleClass (P.cycles i))) := by
    intro hspan
    have hker :
        Submodule.span ℚ
          (Set.range (fun i : ι => P.cycleClass (P.cycles i))) ≤
        LinearMap.ker (Q r) := by
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

#check gram_dual_residual_orthogonal_to_old_native
#check arbitrary_rational_gram_surplus_constructs_native_rank_birth
#print axioms arbitrary_rational_gram_surplus_constructs_native_rank_birth

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
