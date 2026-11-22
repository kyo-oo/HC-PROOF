import Mathlib
import GSTSphereUnionComponents
import GSTProjectiveOverC

/-
Copyright (c) 2026. The HC-PROOF campaign. All rights reserved.

# WAVE 3-A — THE RIEMANN-SPHERE COORDINATE EQUIVALENCE (the finite-line
analytification's arithmetic core)

The stereographic type-equivalence `unitSphereType ≃ Option ℂ` between the
corpus's honest 2-sphere (the metric sphere in `EuclideanSpace ℝ (Fin 3)`,
the analytification shape of every line of the finite-line world) and the
extended complex plane `Option ℂ = ℂ ⊔ {∞}` (the two-chart coordinate model
of the projective line: `some t` = the chart coordinate `t`, `none` = the
point at infinity on the second chart).

This is the self-contained arithmetic component of the analytification
bridge (the unconditional round's Task 2): the scheme-side point
classification (`ComplexPoint (finitePointWorld`-style, on the finite-line
world) is assembled on top in the follow-up waves, and the assembled
`AnalytificationData`'s `pointsEquiv` rides this equivalence slice-by-slice.

The arithmetic is pure real algebra on the coordinates: the sphere equation
`x² + y² + z² = 1` transports the chart identity
`(2a)² + (2b)² + (s-1)² = (s+1)²` at `s = a² + b²`, and the two
cancellation laws are field cancellations at the non-pole `z ≠ 1`.

Honesty ledger: zero `sorry`, zero new axioms, zero `native_decide`.  Every
non-local name is pin-verified at Mathlib 51e6992efd06126df61a496bebf8f49482a4e129
(`EuclideanSpace.real_norm_sq_eq`, `PiLp.toLp_apply` (rfl), the `Matrix`
cons family, `mem_sphere_zero_iff_norm`, `sq_eq_one_iff`) or CI-green in
the corpus.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open Real
open GSTProjectiveOverC GSTSphereUnionComponents

namespace GSTFiniteLineRiemann

/-! ## §0 The coordinate form of the sphere equation -/

/-- The norm-square of a 3-vector in coordinate form (the pinned
`EuclideanSpace.real_norm_sq_eq` + `Fin.sum_univ_three`, isolated once). -/
theorem sphere_norm_sq (v : EuclideanSpace ℝ (Fin 3)) :
    ‖v‖ ^ 2 = (v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  ring

/-- **THE SPHERE EQUATION IN COORDINATES** — the metric-sphere membership
is the unit equation on the three coordinates. -/
theorem mem_sphere_iff_coord (v : EuclideanSpace ℝ (Fin 3)) :
    v ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↔
      (v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2 = 1 := by
  rw [mem_sphere_zero_iff_norm]
  constructor
  · intro h
    have h2 : ‖v‖ ^ 2 = 1 := by rw [h, one_pow]
    rwa [sphere_norm_sq] at h2
  · intro h
    have hn : 0 ≤ ‖v‖ := norm_nonneg v
    have h2 : ‖v‖ ^ 2 = 1 := by rw [sphere_norm_sq, h]
    rcases (sq_eq_one_iff hn).mp h2 with h1 | h1
    · exact h1
    · linarith

/-! ## §1 The forward coordinate map -/

/-- The north pole (the point at infinity's sphere image). -/
def northPole : unitSphereType :=
  ⟨WithLp.toLp 2 ![0, 0, 1], by
    rw [mem_sphere_iff_coord]
    norm_num⟩

/-- The coordinates of the forward stereographic image of `t ∈ ℂ`. -/
def stereoCoord (t : ℂ) : Fin 3 → ℝ :=
  ![2 * t.re / (t.re * t.re + t.im * t.im + 1),
    2 * t.im / (t.re * t.re + t.im * t.im + 1),
    (t.re * t.re + t.im * t.im - 1) / (t.re * t.re + t.im * t.im + 1)]

/-- The denominator positivity of the stereographic image. -/
theorem stereoCoord_denom_pos (t : ℂ) :
    0 < t.re * t.re + t.im * t.im + 1 := by
  have h1 : 0 ≤ t.re * t.re := sq_nonneg t.re
  have h2 : 0 ≤ t.im * t.im := sq_nonneg t.im
  linarith

/-- **THE STEREOGRAPHIC IMAGE IS ON THE SPHERE** — the chart identity
`(2a)² + (2b)² + (s-1)² = (s+1)²` at `s = a² + b²`. -/
theorem stereoCoord_mem (t : ℂ) :
    (WithLp.toLp 2 (stereoCoord t) : EuclideanSpace ℝ (Fin 3)) ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  rw [mem_sphere_iff_coord]
  have hd : t.re * t.re + t.im * t.im + 1 ≠ 0 := by
    exact ne_of_gt (stereoCoord_denom_pos t)
  have h0 : (WithLp.toLp 2 (stereoCoord t) : EuclideanSpace ℝ (Fin 3)) 0
      = 2 * t.re / (t.re * t.re + t.im * t.im + 1) := rfl
  have h1 : (WithLp.toLp 2 (stereoCoord t) : EuclideanSpace ℝ (Fin 3)) 1
      = 2 * t.im / (t.re * t.re + t.im * t.im + 1) := rfl
  have h2 : (WithLp.toLp 2 (stereoCoord t) : EuclideanSpace ℝ (Fin 3)) 2
      = (t.re * t.re + t.im * t.im - 1) /
          (t.re * t.re + t.im * t.im + 1) := rfl
  rw [h0, h1, h2]
  field_simp
  ring

/-- **THE FORWARD COORDINATE MAP** — `none` ↦ the north pole;
`some t` ↦ the stereographic image of `t`. -/
def coordToSphere : Option ℂ → unitSphereType
  | none => northPole
  | some t => ⟨WithLp.toLp 2 (stereoCoord t), stereoCoord_mem t⟩

/-! ## §2 The inverse coordinate map -/

/-- **THE INVERSE COORDINATE MAP** — `v ↦ none` at the north pole;
`v ↦ some ⟨v 0 / (1 - v 2), v 1 / (1 - v 2)⟩` elsewhere. -/
def sphereToCoord (v : unitSphereType) : Option ℂ :=
  if v 2 = 1 then none
  else some ⟨v 0 / (1 - v 2), v 1 / (1 - v 2)⟩

/-- The non-pole denominator positivity. -/
theorem sphere_denom_pos {v : unitSphereType} (hv : v 2 ≠ 1) :
    0 < 1 - v 2 := by
  have hs : (v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2 = 1 :=
    (mem_sphere_iff_coord _).mp v.2
  have h0 : 0 ≤ (v 0) ^ 2 := sq_nonneg _
  have h1 : 0 ≤ (v 1) ^ 2 := sq_nonneg _
  have h2 : 0 ≤ (v 2) ^ 2 := sq_nonneg _
  have hle : v 2 ≤ 1 := by
    by_contra hcon
    push_neg at hcon
    have : 1 < (v 2) ^ 2 := by nlinarith
    nlinarith
  rcases lt_or_eq_of_le hle with h | h
  · linarith
  · exact absurd h hv

/-- The pole case: `v 2 = 1` forces the first two coordinates to vanish
(the sphere equation), so `v` IS the north pole. -/
theorem eq_northPole_of_pole {v : unitSphereType} (hv : v 2 = 1) :
    v = northPole := by
  have hs : (v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2 = 1 :=
    (mem_sphere_iff_coord _).mp v.2
  rw [hv] at hs
  have h0 : v 0 = 0 := by
    have : (v 0) ^ 2 = 0 := by nlinarith
    exact pow_eq_zero_iff two_ne_zero |>.mp this
  have h1 : v 1 = 0 := by
    have : (v 1) ^ 2 = 0 := by nlinarith
    exact pow_eq_zero_iff two_ne_zero |>.mp this
  ext i
  fin_cases i
  · simp [northPole, h0, Matrix.cons_val_zero, PiLp.toLp_apply]
  · simp [northPole, h1, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_succ, PiLp.toLp_apply]
  · simp [northPole, hv, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.cons_val_succ, PiLp.toLp_apply]

/-! ## §3 The two cancellation laws -/

/-- **THE FIRST CANCELLATION** — the coordinate map reads the stereographic
image back to the original coordinate (the pole case by the pole lemma, the
non-pole case by the two field cancellations). -/
theorem sphereToCoord_coordToSphere (t : Option ℂ) :
    sphereToCoord (coordToSphere t) = t := by
  cases t with
  | none =>
      simp only [coordToSphere, sphereToCoord]
      rw [if_pos rfl]
  | some t =>
      simp only [coordToSphere, sphereToCoord]
      have hz : (⟨WithLp.toLp 2 (stereoCoord t), stereoCoord_mem t⟩ :
          unitSphereType) 2 ≠ 1 := by
        intro hcon
        have hd := stereoCoord_denom_pos t
        have hx : (⟨WithLp.toLp 2 (stereoCoord t), stereoCoord_mem t⟩ :
            unitSphereType) 2
            = (t.re * t.re + t.im * t.im - 1) /
                (t.re * t.re + t.im * t.im + 1) := rfl
        rw [hx] at hcon
        field_simp at hcon
        linarith
      rw [if_neg hz]
      congr 1
      have hd : 1 - (t.re * t.re + t.im * t.im - 1) /
          (t.re * t.re + t.im * t.im + 1) ≠ 0 := by
        have hd0 := stereoCoord_denom_pos t
        field_simp
        linarith
      have hx : (⟨WithLp.toLp 2 (stereoCoord t), stereoCoord_mem t⟩ :
          unitSphereType) 0
          = 2 * t.re / (t.re * t.re + t.im * t.im + 1) := rfl
      have hy : (⟨WithLp.toLp 2 (stereoCoord t), stereoCoord_mem t⟩ :
          unitSphereType) 1
          = 2 * t.im / (t.re * t.re + t.im * t.im + 1) := rfl
      rw [hx, hy]
      simp only [Complex.ext_iff, Complex.ofReal_re, Complex.ofReal_im,
        Complex.add_re, Complex.add_im, Complex.mk_re, Complex.mk_im]
      constructor
      · field_simp
        ring
      · field_simp
        ring

/-- **THE SECOND CANCELLATION** — the coordinate map's image of any sphere
point is the original sphere point (the pole case by the pole lemma, the
non-pole case by the sphere-equation field cancellations). -/
theorem coordToSphere_sphereToCoord (v : unitSphereType) :
    coordToSphere (sphereToCoord v) = v := by
  by_cases hv : v 2 = 1
  · rw [sphereToCoord, if_pos hv, coordToSphere]
    exact (eq_northPole_of_pole hv).symm
  · have hs : (v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2 = 1 :=
      (mem_sphere_iff_coord _).mp v.2
    have hsq : (v 0) ^ 2 + (v 1) ^ 2 = 1 - (v 2) ^ 2 := by ring_nf; linarith
    have hz1 : 1 - v 2 ≠ 0 := by
      have := sphere_denom_pos hv
      linarith
    rw [sphereToCoord, if_neg hv]
    simp only [coordToSphere]
    have hd : (v 0 / (1 - v 2)) * (v 0 / (1 - v 2)) +
        (v 1 / (1 - v 2)) * (v 1 / (1 - v 2)) + 1 ≠ 0 := by
      have h0 : 0 ≤ (v 0) ^ 2 := sq_nonneg _
      have h1 : 0 ≤ (v 1) ^ 2 := sq_nonneg _
      have hp : 0 < 1 - v 2 := sphere_denom_pos hv
      field_simp
      nlinarith
    ext i
    fin_cases i
    · have hx : (coordToSphere (some ⟨v 0 / (1 - v 2), v 1 / (1 - v 2)⟩ :
          unitSphereType)) 0
          = 2 * (v 0 / (1 - v 2)) /
              ((v 0 / (1 - v 2)) * (v 0 / (1 - v 2)) +
                (v 1 / (1 - v 2)) * (v 1 / (1 - v 2)) + 1) := rfl
      rw [hx]
      simp only [PiLp.toLp_apply, Matrix.cons_val_zero]
      field_simp
      ring
    · have hy : (coordToSphere (some ⟨v 0 / (1 - v 2), v 1 / (1 - v 2)⟩ :
          unitSphereType)) 1
          = 2 * (v 1 / (1 - v 2)) /
              ((v 0 / (1 - v 2)) * (v 0 / (1 - v 2)) +
                (v 1 / (1 - v 2)) * (v 1 / (1 - v 2)) + 1) := rfl
      rw [hy]
      simp only [PiLp.toLp_apply, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_succ]
      field_simp
      ring
    · have hzc : (coordToSphere (some ⟨v 0 / (1 - v 2), v 1 / (1 - v 2)⟩ :
          unitSphereType)) 2
          = ((v 0 / (1 - v 2)) * (v 0 / (1 - v 2)) +
              (v 1 / (1 - v 2)) * (v 1 / (1 - v 2)) - 1) /
              ((v 0 / (1 - v 2)) * (v 0 / (1 - v 2)) +
                (v 1 / (1 - v 2)) * (v 1 / (1 - v 2)) + 1) := rfl
      rw [hzc]
      simp only [PiLp.toLp_apply, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.cons_val_succ]
      field_simp
      ring

/-! ## §4 The bundled equivalence -/

/-- **THE RIEMANN-SPHERE TYPE EQUIVALENCE** — the honest 2-sphere is the
extended complex plane: the two-chart coordinate model of the projective
line, in both directions, by the two cancellation laws. -/
def riemannSphereEquiv : unitSphereType ≃ Option ℂ :=
  ⟨sphereToCoord, coordToSphere,
    sphereToCoord_coordToSphere, coordToSphere_sphereToCoord⟩

end GSTFiniteLineRiemann

end
