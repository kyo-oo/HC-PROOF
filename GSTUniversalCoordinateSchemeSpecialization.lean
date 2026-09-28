import GSTGeometricRealizationStage2C
import GSTTruncatedWorldCohomologyRing

/-!
# GST UNIVERSAL COORDINATE SCHEME — SPECIALIZATION PRINCIPLE

Stage 2C already constructed the limitless GST coordinate geometry as the
actual affine scheme

    Spec(Z[H,V])

and every finite A x B observation as

    Spec(Z[H,V]/(H^B,V^A)).

What was missing downstream was the explicit universal property connecting
those schemes to ordinary coordinate rings.  This file supplies it.

For every commutative ring R and every chosen pair (h,v) in R there is a
canonical specialization Z[H,V] -> R.  Contravariance gives an actual scheme
morphism

    Spec(R) -> cosmicCoordinateScheme.

If h^B = 0 and v^A = 0, the specialization kills the finite-world truncation
ideal and therefore factors through the A x B world cohomology ring.  Hence
any two nilpotent geometric operators/functions of the required orders define
an honest morphism into the corresponding GST finite observation scheme.

This is pure scheme geometry.  It assumes no Hodge class, no cycle-class
surjectivity and no realization certificate.
-/

set_option maxHeartbeats 50000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicGeometry
open GSTTruncatedWorldCohomologyRing
open GSTGeometricRealizationStage2C
open MvPolynomial

namespace GSTUniversalCoordinateSchemeSpecialization

/-- Universal two-generator specialization of the limitless GST polynomial
coordinate algebra. -/
noncomputable def specializeWorldPoly
    (R : Type*) [CommRing R]
    (h v : R) : WorldPoly →+* R :=
  eval₂Hom (Int.castRingHom R) ![h,v]

@[simp]
theorem specializeWorldPoly_H
    (R : Type*) [CommRing R]
    (h v : R) :
    specializeWorldPoly R h v Hpoly = h := by
  unfold specializeWorldPoly Hpoly
  rw [eval₂Hom_X']
  simp

@[simp]
theorem specializeWorldPoly_V
    (R : Type*) [CommRing R]
    (h v : R) :
    specializeWorldPoly R h v Vpoly = v := by
  unfold specializeWorldPoly Vpoly
  rw [eval₂Hom_X']
  simp

/-- The universal specialization is uniquely determined by the images of H
and V together with the canonical integer structure. -/
theorem specializeWorldPoly_unique
    (R : Type*) [CommRing R]
    (h v : R)
    (f : WorldPoly →+* R)
    (hZ : f.comp (C : ℤ →+* WorldPoly) = Int.castRingHom R)
    (hH : f Hpoly = h)
    (hV : f Vpoly = v) :
    f = specializeWorldPoly R h v := by
  apply MvPolynomial.ringHom_ext
  · intro z
    have hz := congrArg (fun g : ℤ →+* R => g z) hZ
    simpa using hz
  · intro i
    fin_cases i
    · simpa [Hpoly] using hH
    · simpa [Vpoly] using hV

/-- Any affine commutative coordinate ring with two chosen elements maps
canonically into the limitless cosmic GST coordinate scheme. -/
noncomputable def specToCosmic
    (R : Type*) [CommRing R]
    (h v : R) :
    Spec (CommRingCat.of R) ⟶ cosmicCoordinateScheme :=
  Spec.map (CommRingCat.ofHom (specializeWorldPoly R h v))

/-- Nilpotence of the chosen pair kills every generator of the finite-world
truncation ideal. -/
theorem truncIdeal_le_ker_specialize
    (R : Type*) [CommRing R]
    (A B : Nat) (h v : R)
    (hh : h^B = 0)
    (hv : v^A = 0) :
    truncIdeal A B ≤ RingHom.ker (specializeWorldPoly R h v) := by
  rw [truncIdeal, Ideal.span_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · rw [RingHom.mem_ker, map_pow, specializeWorldPoly_H, hh]
  · rw [RingHom.mem_ker, map_pow, specializeWorldPoly_V, hv]

/-- The universal specialization descends through the finite A x B GST world
whenever the chosen pair satisfies the two finite nilpotence equations. -/
noncomputable def specializeWindowRing
    (R : Type*) [CommRing R]
    (A B : Nat) (h v : R)
    (hh : h^B = 0)
    (hv : v^A = 0) :
    WorldCohomologyRing A B →+* R :=
  Ideal.Quotient.lift
    (truncIdeal A B)
    (specializeWorldPoly R h v)
    (truncIdeal_le_ker_specialize R A B h v hh hv)

@[simp]
theorem specializeWindowRing_H
    (R : Type*) [CommRing R]
    (A B : Nat) (h v : R)
    (hh : h^B = 0)
    (hv : v^A = 0) :
    specializeWindowRing R A B h v hh hv (H A B) = h := by
  simp [specializeWindowRing, H]

@[simp]
theorem specializeWindowRing_V
    (R : Type*) [CommRing R]
    (A B : Nat) (h v : R)
    (hh : h^B = 0)
    (hv : v^A = 0) :
    specializeWindowRing R A B h v hh hv (V A B) = v := by
  simp [specializeWindowRing, V]

/-- Scheme-theoretic finite-window specialization. -/
noncomputable def specToWindow
    (R : Type*) [CommRing R]
    (A B : Nat) (h v : R)
    (hh : h^B = 0)
    (hv : v^A = 0) :
    Spec (CommRingCat.of R) ⟶ windowCoordinateScheme A B :=
  Spec.map (CommRingCat.ofHom
    (specializeWindowRing R A B h v hh hv))

/-- The finite specialization really is a factorization of the unrestricted
cosmic specialization through the finite GST observation scheme. -/
theorem specToWindow_triangle
    (R : Type*) [CommRing R]
    (A B : Nat) (h v : R)
    (hh : h^B = 0)
    (hv : v^A = 0) :
    specToWindow R A B h v hh hv ≫ windowToCosmicScheme A B =
      specToCosmic R h v := by
  unfold specToWindow windowToCosmicScheme specToCosmic
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply Ideal.Quotient.ringHom_ext
  ext i
  fin_cases i
  · simp [coordinateProjection, specializeWindowRing, specializeWorldPoly,
      Hpoly, H]
  · simp [coordinateProjection, specializeWindowRing, specializeWorldPoly,
      Vpoly, V]

/-- The universal scheme specialization crown. -/
theorem universal_coordinate_specialization_crown
    (R : Type*) [CommRing R]
    (A B : Nat) (h v : R)
    (hh : h^B = 0)
    (hv : v^A = 0) :
    (specializeWorldPoly R h v Hpoly = h)
      ∧ (specializeWorldPoly R h v Vpoly = v)
      ∧ (specializeWindowRing R A B h v hh hv (H A B) = h)
      ∧ (specializeWindowRing R A B h v hh hv (V A B) = v)
      ∧ (specToWindow R A B h v hh hv ≫ windowToCosmicScheme A B =
          specToCosmic R h v) := by
  exact ⟨specializeWorldPoly_H R h v,
    specializeWorldPoly_V R h v,
    specializeWindowRing_H R A B h v hh hv,
    specializeWindowRing_V R A B h v hh hv,
    specToWindow_triangle R A B h v hh hv⟩

#check specializeWorldPoly
#check specializeWorldPoly_H
#check specializeWorldPoly_V
#check specToCosmic
#check truncIdeal_le_ker_specialize
#check specializeWindowRing
#check specToWindow
#check specToWindow_triangle
#check universal_coordinate_specialization_crown

#print axioms specializeWorldPoly_H
#print axioms truncIdeal_le_ker_specialize
#print axioms specToWindow_triangle
#print axioms universal_coordinate_specialization_crown

end GSTUniversalCoordinateSchemeSpecialization
