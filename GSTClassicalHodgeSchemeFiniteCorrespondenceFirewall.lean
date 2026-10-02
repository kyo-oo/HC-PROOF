import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import GSTClassicalHodgeFiniteClosedCorrespondenceTranspose

/-!
# GST CLASSICAL HODGE — SCHEME-FINITE CORRESPONDENCE FIREWALL

The historical `FiniteClosedCorrespondence` carrier is intentionally weak: it
records a closed subscheme of `X × X` and finiteness of the SET of points in
each left fiber.  `BiFiniteClosedCorrespondence` adds the analogous right-fiber
condition.  Those structures are useful for the finite point-kernel calculus,
but their names must not be confused with a finite morphism of schemes.

This file installs the strict geometric layer.

A `SchemeFiniteClosedCorrespondence` requires the left projection

    C -> X

to satisfy Mathlib's genuine `AlgebraicGeometry.IsFinite` morphism predicate.
A `SchemeBiFiniteClosedCorrespondence` requires BOTH projections to be finite
morphisms.  Mathlib's finite-fiber theorem then forgets this strict object to
the older point-finite structures, so every existing native finite-kernel
construction remains available without weakening the new semantics.

The strict bi-finite object is closed under genuine factor-swap transpose.  In
particular, future first-ghost / correspondence packets can demand this strict
carrier while reusing all existing transition and native-cycle machinery via
`toBiFiniteClosedCorrespondence`.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

namespace GSTClassicalHodgeSchemeFiniteCorrespondenceFirewall

open GSTProjectiveOverC
open GSTClassicalHodgeProjectiveSelfCorrespondences
open GSTClassicalHodgeFiniteClosedCorrespondence
open GSTClassicalHodgeFiniteClosedCorrespondenceTranspose

variable {V : SmoothProjectiveComplexScheme}

/-- A genuine closed self-correspondence whose LEFT projection is a finite
morphism of schemes, not merely a map with a finite set-theoretic fiber. -/
structure SchemeFiniteClosedCorrespondence
    (V : SmoothProjectiveComplexScheme) where
  carrier : Scheme
  intoProduct : carrier ⟶ selfProduct V
  closedImmersion : IsClosedImmersion intoProduct
  left_isFinite : IsFinite (intoProduct ≫ fst V)

namespace SchemeFiniteClosedCorrespondence

/-- Genuine left projection. -/
abbrev left (K : SchemeFiniteClosedCorrespondence V) : K.carrier ⟶ V.X :=
  K.intoProduct ≫ fst V

/-- Scheme-theoretic finiteness implies the older finite-point-fiber condition.
This is the one-way semantic forgetful map used to reuse the established
native correspondence kernel. -/
noncomputable def toFiniteClosedCorrespondence
    (K : SchemeFiniteClosedCorrespondence V) :
    FiniteClosedCorrespondence V where
  carrier := K.carrier
  intoProduct := K.intoProduct
  closedImmersion := K.closedImmersion
  leftFiber_finite := by
    intro x
    letI : IsFinite K.left := K.left_isFinite
    have h := K.left.finite_preimage_singleton x
    simpa [left] using h

@[simp]
theorem toFiniteClosedCorrespondence_left
    (K : SchemeFiniteClosedCorrespondence V) :
    K.toFiniteClosedCorrespondence.left = K.left :=
  rfl

end SchemeFiniteClosedCorrespondence

/-- A genuine closed self-correspondence finite AS A SCHEME MORPHISM over both
projections.  This is the strict meaning of "bi-finite" used by the new
geometry firewall. -/
structure SchemeBiFiniteClosedCorrespondence
    (V : SmoothProjectiveComplexScheme)
    extends SchemeFiniteClosedCorrespondence V where
  right_isFinite : IsFinite (toSchemeFiniteClosedCorrespondence.intoProduct ≫ snd V)

namespace SchemeBiFiniteClosedCorrespondence

/-- Genuine right projection. -/
abbrev right (K : SchemeBiFiniteClosedCorrespondence V) : K.carrier ⟶ V.X :=
  K.intoProduct ≫ snd V

/-- Forget strict scheme-theoretic bi-finiteness to the existing point-finite
bi-correspondence API. -/
noncomputable def toBiFiniteClosedCorrespondence
    (K : SchemeBiFiniteClosedCorrespondence V) :
    BiFiniteClosedCorrespondence V where
  toFiniteClosedCorrespondence :=
    K.toSchemeFiniteClosedCorrespondence.toFiniteClosedCorrespondence
  rightFiber_finite := by
    intro x
    letI : IsFinite K.right := K.right_isFinite
    have h := K.right.finite_preimage_singleton x
    simpa [right] using h

@[simp]
theorem toBiFiniteClosedCorrespondence_left
    (K : SchemeBiFiniteClosedCorrespondence V) :
    K.toBiFiniteClosedCorrespondence.toFiniteClosedCorrespondence.left =
      K.toSchemeFiniteClosedCorrespondence.left :=
  rfl

@[simp]
theorem toBiFiniteClosedCorrespondence_right
    (K : SchemeBiFiniteClosedCorrespondence V) :
    K.toBiFiniteClosedCorrespondence.toFiniteClosedCorrespondence.right =
      K.right :=
  rfl

/-- **STRICT TRANSPOSE.**  Factor swap exchanges the two genuinely finite
projection morphisms, so the transpose of a scheme-bi-finite correspondence is
again scheme-bi-finite. -/
noncomputable def transpose
    (K : SchemeBiFiniteClosedCorrespondence V) :
    SchemeBiFiniteClosedCorrespondence V := by
  let e := selfProductSwapIso V
  letI : IsIso e.hom := e.isIso_hom
  refine {
    carrier := K.carrier
    intoProduct := K.intoProduct ≫ e.hom
    closedImmersion := ?_
    left_isFinite := ?_
    right_isFinite := ?_
  }
  · haveI hK : IsClosedImmersion K.intoProduct := K.closedImmersion
    infer_instance
  · simpa [e, selfProductSwapIso, SchemeFiniteClosedCorrespondence.left,
      right, Category.assoc] using K.right_isFinite
  · simpa [e, selfProductSwapIso, SchemeFiniteClosedCorrespondence.left,
      right, Category.assoc] using
      K.toSchemeFiniteClosedCorrespondence.left_isFinite

/-- Strict transpose exchanges the left projection with the original right
projection. -/
theorem transpose_left
    (K : SchemeBiFiniteClosedCorrespondence V) :
    K.transpose.toSchemeFiniteClosedCorrespondence.left = K.right := by
  change (K.intoProduct ≫ selfProductSwap V) ≫ fst V = K.intoProduct ≫ snd V
  rw [Category.assoc, selfProductSwap_fst]

/-- Strict transpose exchanges the right projection with the original left
projection. -/
theorem transpose_right
    (K : SchemeBiFiniteClosedCorrespondence V) :
    K.transpose.right = K.toSchemeFiniteClosedCorrespondence.left := by
  change (K.intoProduct ≫ selfProductSwap V) ≫ snd V = K.intoProduct ≫ fst V
  rw [Category.assoc, selfProductSwap_snd]

/-- Forgetting strict transpose agrees with the old geometric factor-swap at
least on both projection maps.  This is the semantic compatibility required by
all transition formulas downstream. -/
theorem weak_transpose_left
    (K : SchemeBiFiniteClosedCorrespondence V) :
    K.toBiFiniteClosedCorrespondence.transpose.left = K.right := by
  rw [BiFiniteClosedCorrespondence.transpose_left]
  rfl

/-- Right-hand projection compatibility of the forgotten transpose. -/
theorem weak_transpose_right
    (K : SchemeBiFiniteClosedCorrespondence V) :
    K.toBiFiniteClosedCorrespondence.transpose.right =
      K.toSchemeFiniteClosedCorrespondence.left := by
  rw [BiFiniteClosedCorrespondence.transpose_right]
  rfl

end SchemeBiFiniteClosedCorrespondence

#check SchemeFiniteClosedCorrespondence
#check SchemeFiniteClosedCorrespondence.toFiniteClosedCorrespondence
#check SchemeBiFiniteClosedCorrespondence
#check SchemeBiFiniteClosedCorrespondence.toBiFiniteClosedCorrespondence
#check SchemeBiFiniteClosedCorrespondence.transpose
#check SchemeBiFiniteClosedCorrespondence.transpose_left
#check SchemeBiFiniteClosedCorrespondence.transpose_right

#print axioms SchemeFiniteClosedCorrespondence.toFiniteClosedCorrespondence
#print axioms SchemeBiFiniteClosedCorrespondence.toBiFiniteClosedCorrespondence
#print axioms SchemeBiFiniteClosedCorrespondence.transpose
#print axioms SchemeBiFiniteClosedCorrespondence.transpose_left
#print axioms SchemeBiFiniteClosedCorrespondence.transpose_right

end GSTClassicalHodgeSchemeFiniteCorrespondenceFirewall
