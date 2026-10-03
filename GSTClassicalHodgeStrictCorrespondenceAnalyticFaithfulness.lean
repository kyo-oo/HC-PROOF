import GSTClassicalHodgeStrictCorrespondenceAnalyticSpan
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# GST CLASSICAL HODGE — ANALYTIC CARRIER FAITHFULNESS

The intrinsic analytic carrier was defined as the image of actual complex
points of the strict correspondence in `X^an × X^an`.  A priori an image
construction could identify different carrier points.  For a genuine closed
correspondence this does not happen.

The closed immersion `C -> X × X` is a monomorphism.  Hence a complex point of
`C` is uniquely determined by its left and right projections.  Consequently
the pair map from actual carrier complex points to the intrinsic analytic
locus is injective, and therefore an equivalence onto that locus.

This removes a subtle quotient ambiguity from the analytic-span construction:
our `analyticCarrier` really represents the actual correspondence complex
points faithfully.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

namespace GSTClassicalHodgeStrictCorrespondenceAnalyticFaithfulness

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTClassicalHodgeProjectiveSelfCorrespondences
open GSTClassicalHodgeSchemeFiniteCorrespondenceFirewall
open GSTClassicalHodgeStrictCorrespondenceAnalyticSpan

variable {V : SmoothProjectiveComplexScheme}
variable (A : AnalytificationData V)

/-- Equality of both projected complex points forces equality of the original
carrier complex points. -/
theorem carrierComplexPoint_ext
    (K : SchemeBiFiniteClosedCorrespondence V)
    {z w : CarrierComplexPoint K}
    (hleft : leftComplexPoint K z = leftComplexPoint K w)
    (hright : rightComplexPoint K z = rightComplexPoint K w) :
    z = w := by
  have hleftHom :
      z.1 ≫ K.toSchemeFiniteClosedCorrespondence.left =
        w.1 ≫ K.toSchemeFiniteClosedCorrespondence.left := by
    exact congrArg Subtype.val hleft
  have hrightHom : z.1 ≫ K.right = w.1 ≫ K.right := by
    exact congrArg Subtype.val hright
  have hprod : z.1 ≫ K.intoProduct = w.1 ≫ K.intoProduct := by
    apply pullback.hom_ext
    · simpa [SchemeFiniteClosedCorrespondence.left, Category.assoc] using hleftHom
    · simpa [SchemeBiFiniteClosedCorrespondence.right, Category.assoc] using hrightHom
  haveI : IsClosedImmersion K.intoProduct := K.closedImmersion
  haveI : Mono K.intoProduct :=
    (IsClosedImmersion.iff_isFinite_and_mono (f := K.intoProduct)).mp K.closedImmersion |>.2
  have hz : z.1 = w.1 := by
    simpa using (cancel_mono K.intoProduct).mp hprod
  apply Subtype.ext
  exact hz

/-- **FAITHFUL ANALYTIC PAIR MAP.** -/
theorem carrierPointPair_injective
    (K : SchemeBiFiniteClosedCorrespondence V) :
    Function.Injective (carrierPointPair A K) := by
  intro z w h
  have hl :
      A.pointsEquiv (leftComplexPoint K z) =
        A.pointsEquiv (leftComplexPoint K w) :=
    congrArg Prod.fst h
  have hr :
      A.pointsEquiv (rightComplexPoint K z) =
        A.pointsEquiv (rightComplexPoint K w) :=
    congrArg Prod.snd h
  exact carrierComplexPoint_ext K
    (A.pointsEquiv.injective hl)
    (A.pointsEquiv.injective hr)

/-- Actual carrier complex points are canonically equivalent to the intrinsic
analytic locus. -/
noncomputable def carrierComplexPointEquivAnalyticCarrier
    (K : SchemeBiFiniteClosedCorrespondence V) :
    CarrierComplexPoint K ≃ analyticCarrier A K where
  toFun z := ⟨carrierPointPair A K z, ⟨z, rfl⟩⟩
  invFun q := Classical.choose q.2
  left_inv z := by
    apply carrierPointPair_injective A K
    exact Classical.choose_spec
      (show carrierPointPair A K z ∈ analyticLocus A K from ⟨z, rfl⟩)
  right_inv q := by
    apply Subtype.ext
    exact Classical.choose_spec q.2

@[simp]
theorem carrierComplexPointEquivAnalyticCarrier_val
    (K : SchemeBiFiniteClosedCorrespondence V)
    (z : CarrierComplexPoint K) :
    (carrierComplexPointEquivAnalyticCarrier A K z).1 = carrierPointPair A K z :=
  rfl

#check carrierComplexPoint_ext
#check carrierPointPair_injective
#check carrierComplexPointEquivAnalyticCarrier

#print axioms carrierComplexPoint_ext
#print axioms carrierPointPair_injective

end GSTClassicalHodgeStrictCorrespondenceAnalyticFaithfulness
