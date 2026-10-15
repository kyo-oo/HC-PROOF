import Mathlib

/-!
# GST arbitrary-codimension smooth blow-up transfer

A codimension-c smooth blow-up carries a finite family of exceptional summands,
one for every 1 <= r < c. The source Hodge spaces can have DIFFERENT types:
the r-th source corresponds geometrically to H^(2(p-r))(Z,Q)(-r).

This constructive theorem takes the actual geometric decomposition and the
forward native-to-Betti naturality squares, then builds an algebraic witness
by summing explicit native base and exceptional cycle operations.

No target surjectivity, arbitrary target preimage, primitive seed assumption,
CM denominator nonvanishing, or universal matrix-unit generator is postulated.
The actual scheme-theoretic blow-up decomposition is external geometric input,
not a theorem formalized by this module.
-/

set_option maxHeartbeats 3000000
noncomputable section

namespace GSTBlowupHodgeAllCodimension

/-- Exact finite-exceptional-source interface for a smooth blow-up at
an arbitrary fixed rational Hodge weight. Index r is the exceptional twist.
The source types may differ at EVERY r. -/
structure FiniteBlowupPresentation
    (ι : Type*) [Fintype ι]
    (NB NT HB HT : Type*) (NE HE : ι → Type*)
    [AddCommGroup NB] [Module ℚ NB]
    [AddCommGroup NT] [Module ℚ NT]
    [AddCommGroup HB] [Module ℚ HB]
    [AddCommGroup HT] [Module ℚ HT]
    [∀ r, AddCommGroup (NE r)] [∀ r, Module ℚ (NE r)]
    [∀ r, AddCommGroup (HE r)] [∀ r, Module ℚ (HE r)] where
  clBase : NB →ₗ[ℚ] HB
  clExceptional : ∀ r, NE r →ₗ[ℚ] HE r
  clTarget : NT →ₗ[ℚ] HT
  nativeBase : NB →ₗ[ℚ] NT
  nativeExceptional : ∀ r, NE r →ₗ[ℚ] NT
  toHodgeBase : HB →ₗ[ℚ] HT
  toHodgeExceptional : ∀ r, HE r →ₗ[ℚ] HT
  projectBase : HT →ₗ[ℚ] HB
  projectExceptional : ∀ r, HT →ₗ[ℚ] HE r
  geometricDecomposition : ∀ alpha : HT,
    toHodgeBase (projectBase alpha) +
      ∑ r, toHodgeExceptional r (projectExceptional r alpha) = alpha
  nativeBaseNaturality : ∀ z : NB,
    clTarget (nativeBase z) = toHodgeBase (clBase z)
  nativeExceptionalNaturality : ∀ r (z : NE r),
    clTarget (nativeExceptional r z) =
      toHodgeExceptional r (clExceptional r z)

variable
    {ι : Type*} [Fintype ι]
    {NB NT HB HT : Type*} {NE HE : ι → Type*}
    [AddCommGroup NB] [Module ℚ NB]
    [AddCommGroup NT] [Module ℚ NT]
    [AddCommGroup HB] [Module ℚ HB]
    [AddCommGroup HT] [Module ℚ HT]
    [∀ r, AddCommGroup (NE r)] [∀ r, Module ℚ (NE r)]
    [∀ r, AddCommGroup (HE r)] [∀ r, Module ℚ (HE r)]

/-- Native cycle constructed as an actual finite sum of geometrically allowed
pullback/Gysin operations on independently realized SOURCE Hodge classes. -/
noncomputable def constructFiniteBlowupCycle
    (B : FiniteBlowupPresentation ι NB NT HB HT NE HE)
    (hBase : ∀ beta : HB, ∃ Z : NB, B.clBase Z = beta)
    (hExceptional : ∀ r (beta : HE r),
      ∃ Z : NE r, B.clExceptional r Z = beta)
    (alpha : HT) : NT := by
  classical
  exact
    B.nativeBase (Classical.choose (hBase (B.projectBase alpha))) +
      ∑ r, B.nativeExceptional r
        (Classical.choose (hExceptional r (B.projectExceptional r alpha)))

/-- Every exact target Hodge class gets its own native cycle, constructed
without using target cycle-class surjectivity anywhere. -/
theorem constructFiniteBlowupCycle_correct
    (B : FiniteBlowupPresentation ι NB NT HB HT NE HE)
    (hBase : ∀ beta : HB, ∃ Z : NB, B.clBase Z = beta)
    (hExceptional : ∀ r (beta : HE r),
      ∃ Z : NE r, B.clExceptional r Z = beta)
    (alpha : HT) :
    B.clTarget (constructFiniteBlowupCycle B hBase hExceptional alpha)
      = alpha := by
  classical
  calc
    B.clTarget (constructFiniteBlowupCycle B hBase hExceptional alpha) =
      B.toHodgeBase
        (B.clBase (Classical.choose (hBase (B.projectBase alpha)))) +
      ∑ r, B.toHodgeExceptional r
        (B.clExceptional r
          (Classical.choose (hExceptional r (B.projectExceptional r alpha)))) := by
          simp [constructFiniteBlowupCycle, B.nativeBaseNaturality,
            B.nativeExceptionalNaturality]
    _ = B.toHodgeBase (B.projectBase alpha) +
        ∑ r, B.toHodgeExceptional r (B.projectExceptional r alpha) := by
          have hex (r : ι) :
              B.clExceptional r
                (Classical.choose (hExceptional r (B.projectExceptional r alpha))) =
              B.projectExceptional r alpha :=
            Classical.choose_spec (hExceptional r (B.projectExceptional r alpha))
          simp [hex, Classical.choose_spec (hBase (B.projectBase alpha))]
    _ = alpha := B.geometricDecomposition alpha

/-- Strong finite-rank conclusion for every smooth blow-up codimension:
the target Hodge-fiber cycle-class map is surjective once each independent
geometric source is already known algebraic. -/
theorem finite_blowup_preserves_all_rational_hodge_classes
    (B : FiniteBlowupPresentation ι NB NT HB HT NE HE)
    (hBase : ∀ beta : HB, ∃ Z : NB, B.clBase Z = beta)
    (hExceptional : ∀ r (beta : HE r),
      ∃ Z : NE r, B.clExceptional r Z = beta) :
    Function.Surjective B.clTarget := by
  intro alpha
  exact ⟨constructFiniteBlowupCycle B hBase hExceptional alpha,
    constructFiniteBlowupCycle_correct B hBase hExceptional alpha⟩

/-- A genuine primitive target Hodge class is hit by an actual algebraic cycle
whose class satisfies the same Lefschetz kernel equation. -/
theorem finite_blowup_primitive_realization
    {P : Type*} [AddCommGroup P] [Module ℚ P]
    (B : FiniteBlowupPresentation ι NB NT HB HT NE HE)
    (hBase : ∀ beta : HB, ∃ Z : NB, B.clBase Z = beta)
    (hExceptional : ∀ r (beta : HE r),
      ∃ Z : NE r, B.clExceptional r Z = beta)
    (L : HT →ₗ[ℚ] P) (alpha : HT)
    (hprimitive : L alpha = 0) :
    ∃ Z : NT, B.clTarget Z = alpha ∧
      L (B.clTarget Z) = 0 := by
  refine ⟨constructFiniteBlowupCycle B hBase hExceptional alpha,
    constructFiniteBlowupCycle_correct B hBase hExceptional alpha, ?_⟩
  rw [constructFiniteBlowupCycle_correct B hBase hExceptional alpha]
  exact hprimitive

#check constructFiniteBlowupCycle
#check constructFiniteBlowupCycle_correct
#check finite_blowup_preserves_all_rational_hodge_classes
#check finite_blowup_primitive_realization
#print axioms constructFiniteBlowupCycle_correct
#print axioms finite_blowup_primitive_realization

end GSTBlowupHodgeAllCodimension
