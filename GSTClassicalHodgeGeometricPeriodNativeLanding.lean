import GSTClassicalHodgeCanonicalPointIncidenceTransfer
import GSTClassicalHodgeSurfacePeriodCycleTransfer

/-!
# Genuine Stage-2G geometric-period cycle extraction

This specializes the abstract surface-period push/pull certificate to the
ACTUAL smooth-projective carrier, Mathlib codimension-p native algebraic
cycles, and rational Betti cohomology in HC-PROOF.

It uses *only* the proved canonical point-incidence-to-global transfer
theorem; the geometric incidence law and nonzero period are explicitly
displayed as the precise independent construction inputs. Neither the
Hodge conjecture nor any basis-cycle representative is assumed.

Research motivation: OpenAI math preprint, "The rational Hodge conjecture
for CM abelian varieties" (2026-09-30), Section 03 surface criterion.
The manuscript's special-CM surface period existence cannot simply be
applied to arbitrary smooth projective varieties.
-/

noncomputable section

open AlgebraicGeometry
namespace GSTClassicalHodgeGeometricPeriodNativeLanding

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeBettiCupGysinPrimitives
open GSTClassicalHodgeAmbientCorrespondenceKernelAction
open GSTClassicalHodgeSchemeFiniteCorrespondenceFirewall
open GSTClassicalHodgeFiniteClosedCorrespondence
open GSTClassicalHodgeFiniteClosedCorrespondenceOperator
open GSTClassicalHodgeCanonicalPointIncidenceTransfer
open GSTClassicalHodgeSurfacePeriodCycleTransfer

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {d p : Nat}

/-- A nonzero surface/correspondence period yields a concrete genuine
codimension-p algebraic cycle, *provided* the independently constructed
strict scheme-finite correspondence satisfies the direct Gysin incidence
identity on actual point-cycle classes.

This is the precise native surface-period output of the existing GST
incidence theorem. It does NOT assert existence of the missing input. -/
theorem actual_native_cycle_of_strict_geometric_period
    (P : RationalBettiIntersectionPrimitives H.analytification d)
    (K : SchemeBiFiniteClosedCorrespondence V)
    (κ : MiddleBettiCorrespondenceKernel H.analytification d K)
    (hinc : SuppliedPointDirectIncidenceLaw
      (V := V) (H := H) (d := d) (p := p) P K κ)
    (Z : codimensionCycles V.X p)
    (beta : RationalSingularCohomology H.analytification (2 * p))
    (k : ℚ)
    (hk : k ≠ 0)
    (hperiod :
      kernelAction H.analytification P κ (2 * p)
        (H.cycleClass p Z) = k • beta) :
    ∃ Y : codimensionCycles V.X p,
      H.cycleClass p Y = beta := by
  let A :=
    (K.toBiFiniteClosedCorrespondence.toFiniteClosedCorrespondence).nativeOperator p
  have hA : ∀ Z' : codimensionCycles V.X p,
      H.cycleClass p (A Z') =
        kernelAction H.analytification P κ (2 * p)
          (H.cycleClass p Z') := by
    intro Z'
    exact supplied_cycleClass_nativeOperator_of_suppliedPointDirectLaw
      P K κ hinc Z'
  exact exists_native_cycle_of_geometric_period
    (H.cycleClass p) A
    (kernelAction H.analytification P κ (2 * p))
    hA Z beta k hk hperiod

end GSTClassicalHodgeGeometricPeriodNativeLanding
