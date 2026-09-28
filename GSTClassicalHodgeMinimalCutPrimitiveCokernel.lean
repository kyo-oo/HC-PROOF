import GSTClassicalHodgePrimitiveQuotientDualProjectiveAction
import GSTClassicalHodgeMinimalPrimitiveSeparatorGhost

/-!
# GST CLASSICAL HODGE — MINIMAL PRINCIPAL-CUT PRIMITIVE COKERNEL

The all-lower-weight primitive quotient is intrinsic and very strong.  At a
positive least bad weight it has a particularly concrete first layer: the
minimal separator annihilates the complete Hodge image of the immediately
preceding genuine principal-cut operator.

Thus the obstruction already survives in the cokernel of the verified
principal cut from weight p-1 to p.  This is the exact one-step primitive
remainder to which Lefschetz/Poincare reasoning should be applied; no arbitrary
matrix-unit or correspondence action occurs in its definition.
-/

set_option maxHeartbeats 90000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeMinimalCutPrimitiveCokernel

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeGradedGeometricProgramOrbit
open GSTClassicalHodgeMinimalPrimitiveSeparatorGhost

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Restriction of the genuine principal-cut cohomological operator to the
source Hodge fiber. -/
noncomputable def principalCutOnHodge
    (G : GeometricCycleClassSpine V H)
    (q : Nat) :
    ClassicalHodgeFiber V H q →ₗ[ℚ]
      RationalSingularCohomology H.analytification (2 * (q + 1)) :=
  (G.principalCutPair q).cohomologyOperator.comp
    (rationalHodgeSubspace (H.hodgeBigrading q)).subtype

/-- One-step Hodge image of the genuine principal cut. -/
noncomputable def principalCutHodgeImage
    (G : GeometricCycleClassSpine V H)
    (q : Nat) :
    Submodule ℚ
      (RationalSingularCohomology H.analytification (2 * (q + 1))) :=
  LinearMap.range (principalCutOnHodge G q)

/-- The immediate cut image is contained in the intrinsic all-lower geometric
image at the next weight. -/
theorem principalCutHodgeImage_le_lowerGeometricImage
    (G : GeometricCycleClassSpine V H)
    (q : Nat) :
    principalCutHodgeImage G q ≤ lowerGeometricImage G (q + 1) := by
  rintro y ⟨alpha, rfl⟩
  apply Submodule.subset_span
  refine ⟨q, by omega, .cut q, alpha, ?_⟩
  rfl

/-- At positive minimal weight, the minimal separator kills the complete image
of the immediately preceding principal cut. -/
theorem minimalGhost_principalCutImage_le_ker
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    (hpos : 0 < M.weight) :
    principalCutHodgeImage G (M.weight - 1) ≤
      LinearMap.ker M.separator.detector := by
  intro y hy
  rcases hy with ⟨alpha, rfl⟩
  have hpred : M.weight - 1 < M.weight := by omega
  have hcut := M.primitive (M.weight - 1) hpred
    (.cut (M.weight - 1)) alpha
  simpa [principalCutOnHodge, show M.weight - 1 + 1 = M.weight by omega]
    using hcut

/-- The detected basis sheet is not in the immediate principal-cut image. -/
theorem minimalGhost_basis_not_mem_principalCutImage
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    (hpos : 0 < M.weight) :
    (classicalHodgeBasis V H M.weight M.sheet).1 ∉
      principalCutHodgeImage G (M.weight - 1) := by
  intro hmem
  have hzero := minimalGhost_principalCutImage_le_ker G M hpos hmem
  exact M.separator.detects_basis hzero

/-- Positive-weight one-step primitive cokernel. -/
abbrev PrincipalCutPrimitiveCokernel
    (G : GeometricCycleClassSpine V H)
    (q : Nat) :=
  RationalSingularCohomology H.analytification (2 * (q + 1)) ⧸
    principalCutHodgeImage G q

/-- The minimal detected basis sheet survives nontrivially in the immediate
principal-cut cokernel. -/
noncomputable def minimalCutPrimitiveClass
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    (hpos : 0 < M.weight) :
    PrincipalCutPrimitiveCokernel G (M.weight - 1) :=
  Submodule.Quotient.mk
    (show RationalSingularCohomology H.analytification
        (2 * ((M.weight - 1) + 1)) from
      (by simpa [show M.weight - 1 + 1 = M.weight by omega] using
        (classicalHodgeBasis V H M.weight M.sheet).1))

/-- The one-step primitive class is nonzero. -/
theorem minimalCutPrimitiveClass_ne_zero
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    (hpos : 0 < M.weight) :
    minimalCutPrimitiveClass G M hpos ≠ 0 := by
  intro hz
  apply minimalGhost_basis_not_mem_principalCutImage G M hpos
  exact (Submodule.Quotient.mk_eq_zero
    (principalCutHodgeImage G (M.weight - 1))).mp hz

/-- The minimal separator descends canonically through the immediate cut
cokernel. -/
noncomputable def minimalCutPrimitiveDetector
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    (hpos : 0 < M.weight) :
    PrincipalCutPrimitiveCokernel G (M.weight - 1) →ₗ[ℚ] ℚ :=
  (principalCutHodgeImage G (M.weight - 1)).liftQ M.separator.detector
    (minimalGhost_principalCutImage_le_ker G M hpos)

/-- The descended cut-primitive detector remains nonzero on the detected
primitive class. -/
theorem minimalCutPrimitive_pairing_nonzero
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    (hpos : 0 < M.weight) :
    minimalCutPrimitiveDetector G M hpos
      (minimalCutPrimitiveClass G M hpos) ≠ 0 := by
  simpa [minimalCutPrimitiveDetector, minimalCutPrimitiveClass]
    using M.separator.detects_basis

/-- **ONE-STEP PRIMITIVE CROWN.**  Every positive-weight minimal failure is
already a nonzero primal/dual obstruction in the cokernel of the immediately
preceding genuine principal-cut map. -/
theorem minimal_cut_primitive_cokernel_crown
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    (hpos : 0 < M.weight) :
    minimalCutPrimitiveClass G M hpos ≠ 0
      ∧ minimalCutPrimitiveDetector G M hpos
          (minimalCutPrimitiveClass G M hpos) ≠ 0 := by
  exact ⟨minimalCutPrimitiveClass_ne_zero G M hpos,
    minimalCutPrimitive_pairing_nonzero G M hpos⟩

#check principalCutOnHodge
#check principalCutHodgeImage
#check principalCutHodgeImage_le_lowerGeometricImage
#check minimalGhost_principalCutImage_le_ker
#check minimalGhost_basis_not_mem_principalCutImage
#check PrincipalCutPrimitiveCokernel
#check minimalCutPrimitiveClass
#check minimalCutPrimitiveDetector
#check minimal_cut_primitive_cokernel_crown

#print axioms minimalGhost_principalCutImage_le_ker
#print axioms minimalGhost_basis_not_mem_principalCutImage
#print axioms minimal_cut_primitive_cokernel_crown

end GSTClassicalHodgeMinimalCutPrimitiveCokernel
