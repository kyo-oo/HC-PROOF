import Mathlib.Algebra.Module.Projective
import GSTClassicalHodgeNativeArsenalRepresentation
import GSTClassicalHodgeProjectiveCorrespondenceAlgebra

/-!
# GST CLASSICAL HODGE — NATIVE OPERATOR COHOMOLOGY REALIZATION

A native algebraic-cycle operator should not require an independently supplied
cohomological operator.  The only well-definedness condition is that it
preserve the kernel of the cycle-class map.  Under that condition it descends
to the quotient represented by the actual cycle-class range.  Since rational
vector spaces are projective/injective enough for linear extension, the range
operator extends to ambient rational singular cohomology.

This module therefore turns a native projective-correspondence operator plus
kernel preservation into a complete `CycleClassOperatorPair` automatically.
The cycle-class commuting square is proved, not stored as unrelated data.
-/

set_option maxHeartbeats 20000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeCycleOperatorNaturality
open GSTClassicalHodgeProjectiveCorrespondenceAlgebra

namespace GSTClassicalHodgeNativeOperatorCohomologyRealization

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

abbrev Cycles := codimensionCycles V.X p
abbrev Coh := RationalSingularCohomology H.analytification (2 * p)

/-- A native cycle operator respects cycle-class equivalence precisely when it
maps the kernel of cycle class into itself. -/
def KernelStable
    (A : Cycles V p →ₗ[ℚ] Cycles V p) : Prop :=
  ∀ Z : Cycles V p,
    H.cycleClass p Z = 0 → H.cycleClass p (A Z) = 0

/-- Kernel stability says equal cycle classes have equal transformed cycle
classes. -/
theorem class_congr_of_kernelStable
    (A : Cycles V p →ₗ[ℚ] Cycles V p)
    (hA : KernelStable (H := H) A)
    {Z W : Cycles V p}
    (hZW : H.cycleClass p Z = H.cycleClass p W) :
    H.cycleClass p (A Z) = H.cycleClass p (A W) := by
  have hker : H.cycleClass p (Z - W) = 0 := by
    simp [hZW]
  have himage := hA (Z - W) hker
  simpa using himage

/-- Canonical chosen representative of a class in the actual cycle-class
range. -/
noncomputable def rangeRepresentative
    (x : LinearMap.range (H.cycleClass p)) : Cycles V p :=
  Classical.choose x.2

@[simp]
theorem rangeRepresentative_spec
    (x : LinearMap.range (H.cycleClass p)) :
    H.cycleClass p (rangeRepresentative x) = x.1 :=
  Classical.choose_spec x.2

/-- Native operator descended to the actual cycle-class range. -/
noncomputable def rangeOperator
    (A : Cycles V p →ₗ[ℚ] Cycles V p)
    (hA : KernelStable (H := H) A) :
    LinearMap.range (H.cycleClass p) →ₗ[ℚ]
      LinearMap.range (H.cycleClass p) where
  toFun := fun x => ⟨H.cycleClass p (A (rangeRepresentative x)),
    ⟨A (rangeRepresentative x), rfl⟩⟩
  map_add' := by
    intro x y
    apply Subtype.ext
    have hrep :
        H.cycleClass p (rangeRepresentative (x + y)) =
          H.cycleClass p (rangeRepresentative x + rangeRepresentative y) := by
      simp [rangeRepresentative_spec]
    rw [class_congr_of_kernelStable A hA hrep]
    simp
  map_smul' := by
    intro q x
    apply Subtype.ext
    have hrep :
        H.cycleClass p (rangeRepresentative (q • x)) =
          H.cycleClass p (q • rangeRepresentative x) := by
      simp [rangeRepresentative_spec]
    rw [class_congr_of_kernelStable A hA hrep]
    simp

/-- The descended range operator has the expected action on every actual
cycle class. -/
theorem rangeOperator_rangeRestrict
    (A : Cycles V p →ₗ[ℚ] Cycles V p)
    (hA : KernelStable (H := H) A)
    (Z : Cycles V p) :
    (rangeOperator A hA) ((H.cycleClass p).rangeRestrict Z) =
      (H.cycleClass p).rangeRestrict (A Z) := by
  apply Subtype.ext
  apply class_congr_of_kernelStable A hA
  exact rangeRepresentative_spec _

/-- Include the range operator back into ambient cohomology. -/
noncomputable def rangeOperatorIntoAmbient
    (A : Cycles V p →ₗ[ℚ] Cycles V p)
    (hA : KernelStable (H := H) A) :
    LinearMap.range (H.cycleClass p) →ₗ[ℚ] Coh H p :=
  (LinearMap.range (H.cycleClass p)).subtype.comp (rangeOperator A hA)

/-- Extend the descended native action from the actual cycle-class range to
all ambient rational singular cohomology. -/
noncomputable def ambientOperator
    (A : Cycles V p →ₗ[ℚ] Cycles V p)
    (hA : KernelStable (H := H) A) :
    Coh H p →ₗ[ℚ] Coh H p :=
  Classical.choose (LinearMap.exists_extend (rangeOperatorIntoAmbient A hA))

/-- The ambient extension agrees with the descended operator on the actual
cycle-class range. -/
theorem ambientOperator_comp_rangeSubtype
    (A : Cycles V p →ₗ[ℚ] Cycles V p)
    (hA : KernelStable (H := H) A) :
    (ambientOperator A hA).comp
        (LinearMap.range (H.cycleClass p)).subtype =
      rangeOperatorIntoAmbient A hA :=
  Classical.choose_spec (LinearMap.exists_extend (rangeOperatorIntoAmbient A hA))

/-- **AUTOMATIC CYCLE-CLASS NATURALITY.**  The ambient operator manufactured
from a kernel-stable native operator has the exact commuting square. -/
theorem cycleClass_ambientOperator
    (A : Cycles V p →ₗ[ℚ] Cycles V p)
    (hA : KernelStable (H := H) A)
    (Z : Cycles V p) :
    ambientOperator A hA (H.cycleClass p Z) =
      H.cycleClass p (A Z) := by
  have hcomp := LinearMap.congr_fun (ambientOperator_comp_rangeSubtype A hA)
    ((H.cycleClass p).rangeRestrict Z)
  have hrange := rangeOperator_rangeRestrict A hA Z
  simpa [rangeOperatorIntoAmbient, hrange] using hcomp

/-- Every kernel-stable native operator canonically gives a complete
cycle/cohomology operator pair. -/
noncomputable def toCycleClassOperatorPair
    (A : Cycles V p →ₗ[ℚ] Cycles V p)
    (hA : KernelStable (H := H) A) :
    CycleClassOperatorPair V H p where
  cycleOperator := A
  cohomologyOperator := ambientOperator A hA
  cycleClass_natural := by
    ext Z
    symm
    exact cycleClass_ambientOperator A hA Z

/-- Kernel-stable actual projective-correspondence operators therefore acquire
a canonical ambient cohomological realization. -/
noncomputable def projectiveKernelToOperatorPair
    (K : ProjectiveNativeKernel V p)
    (hK : KernelStable (H := H) K.operator) :
    CycleClassOperatorPair V H p :=
  toCycleClassOperatorPair K.operator hK

#check KernelStable
#check class_congr_of_kernelStable
#check rangeOperator
#check ambientOperator
#check cycleClass_ambientOperator
#check toCycleClassOperatorPair
#check projectiveKernelToOperatorPair

#print axioms class_congr_of_kernelStable
#print axioms rangeOperator_rangeRestrict
#print axioms cycleClass_ambientOperator
#print axioms toCycleClassOperatorPair
#print axioms projectiveKernelToOperatorPair

end GSTClassicalHodgeNativeOperatorCohomologyRealization
