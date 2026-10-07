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

abbrev Cycles (V : SmoothProjectiveComplexScheme) (p : Nat) : Type _ :=
  codimensionCycles V.X p
abbrev Coh (H : HodgeBigradedBettiData V) (p : Nat) : Type _ :=
  RationalSingularCohomology H.analytification (2 * p)

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
  rw [map_sub, map_sub] at himage
  exact eq_of_sub_eq_zero himage

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
    have key : H.cycleClass p (A (rangeRepresentative (x + y))) =
        H.cycleClass p (A (rangeRepresentative x)) +
          H.cycleClass p (A (rangeRepresentative y)) := by
      rw [class_congr_of_kernelStable A hA hrep, map_add A, map_add]
    simp only [Submodule.coe_add]
    exact key
  map_smul' := by
    intro q x
    apply Subtype.ext
    have hrep :
        H.cycleClass p (rangeRepresentative (q • x)) =
          H.cycleClass p (q • rangeRepresentative x) := by
      simp [rangeRepresentative_spec]
    have key : H.cycleClass p (A (rangeRepresentative (q • x))) =
        q • H.cycleClass p (A (rangeRepresentative x)) := by
      rw [class_congr_of_kernelStable A hA hrep, map_smul A, map_smul]
    simp only [SetLike.val_smul, RingHom.id_apply]
    exact key

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

/-! ## Coherent descent on the actual range

Choosing an unrelated ambient extension for each operator does not establish
composition on the ambient space.  First descend on the actual range, then
use one fixed range retraction for every operator.  This constructs the exact
composition algebra and identifies all remaining ambient freedom.
-/

theorem rangeOperator_id :
    rangeOperator (LinearMap.id : Module.End ℚ (Cycles V p))
      (fun _ hZ => hZ) = LinearMap.id := by
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  exact rangeRepresentative_spec a

theorem rangeOperator_zero :
    rangeOperator (0 : Module.End ℚ (Cycles V p)) (by intro Z hZ; simp) = 0 := by
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  simp [rangeOperator]

theorem rangeOperator_add
    (A B : Module.End ℚ (Cycles V p))
    (hA : KernelStable (H := H) A) (hB : KernelStable (H := H) B) :
    rangeOperator (A + B) (by intro Z hZ; simp [hA Z hZ, hB Z hZ]) =
      rangeOperator A hA + rangeOperator B hB := by
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  simp [rangeOperator, map_add]

theorem rangeOperator_smul
    (q : ℚ) (A : Module.End ℚ (Cycles V p))
    (hA : KernelStable (H := H) A) :
    rangeOperator (q • A) (by intro Z hZ; simp [hA Z hZ]) =
      q • rangeOperator A hA := by
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  simp [rangeOperator, map_smul]

theorem rangeOperator_comp
    (A B : Module.End ℚ (Cycles V p))
    (hA : KernelStable (H := H) A) (hB : KernelStable (H := H) B) :
    rangeOperator (A.comp B) (fun Z hZ => hA (B Z) (hB Z hZ)) =
      (rangeOperator A hA).comp (rangeOperator B hB) := by
  apply LinearMap.ext
  intro a
  obtain ⟨Z, hZ⟩ := a.2
  have ha : (H.cycleClass p).rangeRestrict Z = a := Subtype.ext hZ
  rw [← ha]
  simp only [LinearMap.comp_apply, rangeOperator_rangeRestrict]

/-- One fixed linear retraction onto the actual class range, used by every
native operator.  It contains no Hodge-surjectivity premise. -/
noncomputable def classRangeRetraction :
    Coh H p →ₗ[ℚ] LinearMap.range (H.cycleClass p) :=
  Classical.choose (LinearMap.exists_extend
    (LinearMap.id : Module.End ℚ (LinearMap.range (H.cycleClass p))))

theorem classRangeRetraction_spec :
    (classRangeRetraction (V := V) (H := H) (p := p)).comp
      (LinearMap.range (H.cycleClass p)).subtype = LinearMap.id :=
  Classical.choose_spec (LinearMap.exists_extend
    (LinearMap.id : Module.End ℚ (LinearMap.range (H.cycleClass p))))

@[simp]
theorem classRangeRetraction_range
    (a : LinearMap.range (H.cycleClass p)) :
    classRangeRetraction (H := H) a.1 = a :=
  LinearMap.congr_fun classRangeRetraction_spec a

/-- Ambient projection onto classes of actual native cycles. -/
noncomputable def classRangeProjection : Module.End ℚ (Coh H p) :=
  (LinearMap.range (H.cycleClass p)).subtype.comp
    (classRangeRetraction (H := H))

@[simp]
theorem classRangeProjection_range
    (a : LinearMap.range (H.cycleClass p)) :
    classRangeProjection (H := H) a.1 = a.1 := by
  simp [classRangeProjection]

theorem classRangeProjection_mem_range (alpha : Coh H p) :
    classRangeProjection (H := H) alpha ∈ LinearMap.range (H.cycleClass p) :=
  (classRangeRetraction (H := H) alpha).2

theorem classRangeProjection_idempotent :
    (classRangeProjection (V := V) (H := H) (p := p)).comp
      (classRangeProjection (H := H)) = classRangeProjection (H := H) := by
  apply LinearMap.ext
  intro alpha
  exact classRangeProjection_range (classRangeRetraction (H := H) alpha)

theorem classRangeProjection_eq_self_iff (alpha : Coh H p) :
    classRangeProjection (H := H) alpha = alpha ↔
      alpha ∈ LinearMap.range (H.cycleClass p) := by
  constructor
  · intro h
    rw [← h]
    exact classRangeProjection_mem_range alpha
  · intro h
    exact classRangeProjection_range ⟨alpha, h⟩

/-- The complement records the ambient extension freedom. -/
noncomputable def offRangeProjection : Module.End ℚ (Coh H p) :=
  LinearMap.id - classRangeProjection (H := H)

@[simp]
theorem offRangeProjection_range
    (a : LinearMap.range (H.cycleClass p)) :
    offRangeProjection (H := H) a.1 = 0 := by
  simp [offRangeProjection]

theorem ambient_range_decomposition (alpha : Coh H p) :
    classRangeProjection (H := H) alpha + offRangeProjection (H := H) alpha =
      alpha := by
  simp only [offRangeProjection, LinearMap.sub_apply, LinearMap.id_apply]
  abel

/-- Composition-coherent ambient action manufactured from native descent.
It is supported on the actual range and kills the chosen complement. -/
noncomputable def supportedAmbientOperator
    (A : Module.End ℚ (Cycles V p)) (hA : KernelStable (H := H) A) :
    Module.End ℚ (Coh H p) :=
  (LinearMap.range (H.cycleClass p)).subtype.comp
    ((rangeOperator A hA).comp (classRangeRetraction (H := H)))

theorem supportedAmbientOperator_mem_range
    (A : Module.End ℚ (Cycles V p)) (hA : KernelStable (H := H) A)
    (alpha : Coh H p) :
    supportedAmbientOperator A hA alpha ∈ LinearMap.range (H.cycleClass p) :=
  (rangeOperator A hA (classRangeRetraction (H := H) alpha)).2

theorem supportedAmbientOperator_cycleClass
    (A : Module.End ℚ (Cycles V p)) (hA : KernelStable (H := H) A)
    (Z : Cycles V p) :
    supportedAmbientOperator A hA (H.cycleClass p Z) =
      H.cycleClass p (A Z) := by
  have hret : classRangeRetraction (H := H) (H.cycleClass p Z) =
      (H.cycleClass p).rangeRestrict Z :=
    classRangeRetraction_range ((H.cycleClass p).rangeRestrict Z)
  simp only [supportedAmbientOperator, LinearMap.comp_apply, hret,
    rangeOperator_rangeRestrict] <;> rfl

theorem supportedAmbientOperator_id :
    supportedAmbientOperator (LinearMap.id : Module.End ℚ (Cycles V p))
      (fun _ hZ => hZ) = classRangeProjection (H := H) := by
  simp [supportedAmbientOperator, rangeOperator_id, classRangeProjection]

theorem supportedAmbientOperator_zero :
    supportedAmbientOperator (0 : Module.End ℚ (Cycles V p))
      (by intro Z hZ; simp) = 0 := by
  apply LinearMap.ext
  intro alpha
  simp [supportedAmbientOperator, rangeOperator_zero]

theorem supportedAmbientOperator_comp
    (A B : Module.End ℚ (Cycles V p))
    (hA : KernelStable (H := H) A) (hB : KernelStable (H := H) B) :
    supportedAmbientOperator (A.comp B) (fun Z hZ => hA (B Z) (hB Z hZ)) =
      (supportedAmbientOperator A hA).comp (supportedAmbientOperator B hB) := by
  apply LinearMap.ext
  intro alpha
  simp only [supportedAmbientOperator, LinearMap.comp_apply,
    classRangeRetraction_range, rangeOperator_comp]

theorem supportedAmbientOperator_add
    (A B : Module.End ℚ (Cycles V p))
    (hA : KernelStable (H := H) A) (hB : KernelStable (H := H) B) :
    supportedAmbientOperator (A + B) (by intro Z hZ; simp [hA Z hZ, hB Z hZ]) =
      supportedAmbientOperator A hA + supportedAmbientOperator B hB := by
  apply LinearMap.ext
  intro alpha
  simp [supportedAmbientOperator, rangeOperator_add, map_add]

theorem supportedAmbientOperator_smul
    (q : ℚ) (A : Module.End ℚ (Cycles V p))
    (hA : KernelStable (H := H) A) :
    supportedAmbientOperator (q • A) (by intro Z hZ; simp [hA Z hZ]) =
      q • supportedAmbientOperator A hA := by
  apply LinearMap.ext
  intro alpha
  simp [supportedAmbientOperator, rangeOperator_smul, map_smul]

/-- **ALL AMBIENT EXTENSIONS, EXACTLY.** The coherent native core is fixed;
every remaining term factors through the chosen off-range projection.  This
also applies to the original independently chosen `ambientOperator`. -/
theorem ambientNatural_core_decomposition
    (A : Module.End ℚ (Cycles V p)) (hA : KernelStable (H := H) A)
    (T : Module.End ℚ (Coh H p))
    (hT : ∀ Z, T (H.cycleClass p Z) = H.cycleClass p (A Z)) :
    T = supportedAmbientOperator A hA + T.comp (offRangeProjection (H := H)) := by
  apply LinearMap.ext
  intro alpha
  have hcore : T (classRangeProjection (H := H) alpha) =
      supportedAmbientOperator A hA alpha := by
    change T (classRangeRetraction (H := H) alpha).1 =
      H.cycleClass p (A (rangeRepresentative (classRangeRetraction (H := H) alpha)))
    rw [← rangeRepresentative_spec (classRangeRetraction (H := H) alpha)]
    exact hT _
  calc
    T alpha = T (classRangeProjection (H := H) alpha +
        offRangeProjection (H := H) alpha) :=
      congrArg T (ambient_range_decomposition alpha).symm
    _ = supportedAmbientOperator A hA alpha +
        T (offRangeProjection (H := H) alpha) := by rw [map_add, hcore]
    _ = _ := rfl

theorem ambientOperator_core_decomposition
    (A : Module.End ℚ (Cycles V p)) (hA : KernelStable (H := H) A) :
    ambientOperator A hA = supportedAmbientOperator A hA +
      (ambientOperator A hA).comp (offRangeProjection (H := H)) :=
  ambientNatural_core_decomposition A hA (ambientOperator A hA)
    (cycleClass_ambientOperator A hA)

#print axioms classRangeRetraction
#print axioms supportedAmbientOperator_comp
#print axioms ambientNatural_core_decomposition

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
