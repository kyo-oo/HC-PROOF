import GSTClassicalHodgeNativeOperatorCohomologyRealization
import GSTClassicalHodgeProjectiveCorrespondenceAlgebra

/-!
# GST CLASSICAL HODGE — KERNEL-STABLE NATIVE OPERATOR ALGEBRA

The cohomological realization of a native cycle operator only requires one
well-definedness law: preservation of the kernel of cycle class.  This law is
closed under the complete operator algebra used by the limitless cosmology.

Consequently kernel stability never needs to be reproved for a polynomial,
projector, Lefschetz iterate, or finite rational combination.  It is enough to
establish it on primitive native geometric generators; all generated
operators inherit a canonical ambient cohomological realization.
-/

set_option maxHeartbeats 20000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeProjectiveCorrespondenceAlgebra
open GSTClassicalHodgeNativeOperatorCohomologyRealization

namespace GSTClassicalHodgeKernelStableOperatorAlgebra

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

abbrev NativeEnd :=
  codimensionCycles V.X p →ₗ[ℚ] codimensionCycles V.X p

/-- The zero native operator is kernel-stable. -/
theorem zero_kernelStable :
    KernelStable (H := H) (0 : NativeEnd V p) := by
  intro Z hZ
  simp

/-- The identity native operator is kernel-stable. -/
theorem id_kernelStable :
    KernelStable (H := H) (LinearMap.id : NativeEnd V p) := by
  intro Z hZ
  simpa using hZ

/-- Kernel stability is preserved by addition. -/
theorem add_kernelStable
    {A B : NativeEnd V p}
    (hA : KernelStable (H := H) A)
    (hB : KernelStable (H := H) B) :
    KernelStable (H := H) (A + B) := by
  intro Z hZ
  simp [hA Z hZ, hB Z hZ]

/-- Kernel stability is preserved by negation. -/
theorem neg_kernelStable
    {A : NativeEnd V p}
    (hA : KernelStable (H := H) A) :
    KernelStable (H := H) (-A) := by
  intro Z hZ
  simp [hA Z hZ]

/-- Kernel stability is preserved by subtraction. -/
theorem sub_kernelStable
    {A B : NativeEnd V p}
    (hA : KernelStable (H := H) A)
    (hB : KernelStable (H := H) B) :
    KernelStable (H := H) (A - B) :=
  add_kernelStable hA (neg_kernelStable hB)

/-- Kernel stability is preserved by rational scaling. -/
theorem smul_kernelStable
    (q : ℚ) {A : NativeEnd V p}
    (hA : KernelStable (H := H) A) :
    KernelStable (H := H) (q • A) := by
  intro Z hZ
  simp [hA Z hZ]

/-- Kernel stability is preserved by composition. -/
theorem comp_kernelStable
    {A B : NativeEnd V p}
    (hA : KernelStable (H := H) A)
    (hB : KernelStable (H := H) B) :
    KernelStable (H := H) (A.comp B) := by
  intro Z hZ
  exact hA (B Z) (hB Z hZ)

/-- Every iterate of a kernel-stable native operator is kernel-stable. -/
theorem pow_kernelStable
    {A : NativeEnd V p}
    (hA : KernelStable (H := H) A) :
    ∀ n : Nat, KernelStable (H := H) (A ^ n)
  | 0 => by simpa using (id_kernelStable (V := V) (H := H) (p := p))
  | n + 1 => by
      simpa [pow_succ] using
        comp_kernelStable hA (pow_kernelStable hA n)

/-- Finite sums of kernel-stable native operators are kernel-stable. -/
theorem finset_sum_kernelStable
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι)
    (A : ι → NativeEnd V p)
    (hA : ∀ i ∈ s, KernelStable (H := H) (A i)) :
    KernelStable (H := H) (∑ i ∈ s, A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero_kernelStable (V := V) (H := H) (p := p))
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact add_kernelStable (hA a (by simp))
        (ih (fun i hi => hA i (by simp [hi])))

/-- Kernel-stable native endomorphisms form a rational submodule of the full
native operator space. -/
noncomputable def kernelStableSubmodule :
    Submodule ℚ (NativeEnd V p) where
  carrier := {A | KernelStable (H := H) A}
  zero_mem' := zero_kernelStable
  add_mem' := fun hA hB => add_kernelStable hA hB
  smul_mem' := fun q A hA => smul_kernelStable q hA

/-- If every actual scheme-endomorphism generator preserves the cycle-class
kernel, then the entire rational projective-correspondence span does. -/
theorem projectiveCorrespondence_kernelStable
    (hgeom : ∀ f : V.X ⟶ V.X,
      KernelStable (H := H) (geometricGenerator V p f)) :
    ∀ A : NativeEnd V p,
      A ∈ projectiveCorrespondenceSpan V p →
        KernelStable (H := H) A := by
  intro A hA
  have hsubset : geometricGeneratorSet V p ⊆
      (kernelStableSubmodule (V := V) (H := H) (p := p) : Set (NativeEnd V p)) := by
    rintro T ⟨f, rfl⟩
    exact hgeom f
  exact (Submodule.span_le.mpr hsubset) hA

/-- Every kernel-stable projective-correspondence operator acquires the
canonical ambient cohomological action constructed in the previous module. -/
noncomputable def projectiveCorrespondenceOperatorPair
    (K : ProjectiveNativeKernel V p)
    (hgeom : ∀ f : V.X ⟶ V.X,
      KernelStable (H := H) (geometricGenerator V p f)) :=
  projectiveKernelToOperatorPair K
    (projectiveCorrespondence_kernelStable hgeom K.1 K.2)

#check zero_kernelStable
#check id_kernelStable
#check add_kernelStable
#check smul_kernelStable
#check comp_kernelStable
#check pow_kernelStable
#check finset_sum_kernelStable
#check kernelStableSubmodule
#check projectiveCorrespondence_kernelStable
#check projectiveCorrespondenceOperatorPair

#print axioms projectiveCorrespondence_kernelStable
#print axioms projectiveCorrespondenceOperatorPair

end GSTClassicalHodgeKernelStableOperatorAlgebra
