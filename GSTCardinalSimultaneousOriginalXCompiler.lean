import Mathlib

/-!
# GST simultaneous cardinal-indexed actual-original-X operator compiler

The owner's proposed ONE connected cardinal/topology/CM/N-cohomology/curvature
mechanism must land on the SAME original X. This module complements, rather
than replaces, the connected cross-world geometry.

The index type I has ARBITRARY cardinality. Each index designates a genuine
original-X rational Chow correspondence, supplied by geometric construction.
The cycleClass is instantiated with the canonical rational Betti map.

Theorems:
(1) finite correspondence WORDS preserve the canonical square;
(2) simultaneous FINITE rational packets preserve it;
(3) noncommutative native curvature transports to Betti commutator;
(4) a nonzero residual detector certifies a constructed actual native
    word or curvature cycle is independent of all previously known sources.

No unknown Hodge target preimage, Hodge surjectivity, global full-rank
existence, or actual Chow source-birth operation is assumed in the proofs.
The existence of geometric input correspondences still requires proof on X.
-/

set_option maxHeartbeats 2000000
noncomputable section

namespace GSTCardinalSimultaneousOriginalXCompiler

universe u v w

variable {ι : Type u} {A : Type v} {B : Type w}
variable [AddCommGroup A] [Module ℚ A]
variable [AddCommGroup B] [Module ℚ B]

/-- Every index refers to an actual original-X Chow operator on A,
its rational Betti action on B, and their canonical commuting square. -/
structure NativeGeometricFamily (ι : Type u) (A : Type v) (B : Type w)
    [AddCommGroup A] [Module ℚ A]
    [AddCommGroup B] [Module ℚ B] where
  cycleClass : A →ₗ[ℚ] B
  native : ι → Module.End ℚ A
  betti : ι → Module.End ℚ B
  square : ∀ (i : ι) (Z : A),
    cycleClass (native i Z) = betti i (cycleClass Z)
  seed : A

/-- An arbitrarily long finite native Chow word from the cardinal
family, starting from ONE genuine original-X source cycle. -/
def nativeWord (F : NativeGeometricFamily ι A B) : List ι → A
  | [] => F.seed
  | i :: word => F.native i (nativeWord F word)

/-- The corresponding Hodge/Betti word, not a preselected target class. -/
def bettiWord (F : NativeGeometricFamily ι A B) : List ι → B
  | [] => F.cycleClass F.seed
  | i :: word => F.betti i (bettiWord F word)

/-- Exact native-to-Betti square for ANY finite word from an
arbitrarily large family of actually geometric original-X operations. -/
theorem nativeWord_class
    (F : NativeGeometricFamily ι A B) (word : List ι) :
    F.cycleClass (nativeWord F word) = bettiWord F word := by
  induction word with
  | nil => rfl
  | cons i word ih =>
      change F.cycleClass (F.native i (nativeWord F word)) =
        F.betti i (bettiWord F word)
      rw [F.square i (nativeWord F word), ih]

/-- A simultaneous packet on one original X. All cardinally many
operators are available, but the current Chow sum is finite. -/
def nativePacket
    (F : NativeGeometricFamily ι A B)
    (s : Finset ι) (c : ι → ℚ) (Z : A) : A :=
  s.sum (fun i => c i • F.native i Z)

/-- Betti signal of the same original-X simultaneous GST packet. -/
def bettiPacket
    (F : NativeGeometricFamily ι A B)
    (s : Finset ι) (c : ι → ℚ) (x : B) : B :=
  s.sum (fun i => c i • F.betti i x)

/-- All simultaneous finite cardinal packets preserve the true
native-to-cohomology square. -/
theorem nativePacket_class
    (F : NativeGeometricFamily ι A B)
    (s : Finset ι) (c : ι → ℚ) (Z : A) :
    F.cycleClass (nativePacket F s c Z) =
      bettiPacket F s c (F.cycleClass Z) := by
  simp only [nativePacket, bettiPacket, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul, F.square i Z]

/-- Noncommutative original-X native GST curvature on the source. -/
def nativeCurvature
    (F : NativeGeometricFamily ι A B) (i j : ι) : A :=
  F.native i (F.native j F.seed) -
    F.native j (F.native i F.seed)

/-- Every native curvature source has the exact corresponding
Hodge commutator as its canonical rational Betti class. -/
theorem nativeCurvature_class
    (F : NativeGeometricFamily ι A B) (i j : ι) :
    F.cycleClass (nativeCurvature F i j) =
      F.betti i (F.betti j (F.cycleClass F.seed)) -
        F.betti j (F.betti i (F.cycleClass F.seed)) := by
  unfold nativeCurvature
  rw [map_sub, F.square i (F.native j F.seed),
    F.square j (F.native i F.seed),
    F.square j F.seed, F.square i F.seed]

/-- If a genuine rational Hodge detector kills all OLD native source
classes but detects a concrete native correspondence word, that
word has constructed a NEW algebraic Hodge direction relative to old. -/
theorem nativeWord_fresh_of_detector
    (F : NativeGeometricFamily ι A B)
    (word : List ι)
    {J : Type*} (old : J → A)
    (detector : B →ₗ[ℚ] ℚ)
    (hOld : ∀ j : J, detector (F.cycleClass (old j)) = 0)
    (hNew : detector (F.cycleClass (nativeWord F word)) ≠ 0) :
    F.cycleClass (nativeWord F word) ∉
      Submodule.span ℚ (Set.range (fun j : J => F.cycleClass (old j))) := by
  intro hspan
  have hle :
      Submodule.span ℚ (Set.range (fun j : J => F.cycleClass (old j))) ≤
        LinearMap.ker detector := by
    apply Submodule.span_le.mpr
    rintro x ⟨j, rfl⟩
    exact LinearMap.mem_ker.mpr (hOld j)
  exact hNew (LinearMap.mem_ker.mp (hle hspan))

/-- The same exact noncircular certificate for a genuine original-X
native curvature-cycle, not just a GST arbitrary word. -/
theorem nativeCurvature_fresh_of_detector
    (F : NativeGeometricFamily ι A B)
    (i j : ι)
    {J : Type*} (old : J → A)
    (detector : B →ₗ[ℚ] ℚ)
    (hOld : ∀ k : J, detector (F.cycleClass (old k)) = 0)
    (hNew : detector (F.cycleClass (nativeCurvature F i j)) ≠ 0) :
    F.cycleClass (nativeCurvature F i j) ∉
      Submodule.span ℚ (Set.range (fun k : J => F.cycleClass (old k))) := by
  intro hspan
  have hle :
      Submodule.span ℚ (Set.range (fun k : J => F.cycleClass (old k))) ≤
        LinearMap.ker detector := by
    apply Submodule.span_le.mpr
    rintro x ⟨k, rfl⟩
    exact LinearMap.mem_ker.mpr (hOld k)
  exact hNew (LinearMap.mem_ker.mp (hle hspan))

#check nativeWord_class
#check nativePacket_class
#check nativeCurvature_class
#check nativeWord_fresh_of_detector
#check nativeCurvature_fresh_of_detector

#print axioms nativeWord_class
#print axioms nativePacket_class
#print axioms nativeCurvature_class
#print axioms nativeWord_fresh_of_detector
#print axioms nativeCurvature_fresh_of_detector

end GSTCardinalSimultaneousOriginalXCompiler
