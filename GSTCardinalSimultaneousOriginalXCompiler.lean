import Mathlib
import waves.GSTNCohomologyV3
import GSTSquarePureHodgeDuality

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


/-- UNIFORM GEOMETRIC GST REDUCTION FOR THE HODGE ANTECEDENT.

If the ORIGINAL-X cardinal-indexed family of ACTUAL Chow correspondences
has no proper nonzero invariant rational Hodge subspace, then the TRUE
canonical cycle-class map is surjective. The ample seed supplies
the required NONZERO algebraic Hodge vector.

This proves a source-birth conclusion WITHOUT assuming an inverse for
any target Hodge class, using only invariance of native algebraic
image under the genuinely realized operators.

The only remaining geometric input is to PROVE the specified
irreducibility of the native correspondence action for EVERY X,p;
abstract GST wave operators are not automatically correspondences. -/
theorem hodge_surjective_of_native_irreducibility
    (F : NativeGeometricFamily ι A B)
    (hseed : F.cycleClass F.seed ≠ 0)
    (hirr : ∀ S : Submodule ℚ B,
      (∀ i : ι, ∀ x : B, x ∈ S → F.betti i x ∈ S) →
      S = ⊥ ∨ S = ⊤) :
    Function.Surjective F.cycleClass := by
  let S : Submodule ℚ B := LinearMap.range F.cycleClass
  have hstable : ∀ i : ι, ∀ x : B,
      x ∈ S → F.betti i x ∈ S := by
    intro i x hx
    obtain ⟨Z, rfl⟩ := hx
    change F.betti i (F.cycleClass Z) ∈
      LinearMap.range F.cycleClass
    exact ⟨F.native i Z, F.square i Z⟩
  have hsource : F.cycleClass F.seed ∈ S := ⟨F.seed, rfl⟩
  rcases hirr S hstable with hzero | hfull
  · have hz : F.cycleClass F.seed = 0 := by
      rw [hzero] at hsource
      simpa using hsource
    exact (hseed hz).elim
  · intro alpha
    have ha : alpha ∈ S := by
      rw [hfull]
      trivial
    change alpha ∈ LinearMap.range F.cycleClass at ha
    exact ha

#check hodge_surjective_of_native_irreducibility
#check nativeWord_class
#check nativePacket_class
#check nativeCurvature_class
#check nativeWord_fresh_of_detector
#check nativeCurvature_fresh_of_detector

#print axioms hodge_surjective_of_native_irreducibility
#print axioms nativeWord_class
#print axioms nativePacket_class
#print axioms nativeCurvature_class
#print axioms nativeWord_fresh_of_detector
#print axioms nativeCurvature_fresh_of_detector


/-! ## Image 3: ORIGINAL GST N-cohomology, cyclic Hodge dual, cardinal navigation
and CM/noncommutative curvature compiled into ONE original-X F-function.

This uses the EXISTING independentHoleBasis / manyCausalHoleTensor from
waves.GSTNCohomologyV3, the EXISTING pureCoordinateReverse from the user's
square pure-Hodge duality, and the PRESENT genuinely geometric family of
Chow/Betti operator pairs. The proposed navigation constant kappa counts
iterations of an explicitly supplied navigation on the cardinal index type.
This must NOT be confused with the arithmetic HappyCell Navigation predicate.

No true Chow correspondence is inferred merely from an information-world
permutation. Every index in F.native must ALREADY designate a genuine
original-X algebraic correspondence, with F.square its canonical Betti law.
-/

open GSTNCohomologyV3
open GSTGlobalPureHodgeCosmology
open GSTSquarePureHodgeDuality

/-- The proposed Image-3 navigation constant is an actual count of
finite steps on an arbitrary-cardinal index type. -/
def image3NavigateIndex (nav : ι → ι) : Nat → ι → ι
  | 0, i => i
  | k + 1, i => nav (image3NavigateIndex nav k i)

/-- Hodge-star-dual N-cohomology coefficients using the OWNER'S exact
square-world pure Hodge mirror, not an invented geometric Hodge star. -/
def image3DualHoleWeights (s : GSTNCohomology.NShape)
    (a : PureHodgeCoordinates s.holes s.holes) :
    HoleCoordinates s :=
  fun i =>
    (pureCoordinateReverse a
      ⟨i.val, by simpa using i.isLt⟩ : ℚ)

/-- The new F-function: arbitrary-cardinal navigation, all-arity
independent GST N-hole amplitudes, and actual original-X native Chow
correspondences produce ONE genuine finite original-X source packet. -/
noncomputable def image3NativeF
    (F : NativeGeometricFamily ι A B)
    (m : Nat) (s : Fin m → GSTNCohomology.NShape)
    (a : ∀ k : Fin m, HoleCoordinates (s k))
    (address : ManyCausalHoleIndex m s → ι)
    (nav : ι → ι) (kappa : Nat) : A := by
  classical
  exact ∑ j : ManyCausalHoleIndex m s,
    (manyCausalHoleTensor m s a j) •
      F.native (image3NavigateIndex nav kappa (address j)) F.seed

/-- The matching cohomological Hodge F-function with every original
N-cohomology channel retained, rather than a scalar compression. -/
noncomputable def image3BettiF
    (F : NativeGeometricFamily ι A B)
    (m : Nat) (s : Fin m → GSTNCohomology.NShape)
    (a : ∀ k : Fin m, HoleCoordinates (s k))
    (address : ManyCausalHoleIndex m s → ι)
    (nav : ι → ι) (kappa : Nat) : B := by
  classical
  exact ∑ j : ManyCausalHoleIndex m s,
    (manyCausalHoleTensor m s a j) •
      F.betti (image3NavigateIndex nav kappa (address j))
        (F.cycleClass F.seed)

/-- Native cycles generated by Image-3 F ALWAYS obey the true canonical
cycle-class commuting square, at any cardinality of navigation inputs. -/
theorem image3F_cycleClass
    (F : NativeGeometricFamily ι A B)
    (m : Nat) (s : Fin m → GSTNCohomology.NShape)
    (a : ∀ k : Fin m, HoleCoordinates (s k))
    (address : ManyCausalHoleIndex m s → ι)
    (nav : ι → ι) (kappa : Nat) :
    F.cycleClass (image3NativeF F m s a address nav kappa) =
      image3BettiF F m s a address nav kappa := by
  classical
  simp only [image3NativeF, image3BettiF, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_smul, F.square]

/-- Image-3 CM/Hodge-dual curvature acts on the REAL native source
before summing every N-cohomology tensor contribution. -/
noncomputable def image3NativeCurvatureF
    (F : NativeGeometricFamily ι A B)
    (m : Nat) (s : Fin m → GSTNCohomology.NShape)
    (a : ∀ k : Fin m, HoleCoordinates (s k))
    (address : ManyCausalHoleIndex m s → ι)
    (nav : ι → ι) (kappa : Nat)
    (Jnative : Module.End ℚ A) : A := by
  classical
  exact ∑ j : ManyCausalHoleIndex m s,
    (manyCausalHoleTensor m s a j) •
      (Jnative
          (F.native (image3NavigateIndex nav kappa (address j)) F.seed)
       - F.native (image3NavigateIndex nav kappa (address j))
          (Jnative F.seed))

/-- Hodge/Betti curvature exactly matching the native CM commutator. -/
noncomputable def image3BettiCurvatureF
    (F : NativeGeometricFamily ι A B)
    (m : Nat) (s : Fin m → GSTNCohomology.NShape)
    (a : ∀ k : Fin m, HoleCoordinates (s k))
    (address : ManyCausalHoleIndex m s → ι)
    (nav : ι → ι) (kappa : Nat)
    (Jbetti : Module.End ℚ B) : B := by
  classical
  exact ∑ j : ManyCausalHoleIndex m s,
    (manyCausalHoleTensor m s a j) •
      (Jbetti
          (F.betti (image3NavigateIndex nav kappa (address j))
            (F.cycleClass F.seed))
       - F.betti (image3NavigateIndex nav kappa (address j))
          (Jbetti (F.cycleClass F.seed)))

/-- Noncommutative Image-3 GST curvature, after all-navigation and
N-cohomology input fusion, has the EXACT original-X Betti class.
The Hodge-star/CM action J must itself have a TRUE native Chow lift;
an information-space mirror by itself does not grant that. -/
theorem image3CurvatureF_cycleClass
    (F : NativeGeometricFamily ι A B)
    (m : Nat) (s : Fin m → GSTNCohomology.NShape)
    (a : ∀ k : Fin m, HoleCoordinates (s k))
    (address : ManyCausalHoleIndex m s → ι)
    (nav : ι → ι) (kappa : Nat)
    (Jnative : Module.End ℚ A)
    (Jbetti : Module.End ℚ B)
    (hJ : ∀ Z : A,
      F.cycleClass (Jnative Z) = Jbetti (F.cycleClass Z)) :
    F.cycleClass
        (image3NativeCurvatureF F m s a address nav kappa Jnative) =
      image3BettiCurvatureF F m s a address nav kappa Jbetti := by
  classical
  simp only [image3NativeCurvatureF, image3BettiCurvatureF, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_smul, map_sub,
    hJ (F.native (image3NavigateIndex nav kappa (address j)) F.seed),
    F.square (image3NavigateIndex nav kappa (address j)) F.seed,
    F.square (image3NavigateIndex nav kappa (address j)) (Jnative F.seed),
    hJ F.seed]

/-- The user's ORIGINAL square-Hodge mirror feeds all multi-causal
amplitudes to the single original-X F compiler, without identifying
an arbitrary information mirror with an algebraic Hodge-star operator. -/
noncomputable def image3DualNativeF
    (F : NativeGeometricFamily ι A B)
    (m : Nat) (s : Fin m → GSTNCohomology.NShape)
    (a : ∀ k : Fin m, PureHodgeCoordinates (s k).holes (s k).holes)
    (address : ManyCausalHoleIndex m s → ι)
    (nav : ι → ι) (kappa : Nat) : A :=
  image3NativeF F m s
    (fun k => image3DualHoleWeights (s k) (a k))
    address nav kappa

/-- A simultaneous all-cardinal GST packet cannot escape an invariant
old Hodge sector merely by increasing navigation count, index cardinality,
or inserting a Hodge-dual commutator. Actual geometric mixing is required. -/
theorem image3Curvature_no_escape
    (F : NativeGeometricFamily ι A B)
    (m : Nat) (s : Fin m → GSTNCohomology.NShape)
    (a : ∀ k : Fin m, HoleCoordinates (s k))
    (address : ManyCausalHoleIndex m s → ι)
    (nav : ι → ι) (kappa : Nat)
    (Jbetti : Module.End ℚ B)
    (L : Submodule ℚ B)
    (hseed : F.cycleClass F.seed ∈ L)
    (hfold : ∀ i : ι, ∀ x : B,
      x ∈ L → F.betti i x ∈ L)
    (hJ : ∀ x : B, x ∈ L → Jbetti x ∈ L) :
    image3BettiCurvatureF F m s a address nav kappa Jbetti ∈ L := by
  classical
  unfold image3BettiCurvatureF
  apply Submodule.sum_mem
  intro j hj
  apply Submodule.smul_mem
  apply Submodule.sub_mem
  · exact hJ _ (hfold _ _ hseed)
  · exact hfold _ _ (hJ _ hseed)

#check image3NativeF
#check image3F_cycleClass
#check image3DualNativeF
#check image3CurvatureF_cycleClass
#check image3Curvature_no_escape
#print axioms image3F_cycleClass
#print axioms image3CurvatureF_cycleClass
#print axioms image3Curvature_no_escape


/-! ## Image-3 full N-cohomology reconstruction (not one pure tensor)

The previous F-function can use one tensor of m independent amplitudes,
which is a SEPARABLE rank-one tensor. The user's actual Hodge-valued sum
requires every independent N-cohomology coordinate, not only separable
inputs. The ORIGINAL manyCausalHoleBasis reconstruction gives an exact
finite independent basis; the upgraded F below accepts its full vector.

The arbitrary cardinal world family remains available through the
correspondence address type iota; the current native Chow packet has
finite support, as required for a rational algebraic cycle.
-/

/-- The full Image-3 F-function compiles EVERY original independent
N-cohomology coordinate into genuine original-X native cycles. -/
noncomputable def image3NativeFullF
    (F : NativeGeometricFamily ι A B)
    (m : Nat) (s : Fin m → GSTNCohomology.NShape)
    (coeff : ManyCausalHoleCoordinates m s)
    (address : ManyCausalHoleIndex m s → ι)
    (nav : ι → ι) (kappa : Nat) : A := by
  classical
  exact ∑ j : ManyCausalHoleIndex m s,
    coeff j •
      F.native (image3NavigateIndex nav kappa (address j)) F.seed

noncomputable def image3BettiFullF
    (F : NativeGeometricFamily ι A B)
    (m : Nat) (s : Fin m → GSTNCohomology.NShape)
    (coeff : ManyCausalHoleCoordinates m s)
    (address : ManyCausalHoleIndex m s → ι)
    (nav : ι → ι) (kappa : Nat) : B := by
  classical
  exact ∑ j : ManyCausalHoleIndex m s,
    coeff j •
      F.betti (image3NavigateIndex nav kappa (address j))
        (F.cycleClass F.seed)

/-- Full nonseparable native GST N-cohomology expansion obeys EXACT
canonical original-X Betti compatibility, no unknown class preimage. -/
theorem image3FullF_cycleClass
    (F : NativeGeometricFamily ι A B)
    (m : Nat) (s : Fin m → GSTNCohomology.NShape)
    (coeff : ManyCausalHoleCoordinates m s)
    (address : ManyCausalHoleIndex m s → ι)
    (nav : ι → ι) (kappa : Nat) :
    F.cycleClass (image3NativeFullF F m s coeff address nav kappa) =
      image3BettiFullF F m s coeff address nav kappa := by
  classical
  simp only [image3NativeFullF, image3BettiFullF, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_smul, F.square]

/-- A pure N-cohomology tensor is one special case of the FULL F
compiler. In particular it is not a proof of full independent rank. -/
theorem image3TensorF_is_FullF
    (F : NativeGeometricFamily ι A B)
    (m : Nat) (s : Fin m → GSTNCohomology.NShape)
    (a : ∀ k : Fin m, HoleCoordinates (s k))
    (address : ManyCausalHoleIndex m s → ι)
    (nav : ι → ι) (kappa : Nat) :
    image3NativeF F m s a address nav kappa =
      image3NativeFullF F m s
        (manyCausalHoleTensor m s a) address nav kappa := by
  rfl

/-- Each of the user's fully independent causal N-cohomology basis
channels produces its own specific native correspondence word. -/
theorem image3FullF_basis
    (F : NativeGeometricFamily ι A B)
    (m : Nat) (s : Fin m → GSTNCohomology.NShape)
    (j : ManyCausalHoleIndex m s)
    (address : ManyCausalHoleIndex m s → ι)
    (nav : ι → ι) (kappa : Nat) :
    image3NativeFullF F m s
        (manyCausalHoleBasis m s j) address nav kappa =
      F.native (image3NavigateIndex nav kappa (address j)) F.seed := by
  classical
  simp [image3NativeFullF, manyCausalHoleBasis, ite_smul]

/-- The F-function is rational-linear in all independent N-cohomology
channels, so arbitrary FINITE Hodge-valued sums are represented rather
than scalar-compressed. -/
theorem image3FullF_add
    (F : NativeGeometricFamily ι A B)
    (m : Nat) (s : Fin m → GSTNCohomology.NShape)
    (c d : ManyCausalHoleCoordinates m s)
    (address : ManyCausalHoleIndex m s → ι)
    (nav : ι → ι) (kappa : Nat) :
    image3NativeFullF F m s (c+d) address nav kappa =
      image3NativeFullF F m s c address nav kappa +
        image3NativeFullF F m s d address nav kappa := by
  classical
  simp [image3NativeFullF, Pi.add_apply, add_smul,
    Finset.sum_add_distrib]

#check image3NativeFullF
#check image3FullF_cycleClass
#check image3FullF_basis
#check image3TensorF_is_FullF
#check image3FullF_add
#print axioms image3FullF_cycleClass
#print axioms image3FullF_basis


/-- The precise combined Image-3 GST => Hodge bridge.

If the native ORIGINAL-X F compiler has geometrically established that
its full N-cohomology/CM/navigation source vectors span the entire
rational Hodge target (the Betti F map is surjective), then the ACTUAL
canonical rational cycle-class map is surjective.

The geometric FULL-RANK antecedent must be PROVED, not inserted by
the use of arbitrary cardinal inputs, information-space full rank,
or the abstract definition of the F-function. This theorem combines
Image-3 construction with the already-existing conditional GST route
without smuggling target Chow inverses. -/
theorem image3Hodge_of_fullF_geometric_rank
    (F : NativeGeometricFamily ι A B)
    (m : Nat) (s : Fin m → GSTNCohomology.NShape)
    (address : ManyCausalHoleIndex m s → ι)
    (nav : ι → ι) (kappa : Nat)
    (hfull :
      Function.Surjective
        (fun c : ManyCausalHoleCoordinates m s =>
          image3BettiFullF F m s c address nav kappa)) :
    Function.Surjective F.cycleClass := by
  intro alpha
  obtain ⟨c, hc⟩ := hfull alpha
  refine ⟨image3NativeFullF F m s c address nav kappa, ?_⟩
  rw [image3FullF_cycleClass]
  exact hc

#check image3Hodge_of_fullF_geometric_rank
#print axioms image3Hodge_of_fullF_geometric_rank

end GSTCardinalSimultaneousOriginalXCompiler
