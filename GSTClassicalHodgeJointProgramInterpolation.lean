import GSTClassicalHodgeGradedGeometricOrbitAlgebra

/-!
# Ordered interpolation by genuine geometric programs

Different pairs of directions may be separated by different programs.  The
programs need only act diagonally on the specified finite family; they need
not commute on ambient cohomology.  Ordered products of normalized affine
factors compile coordinate projectors into the existing geometric language.
All conclusions below concern the specified spectral span, not its complement.
-/

noncomputable section

open scoped BigOperators

namespace GSTClassicalHodgeJointProgramInterpolation

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeGradedGeometricProgramOrbit
open GSTClassicalHodgeGradedGeometricOrbitAlgebra

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Pairwise spectral data for actual programs.  Separation is required only
for distinct labels.  No cycle representative of a direction is a field. -/
structure JointProgramSpectrum
    (G : GeometricCycleClassSpine V H) (p : Nat) (ι : Type*) where
  vector : ι → RationalSingularCohomology H.analytification (2 * p)
  probe : ι → ι → GradedGeometricProgram V p p
  eigenvalue : ι → ι → ι → ℚ
  eigenvector : ∀ i j k,
    (probe i j).cohomologyEval G (vector k) =
      eigenvalue i j k • vector k
  separates : ∀ i j, j ≠ i → eigenvalue i j i ≠ eigenvalue i j j

namespace JointProgramSpectrum

variable {G : GeometricCycleClassSpine V H}
variable {ι : Type*} [DecidableEq ι]

/-- A factor preserves the requested direction and kills one competing
direction.  The diagonal case is literally the identity program. -/
def factor (S : JointProgramSpectrum G p ι) (i j : ι) :
    GradedGeometricProgram V p p :=
  if j = i then .id p else
    .smul (S.eigenvalue i j i - S.eigenvalue i j j)⁻¹
      (.add (S.probe i j) (.smul (-S.eigenvalue i j j) (.id p)))

def gain (S : JointProgramSpectrum G p ι) (i j k : ι) : ℚ :=
  if j = i then 1 else
    (S.eigenvalue i j i - S.eigenvalue i j j)⁻¹ *
      (S.eigenvalue i j k - S.eigenvalue i j j)

theorem factor_on_vector (S : JointProgramSpectrum G p ι) (i j k : ι) :
    (S.factor i j).cohomologyEval G (S.vector k) =
      S.gain i j k • S.vector k := by
  by_cases hji : j = i
  · simp only [factor, gain, if_pos hji, one_smul]
    rfl
  · simp only [factor, gain, if_neg hji]
    change
      (S.eigenvalue i j i - S.eigenvalue i j j)⁻¹ •
          ((S.probe i j).cohomologyEval G (S.vector k) +
            (-S.eigenvalue i j j) • S.vector k) = _
    rw [S.eigenvector]
    simp only [sub_eq_add_neg, add_smul, mul_smul]

@[simp]
theorem gain_self (S : JointProgramSpectrum G p ι) (i j : ι) :
    S.gain i j i = 1 := by
  by_cases hji : j = i
  · simp [gain, hji]
  · simp [gain, hji, sub_ne_zero.mpr (S.separates i j hji)]

@[simp]
theorem gain_kills (S : JointProgramSpectrum G p ι) (i j : ι)
    (hji : j ≠ i) : S.gain i j j = 0 := by
  simp [gain, hji]

/-- Ordered composition is essential: no ambient commutativity is assumed. -/
def word (S : JointProgramSpectrum G p ι) (i : ι) :
    List ι → GradedGeometricProgram V p p
  | [] => .id p
  | j :: L => .comp (S.factor i j) (S.word i L)

def response (S : JointProgramSpectrum G p ι) (i : ι) :
    List ι → ι → ℚ
  | [], _ => 1
  | j :: L, k => S.gain i j k * S.response i L k

/-- Exact execution at every prefix, including repeated factors. -/
theorem word_on_vector (S : JointProgramSpectrum G p ι) (i : ι)
    (L : List ι) (k : ι) :
    (S.word i L).cohomologyEval G (S.vector k) =
      S.response i L k • S.vector k := by
  induction L with
  | nil =>
      change S.vector k = (1 : ℚ) • S.vector k
      exact (one_smul ℚ (S.vector k)).symm
  | cons j L ih =>
      change
        (S.word i L).cohomologyEval G
            ((S.factor i j).cohomologyEval G (S.vector k)) =
          (S.gain i j k * S.response i L k) • S.vector k
      rw [S.factor_on_vector, map_smul, ih, mul_smul]

@[simp]
theorem response_self (S : JointProgramSpectrum G p ι)
    (i : ι) (L : List ι) : S.response i L i = 1 := by
  induction L with
  | nil => rfl
  | cons j L ih => simp [response, ih]

theorem response_zero_of_mem (S : JointProgramSpectrum G p ι)
    (i k : ι) (L : List ι) (hki : k ≠ i) (hk : k ∈ L) :
    S.response i L k = 0 := by
  induction L with
  | nil => simp at hk
  | cons j L ih =>
      rcases List.mem_cons.mp hk with h | h
      · subst j
        simp [response, S.gain_kills i k hki]
      · simp [response, ih h]

variable [Fintype ι]

/-- A finite program isolating one direction of the joint spectrum. -/
def projector (S : JointProgramSpectrum G p ι) (i : ι) :
    GradedGeometricProgram V p p :=
  S.word i Finset.univ.toList

@[simp]
theorem projector_self (S : JointProgramSpectrum G p ι) (i : ι) :
    (S.projector i).cohomologyEval G (S.vector i) = S.vector i := by
  rw [projector, S.word_on_vector, S.response_self, one_smul]

theorem projector_other (S : JointProgramSpectrum G p ι) (i k : ι)
    (hki : k ≠ i) :
    (S.projector i).cohomologyEval G (S.vector k) = 0 := by
  rw [projector, S.word_on_vector,
    S.response_zero_of_mem i k Finset.univ.toList hki (by simp), zero_smul]

/-- The full finite execution law; coefficients outside the selected slot
vanish by actual program evaluation. -/
theorem projector_on_sum (S : JointProgramSpectrum G p ι)
    (a : ι → ℚ) (i : ι) :
    (S.projector i).cohomologyEval G (∑ k, a k • S.vector k) =
      a i • S.vector i := by
  rw [map_sum]
  simp_rw [map_smul]
  rw [Finset.sum_eq_single i]
  · rw [S.projector_self]
  · intro k _ hki
    rw [S.projector_other i k hki, smul_zero]
  · simp

/-- The projectors resolve the identity on the selected spectral span. -/
theorem sum_projectors_on_sum (S : JointProgramSpectrum G p ι)
    (a : ι → ℚ) :
    (∑ i, (S.projector i).cohomologyEval G (∑ k, a k • S.vector k)) =
      ∑ k, a k • S.vector k := by
  simp_rw [S.projector_on_sum]

/-- Orthogonality and idempotence on the selected span. -/
theorem projector_comp_on_sum (S : JointProgramSpectrum G p ι)
    (a : ι → ℚ) (i j : ι) :
    (S.projector i).cohomologyEval G
        ((S.projector j).cohomologyEval G (∑ k, a k • S.vector k)) =
      if j = i then a i • S.vector i else 0 := by
  rw [S.projector_on_sum, map_smul]
  by_cases hji : j = i
  · subst j
    simp only [S.projector_self, if_pos rfl]
  · rw [S.projector_other i j hji, smul_zero, if_neg hji]

/-- Every interpolating projector preserves the genuine geometric orbit. -/
theorem projector_preserves_orbit (S : JointProgramSpectrum G p ι)
    (i : ι) {x : RationalSingularCohomology H.analytification (2 * p)}
    (hx : x ∈ geometricProgramOrbitModule G p) :
    (S.projector i).cohomologyEval G x ∈ geometricProgramOrbitModule G p :=
  program_maps_geometricProgramOrbitModule G (S.projector i) hx

end JointProgramSpectrum

#print axioms JointProgramSpectrum.word_on_vector
#print axioms JointProgramSpectrum.projector_on_sum
#print axioms JointProgramSpectrum.projector_comp_on_sum
#print axioms JointProgramSpectrum.projector_preserves_orbit

end GSTClassicalHodgeJointProgramInterpolation
