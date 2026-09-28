import GSTClassicalHodgeGeometricPrimitiveQuotient
import GSTClassicalHodgeAtomicDefectDuality
import GSTClassicalHodgeSingleSheetCrown

/-!
# GST CLASSICAL HODGE — MINIMAL ALGEBRAIC PRIMITIVE QUOTIENT

The geometric primitive quotient from the previous layer removes every state
arriving at the least bad Hodge weight from a strictly lower weight through a
verified mixed geometric program.  Minimality gives much more than annihilation
of those states: every lower Hodge weight is already algebraic.

Indeed, if q is below the least separator weight then no genuine Hodge basis
sheet in weight q admits an atomic separator.  The single-sheet crown converts
that statement into vanishing of the complete atomic defect map in weight q.
Hence every true rational (q,q) Hodge state is an actual native cycle class.

Combining this with master program naturality proves that the entire lower
program image in the minimal bad weight consists of genuine algebraic Hodge
classes.  Therefore the remaining obstruction is a quotient of the genuine
Hodge fiber by an explicitly verified algebraic Hodge submodule.

No new hypothesis is introduced.  The construction is forced by minimality of
the separator and the already-proved cycle-class naturality of the graded
program algebra.
-/

set_option maxHeartbeats 90000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeMinimalAlgebraicPrimitiveQuotient

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeAtomicDefectDuality
open GSTClassicalHodgeSingleSheetCrown
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeGradedGeometricProgramOrbit
open GSTClassicalHodgeMinimalPrimitiveSeparatorGhost
open GSTClassicalHodgeGeometricPrimitiveQuotient

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Below the least bad weight, the atomic defect map vanishes identically.
This is a direct consequence of the definition of minimality: every basis
separator is absent, and basiswise defect vanishing determines the whole
linear defect map. -/
theorem minimalGhost_lowerWeight_atomicDefect_zero
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    {q : Nat}
    (hq : q < M.weight) :
    atomicDefectLinearMap V H q = 0 := by
  apply (atomicDefect_zero_iff_basis_zero V H q).2
  intro i
  apply (basis_atomicDefect_zero_iff_no_separator V H q i).2
  refine ⟨?_⟩
  intro S
  apply M.minimal q hq
  exact ⟨i, ⟨S⟩⟩

/-- Therefore every genuine Hodge vector in a lower weight lies in the span of
actual codimension-q point-cycle classes. -/
theorem minimalGhost_lowerWeight_hodge_le_atomicSpan
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    {q : Nat}
    (hq : q < M.weight) :
    rationalHodgeSubspace (H.hodgeBigrading q) ≤
      pointCycleClassSpan q (H.cycleClass q) := by
  exact (atomicDefectLinearMap_eq_zero_iff V H q).1
    (minimalGhost_lowerWeight_atomicDefect_zero G M hq)

/-- Range form: every lower-weight Hodge vector has an actual native cycle
representative. -/
theorem minimalGhost_lowerWeight_hodge_le_cycleClassRange
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    {q : Nat}
    (hq : q < M.weight) :
    rationalHodgeSubspace (H.hodgeBigrading q) ≤
      LinearMap.range (H.cycleClass q) := by
  rw [smoothProjective_cycleClass_range_eq_atomic_span V H q]
  exact minimalGhost_lowerWeight_hodge_le_atomicSpan G M hq

/-- Elementwise source-cycle extraction for a lower Hodge state. -/
theorem minimalGhost_lowerWeight_has_native_cycle
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    {q : Nat}
    (hq : q < M.weight)
    (alpha : ClassicalHodgeFiber V H q) :
    ∃ Z : codimensionCycles V.X q,
      H.cycleClass q Z = alpha.1 := by
  exact minimalGhost_lowerWeight_hodge_le_cycleClassRange G M hq alpha.2

/-- Every raw lower-program image in the minimal bad weight is itself an
actual cycle-class value.  This uses only source algebraicity below the minimum
and the master cycle-class commuting square for the chosen geometric program. -/
theorem minimalGhost_lowerProgramImageSet_mem_cycleClassRange
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    {x : AmbientWeightCohomology H M.weight}
    (hx : x ∈ lowerProgramImageSet G M.weight) :
    x ∈ LinearMap.range (H.cycleClass M.weight) := by
  rcases hx with ⟨q, hq, P, alpha, rfl⟩
  rcases minimalGhost_lowerWeight_has_native_cycle G M hq alpha with
    ⟨Z, hZ⟩
  refine ⟨P.cycleEval G Z, ?_⟩
  rw [P.cycleClass_cycleEval G Z, hZ]

/-- The complete lower geometric image module is algebraic in the minimal bad
weight. -/
theorem minimalGhost_lowerProgramImageModule_le_cycleClassRange
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G) :
    lowerProgramImageModule G M.weight ≤
      LinearMap.range (H.cycleClass M.weight) := by
  apply Submodule.span_le.mpr
  intro x hx
  exact minimalGhost_lowerProgramImageSet_mem_cycleClassRange G M hx

/-- Consequently the whole lower geometric image is also true Hodge type in
the minimal weight.  This follows from actual algebraicity, not from an
abstract assumption that arbitrary Hodge vectors are preserved by programs. -/
theorem minimalGhost_lowerProgramImageModule_le_hodge
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G) :
    lowerProgramImageModule G M.weight ≤
      rationalHodgeSubspace (H.hodgeBigrading M.weight) := by
  intro x hx
  have hrange :=
    minimalGhost_lowerProgramImageModule_le_cycleClassRange G M hx
  rcases hrange with ⟨Z, rfl⟩
  exact G.algebraic_is_hodge M.weight Z

/-- The lower-generated algebraic Hodge states, expressed intrinsically as a
submodule of the genuine Hodge fiber. -/
noncomputable def minimalLowerAlgebraicHodgeSubmodule
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G) :
    Submodule ℚ (ClassicalHodgeFiber V H M.weight) :=
  (lowerProgramImageModule G M.weight).comap
    (rationalHodgeSubspace (H.hodgeBigrading M.weight)).subtype

@[simp]
theorem mem_minimalLowerAlgebraicHodgeSubmodule_iff
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    (alpha : ClassicalHodgeFiber V H M.weight) :
    alpha ∈ minimalLowerAlgebraicHodgeSubmodule G M ↔
      alpha.1 ∈ lowerProgramImageModule G M.weight :=
  Iff.rfl

/-- Every lower-generated Hodge state is already in the full algebraic Hodge
subspace of the minimal weight. -/
theorem minimalLowerAlgebraicHodgeSubmodule_le_AlgebraicHodgeSubspace
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G) :
    minimalLowerAlgebraicHodgeSubmodule G M ≤
      AlgebraicHodgeSubspace V H M.weight := by
  intro alpha halpha
  have hrange :=
    minimalGhost_lowerProgramImageModule_le_cycleClassRange G M halpha
  rw [smoothProjective_cycleClass_range_eq_atomic_span V H M.weight] at hrange
  exact hrange

/-- The offending minimal basis sheet is not contained in the lower-generated
algebraic Hodge submodule. -/
theorem minimalGhost_basis_not_mem_minimalLowerAlgebraicHodgeSubmodule
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G) :
    classicalHodgeBasis V H M.weight M.sheet ∉
      minimalLowerAlgebraicHodgeSubmodule G M := by
  intro hmem
  exact minimalGhost_sheet_not_mem_lowerProgramImage G M hmem

/-- Genuine Hodge primitive quotient: remove all Hodge states already produced
algebraically from lower weights through the verified geometry. -/
abbrev MinimalPrimitiveHodgeQuotient
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G) :=
  ClassicalHodgeFiber V H M.weight ⧸
    minimalLowerAlgebraicHodgeSubmodule G M

/-- Canonical projection to the genuine primitive Hodge quotient. -/
noncomputable def primitiveHodgeClass
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G) :
    ClassicalHodgeFiber V H M.weight →ₗ[ℚ]
      MinimalPrimitiveHodgeQuotient G M :=
  (minimalLowerAlgebraicHodgeSubmodule G M).mkQ

/-- The offending basis sheet survives as a nonzero genuine primitive Hodge
quotient class. -/
theorem minimalGhost_primitiveHodgeClass_ne_zero
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G) :
    primitiveHodgeClass G M
      (classicalHodgeBasis V H M.weight M.sheet) ≠ 0 := by
  intro hz
  have hmem :
      classicalHodgeBasis V H M.weight M.sheet ∈
        minimalLowerAlgebraicHodgeSubmodule G M := by
    exact (Submodule.Quotient.mk_eq_zero
      (minimalLowerAlgebraicHodgeSubmodule G M)).mp hz
  exact minimalGhost_basis_not_mem_minimalLowerAlgebraicHodgeSubmodule G M hmem

/-- Restriction of the minimal separator to the genuine Hodge fiber. -/
noncomputable def minimalGhostHodgeDetector
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G) :
    ClassicalHodgeFiber V H M.weight →ₗ[ℚ] ℚ :=
  M.separator.detector.comp
    (rationalHodgeSubspace (H.hodgeBigrading M.weight)).subtype

/-- The restricted detector annihilates the complete lower-generated Hodge
submodule. -/
theorem minimalLowerAlgebraicHodgeSubmodule_le_detectorKernel
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G) :
    minimalLowerAlgebraicHodgeSubmodule G M ≤
      LinearMap.ker (minimalGhostHodgeDetector G M) := by
  intro alpha halpha
  exact minimalGhost_lowerProgramImage_le_kernel G M halpha

/-- Descended nonzero detector on the genuine primitive Hodge quotient. -/
noncomputable def minimalPrimitiveHodgeDetector
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G) :
    MinimalPrimitiveHodgeQuotient G M →ₗ[ℚ] ℚ :=
  (minimalLowerAlgebraicHodgeSubmodule G M).liftQ
    (minimalGhostHodgeDetector G M)
    (minimalLowerAlgebraicHodgeSubmodule_le_detectorKernel G M)

@[simp]
theorem minimalPrimitiveHodgeDetector_primitiveHodgeClass
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G)
    (alpha : ClassicalHodgeFiber V H M.weight) :
    minimalPrimitiveHodgeDetector G M (primitiveHodgeClass G M alpha) =
      M.separator.detector alpha.1 := by
  exact Submodule.liftQ_apply
    (minimalLowerAlgebraicHodgeSubmodule G M)
    (minimalGhostHodgeDetector G M) alpha

/-- The primitive quotient detector remains genuinely nonzero. -/
theorem minimalPrimitiveHodgeDetector_ne_zero
    (G : GeometricCycleClassSpine V H)
    (M : MinimalPrimitiveGhost G) :
    minimalPrimitiveHodgeDetector G M ≠ 0 := by
  intro hz
  have hval := LinearMap.congr_fun hz
    (primitiveHodgeClass G M
      (classicalHodgeBasis V H M.weight M.sheet))
  simp [minimalPrimitiveHodgeDetector_primitiveHodgeClass] at hval
  exact M.separator.detects_basis hval

/-- **MINIMAL ALGEBRAIC PRIMITIVE FAILURE PACKET.**
Every classical Stage-2G failure yields a nonzero quotient of one genuine Hodge
fiber by a submodule already proved algebraic through lower-weight geometry,
and a nonzero detector on that quotient.  Thus all remaining failure is truly
same-weight primitive algebraicity, not cross-weight propagation. -/
theorem not_hodge_yields_nontrivial_minimalPrimitiveHodgeQuotient
    (G : GeometricCycleClassSpine V H)
    (hnot : ¬ BigradedBettiHodgeStatement V H) :
    ∃ M : MinimalPrimitiveGhost G,
      primitiveHodgeClass G M
          (classicalHodgeBasis V H M.weight M.sheet) ≠ 0
      ∧ minimalPrimitiveHodgeDetector G M ≠ 0
      ∧ minimalLowerAlgebraicHodgeSubmodule G M ≤
          AlgebraicHodgeSubspace V H M.weight := by
  let M := minimalPrimitiveGhostOfFailure G hnot
  exact ⟨M,
    minimalGhost_primitiveHodgeClass_ne_zero G M,
    minimalPrimitiveHodgeDetector_ne_zero G M,
    minimalLowerAlgebraicHodgeSubmodule_le_AlgebraicHodgeSubspace G M⟩

#check minimalGhost_lowerWeight_atomicDefect_zero
#check minimalGhost_lowerWeight_hodge_le_atomicSpan
#check minimalGhost_lowerWeight_hodge_le_cycleClassRange
#check minimalGhost_lowerProgramImageModule_le_cycleClassRange
#check minimalGhost_lowerProgramImageModule_le_hodge
#check minimalLowerAlgebraicHodgeSubmodule
#check minimalLowerAlgebraicHodgeSubmodule_le_AlgebraicHodgeSubspace
#check MinimalPrimitiveHodgeQuotient
#check primitiveHodgeClass
#check minimalGhost_primitiveHodgeClass_ne_zero
#check minimalPrimitiveHodgeDetector
#check minimalPrimitiveHodgeDetector_ne_zero
#check not_hodge_yields_nontrivial_minimalPrimitiveHodgeQuotient

#print axioms minimalGhost_lowerWeight_atomicDefect_zero
#print axioms minimalGhost_lowerProgramImageModule_le_cycleClassRange
#print axioms minimalGhost_lowerProgramImageModule_le_hodge
#print axioms minimalLowerAlgebraicHodgeSubmodule_le_AlgebraicHodgeSubspace
#print axioms minimalGhost_primitiveHodgeClass_ne_zero
#print axioms minimalPrimitiveHodgeDetector_ne_zero
#print axioms not_hodge_yields_nontrivial_minimalPrimitiveHodgeQuotient

end GSTClassicalHodgeMinimalAlgebraicPrimitiveQuotient
