import GSTClassicalHodgeFirstPrimitiveProjectiveDualSector

/-!
# GST CLASSICAL HODGE — FIRST PRIMITIVE SECTOR RETRACTION

The least-failure normal form makes every lower realized Hodge-defect sector
zero.  Therefore a contradiction does not require a return law on the whole
Hodge fiber, nor even on the whole first primitive defect sector.

It is enough to send one distinguished nonzero first-failure ghost defect down
to any lower realized defect sector and return it up with a nonzero scalar:

  z_E --down--> D_Hdg(q) --up--> D_prim(first)

  up (down z_E) = lambda * z_E,   lambda != 0.

Since `D_Hdg(q) = 0`, the left side is zero, while the right side is nonzero.

This is the smallest cross-weight extinction interface developed so far.  It
makes no claim about arbitrary Hodge vectors, basis directions, projective
irreducibility, or full quotient inversion.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeFirstPrimitiveSectorRetraction

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeAtomicDefectDuality
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgePrimitiveAtomicDefectReduction
open GSTClassicalHodgeTraceZeroPrimitiveTomographyGhost
open GSTClassicalHodgePrimitiveProjectiveDefectModule
open GSTClassicalHodgeHodgeDefectImageFunctoriality
open GSTClassicalHodgeFirstPrimitiveProjectiveFailure
open GSTClassicalHodgeFirstFailurePrimitiveImage
open GSTClassicalHodgeFirstPrimitiveProjectiveSector

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- A nonzero-scaled retraction of the entire first primitive defect sector
through one lower realized Hodge-defect sector. -/
structure FirstPrimitiveSectorScaledLowerRetraction
    {G : GeometricCycleClassSpine V H}
    (F : FirstAtomicDefectWeight V H)
    (p q : Nat)
    (hp : F.weight = p + 1)
    (D : LefschetzPrimitiveDecomposition G) where
  lower : q < F.weight
  down : PrimitiveDefectImage D (p + 1) →ₗ[ℚ] HodgeDefectImage V H q
  up : HodgeDefectImage V H q →ₗ[ℚ] PrimitiveDefectImage D (p + 1)
  scalar : ℚ
  scalar_ne_zero : scalar ≠ 0
  roundtrip : up.comp down = scalar • LinearMap.id

/-- No such sector-wide scaled lower retraction can exist at a least failure. -/
theorem no_FirstPrimitiveSectorScaledLowerRetraction
    {G : GeometricCycleClassSpine V H}
    (F : FirstAtomicDefectWeight V H)
    {p q : Nat}
    (hp : F.weight = p + 1)
    (D : LefschetzPrimitiveDecomposition G) :
    ¬ Nonempty (FirstPrimitiveSectorScaledLowerRetraction F p q hp D) := by
  intro hR
  let R := Classical.choice hR
  have hsector : PrimitiveDefectImage D (p + 1) ≠ ⊥ :=
    firstFailure_PrimitiveDefectImage_ne_bot F hp D
  have hex : ∃ z : PrimitiveDefectImage D (p + 1), z ≠ 0 := by
    by_contra hnone
    push_neg at hnone
    apply hsector
    apply le_antisymm
    · intro z hz
      simpa [hnone z] using (Submodule.zero_mem (PrimitiveDefectImage D (p + 1)))
    · exact bot_le
  rcases hex with ⟨z, hz⟩
  have hlower : HodgeDefectImage V H q = ⊥ :=
    firstAtomicDefect_lower_HodgeDefectImage_eq_bot F q R.lower
  have hdown : R.down z = 0 := by
    apply Subtype.ext
    have hmem : (R.down z).1 ∈ (⊥ : Submodule ℚ (AtomicDefectSpace V H q)) := by
      rw [← hlower]
      exact (R.down z).2
    simpa using hmem
  have hround := LinearMap.congr_fun R.roundtrip z
  rw [LinearMap.comp_apply, hdown, map_zero] at hround
  have hscalar : R.scalar • z = 0 := by
    simpa using hround.symm
  have hinv := congrArg (fun y => R.scalar⁻¹ • y) hscalar
  have hz0 : z = 0 := by
    simpa [smul_smul, R.scalar_ne_zero] using hinv
  exact hz hz0

/-- One-state version: only the distinguished first-failure ghost state has to
satisfy a nonzero-scaled lower round trip. -/
structure FirstGhostScaledLowerReturn
    {G : GeometricCycleClassSpine V H}
    {T : GSTClassicalHodgeProjectiveDegreeTrace.ProjectiveDegreeTraceSemantics V H}
    (F : FirstAtomicDefectWeight V H)
    (p q : Nat)
    (hp : F.weight = p + 1)
    (D : LefschetzPrimitiveDecomposition G)
    (A : GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor G T (p + 1))
    (E : TraceZeroPrimitiveTomographyGhost A D) where
  lower : q < F.weight
  down : PrimitiveDefectImage D (p + 1) →ₗ[ℚ] HodgeDefectImage V H q
  up : HodgeDefectImage V H q →ₗ[ℚ] PrimitiveDefectImage D (p + 1)
  scalar : ℚ
  scalar_ne_zero : scalar ≠ 0
  ghost_roundtrip :
    let z : PrimitiveDefectImage D (p + 1) :=
      ⟨E.defectState,
        firstFailure_ghost_defectState_mem_PrimitiveDefectImage F hp D A E⟩
    up (down z) = scalar • z

/-- **ONE-STATE FIRST-FAILURE EXTINCTION.**
Even a scaled lower return for the single distinguished nonzero ghost state is
impossible at the least failure. -/
theorem no_FirstGhostScaledLowerReturn
    {G : GeometricCycleClassSpine V H}
    {T : GSTClassicalHodgeProjectiveDegreeTrace.ProjectiveDegreeTraceSemantics V H}
    (F : FirstAtomicDefectWeight V H)
    {p q : Nat}
    (hp : F.weight = p + 1)
    (D : LefschetzPrimitiveDecomposition G)
    (A : GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor G T (p + 1))
    (E : TraceZeroPrimitiveTomographyGhost A D) :
    ¬ Nonempty (FirstGhostScaledLowerReturn F p q hp D A E) := by
  intro hR
  let R := Classical.choice hR
  let z : PrimitiveDefectImage D (p + 1) :=
    ⟨E.defectState,
      firstFailure_ghost_defectState_mem_PrimitiveDefectImage F hp D A E⟩
  have hz : z ≠ 0 := by
    intro hz0
    apply E.defectState_ne_zero
    exact congrArg Subtype.val hz0
  have hlower : HodgeDefectImage V H q = ⊥ :=
    firstAtomicDefect_lower_HodgeDefectImage_eq_bot F q R.lower
  have hdown : R.down z = 0 := by
    apply Subtype.ext
    have hmem : (R.down z).1 ∈ (⊥ : Submodule ℚ (AtomicDefectSpace V H q)) := by
      rw [← hlower]
      exact (R.down z).2
    simpa using hmem
  have hround := R.ghost_roundtrip
  dsimp [z] at hround ⊢
  rw [hdown, map_zero] at hround
  have hscalar : R.scalar • z = 0 := by
    simpa [z] using hround.symm
  have hinv := congrArg (fun y => R.scalar⁻¹ • y) hscalar
  have hz0 : z = 0 := by
    simpa [smul_smul, R.scalar_ne_zero] using hinv
  exact hz hz0

/-- Pointwise formulation without packaging linear maps: any candidate lower
transport/return pair must fail the scaled round-trip equation on the ghost. -/
theorem firstGhost_scaled_roundtrip_must_fail
    {G : GeometricCycleClassSpine V H}
    {T : GSTClassicalHodgeProjectiveDegreeTrace.ProjectiveDegreeTraceSemantics V H}
    (F : FirstAtomicDefectWeight V H)
    {p q : Nat}
    (hp : F.weight = p + 1)
    (D : LefschetzPrimitiveDecomposition G)
    (A : GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor G T (p + 1))
    (E : TraceZeroPrimitiveTomographyGhost A D)
    (hq : q < F.weight)
    (down : PrimitiveDefectImage D (p + 1) →ₗ[ℚ] HodgeDefectImage V H q)
    (up : HodgeDefectImage V H q →ₗ[ℚ] PrimitiveDefectImage D (p + 1))
    (scalar : ℚ)
    (hscalar : scalar ≠ 0) :
    let z : PrimitiveDefectImage D (p + 1) :=
      ⟨E.defectState,
        firstFailure_ghost_defectState_mem_PrimitiveDefectImage F hp D A E⟩
    up (down z) ≠ scalar • z := by
  dsimp
  intro hround
  let R : FirstGhostScaledLowerReturn F p q hp D A E := {
    lower := hq
    down := down
    up := up
    scalar := scalar
    scalar_ne_zero := hscalar
    ghost_roundtrip := hround
  }
  exact no_FirstGhostScaledLowerReturn F hp D A E ⟨R⟩

#check FirstPrimitiveSectorScaledLowerRetraction
#check no_FirstPrimitiveSectorScaledLowerRetraction
#check FirstGhostScaledLowerReturn
#check no_FirstGhostScaledLowerReturn
#check firstGhost_scaled_roundtrip_must_fail

#print axioms no_FirstPrimitiveSectorScaledLowerRetraction
#print axioms no_FirstGhostScaledLowerReturn
#print axioms firstGhost_scaled_roundtrip_must_fail

end GSTClassicalHodgeFirstPrimitiveSectorRetraction
