import Mathlib.Algebra.Module.Projective
import GSTClassicalHodgeMinimalGhostAutomaticProjector
import GSTClassicalHodgeAtomicSpan

/-!
# GST CLASSICAL HODGE — AUTOMATIC ALGEBRAIC SOURCE PROJECTOR

For the minimal-ghost two-slot attack, the source projector does not need an
independent geometric externalization either.

Take one nonzero algebraic Hodge state `a` and one live basis coordinate `i`.
Normalize the i-th Hodge coordinate so that it reads `a` as one, extend that
scalar readout linearly to ambient cohomology, and write the result back into
the line spanned by `a`.

Because `a` is algebraic, choose one actual native cycle `Z_a` with
`cycleClass Z_a = a`.  Every point-cycle input is then lifted natively by the
same scalar multiple of `Z_a`.  Hence the resulting rank-one source projector
has native point lifts automatically.

Combined with the automatic minimal-ghost target projector, this removes TWO
of the THREE old primitive externalization obligations.  Only the middle GST
Lefschetz/mixing primitive remains.
-/

set_option maxHeartbeats 90000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeAlgebraicSourceProjector

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeNativeGeneratorNaturality

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

abbrev Coh := RationalSingularCohomology H.analytification (2 * p)
abbrev HFiber := ClassicalHodgeFiber V H p

/-- Normalized coordinate readout on the genuine Hodge fiber. -/
noncomputable def normalizedSourceRead
    (a : HFiber V H p)
    (i : ClassicalHodgeBasisIndex V H p)
    (hi : hodgeCoordinate i a ≠ 0) :
    HFiber V H p →ₗ[ℚ] ℚ :=
  (hodgeCoordinate i a)⁻¹ • hodgeCoordinate i

@[simp]
theorem normalizedSourceRead_self
    (a : HFiber V H p)
    (i : ClassicalHodgeBasisIndex V H p)
    (hi : hodgeCoordinate i a ≠ 0) :
    normalizedSourceRead a i hi a = 1 := by
  simp [normalizedSourceRead, hi]

/-- Extend the normalized scalar coordinate from the Hodge subspace to all
ambient rational singular cohomology. -/
noncomputable def ambientSourceRead
    (a : HFiber V H p)
    (i : ClassicalHodgeBasisIndex V H p)
    (hi : hodgeCoordinate i a ≠ 0) : Coh H p →ₗ[ℚ] ℚ :=
  Classical.choose (LinearMap.exists_extend (normalizedSourceRead a i hi))

/-- The ambient extension agrees with the normalized coordinate on every Hodge
state. -/
theorem ambientSourceRead_on_hodge
    (a : HFiber V H p)
    (i : ClassicalHodgeBasisIndex V H p)
    (hi : hodgeCoordinate i a ≠ 0)
    (x : HFiber V H p) :
    ambientSourceRead a i hi x.1 = normalizedSourceRead a i hi x := by
  have h := Classical.choose_spec
    (LinearMap.exists_extend (normalizedSourceRead a i hi))
  exact LinearMap.congr_fun h x

/-- Rank-one ambient projector onto the line spanned by the chosen algebraic
source. -/
noncomputable def algebraicSourceProjector
    (a : HFiber V H p)
    (i : ClassicalHodgeBasisIndex V H p)
    (hi : hodgeCoordinate i a ≠ 0) :
    Coh H p →ₗ[ℚ] Coh H p :=
  LinearMap.smulRight (ambientSourceRead a i hi) a.1

/-- The source projector fixes the chosen source exactly. -/
theorem algebraicSourceProjector_fixes_source
    (a : HFiber V H p)
    (i : ClassicalHodgeBasisIndex V H p)
    (hi : hodgeCoordinate i a ≠ 0) :
    algebraicSourceProjector a i hi a.1 = a.1 := by
  rw [algebraicSourceProjector]
  change ambientSourceRead a i hi a.1 • a.1 = a.1
  rw [ambientSourceRead_on_hodge]
  rw [normalizedSourceRead_self]
  simp

/-- Every algebraic Hodge source has an actual native cycle representative. -/
theorem exists_native_source_cycle
    (a : HFiber V H p)
    (ha : a ∈ AlgebraicHodgeSubspace V H p) :
    ∃ Z : codimensionCycles V.X p, H.cycleClass p Z = a.1 := by
  have hspan : a.1 ∈ pointCycleClassSpan p (H.cycleClass p) := ha
  have hrange := pointCycleClassSpan_le_cycleClass_range
    p (H.cycleClass p) hspan
  exact hrange

/-- **AUTOMATIC SOURCE-PROJECTOR NATURALITY.**
If the target line is algebraic, every point input has a native lift obtained
by scaling one native representative of the source line. -/
theorem algebraicSourceProjector_hasNativePointLifts
    (a : HFiber V H p)
    (ha : a ∈ AlgebraicHodgeSubspace V H p)
    (i : ClassicalHodgeBasisIndex V H p)
    (hi : hodgeCoordinate i a ≠ 0) :
    HasNativePointLifts (p := p) (cl := H.cycleClass p)
      (algebraicSourceProjector a i hi) := by
  obtain ⟨Za, hZa⟩ := exists_native_source_cycle a ha
  intro x
  refine ⟨(ambientSourceRead a i hi
      (H.cycleClass p (GSTNativeCodimensionCyclePresentation.codimensionPointCycle
        V.X p x))) • Za, ?_⟩
  rw [LinearMap.map_smul, hZa]
  rfl

/-- Consequently the source projector preserves the complete atomic
cycle-class span. -/
theorem algebraicSourceProjector_atomicStable
    (a : HFiber V H p)
    (ha : a ∈ AlgebraicHodgeSubspace V H p)
    (i : ClassicalHodgeBasisIndex V H p)
    (hi : hodgeCoordinate i a ≠ 0) :
    GSTClassicalHodgeGeneratorwiseAtomicStability.AtomicSpanStable
      (p := p) (cl := H.cycleClass p)
      (algebraicSourceProjector a i hi) := by
  exact (smoothProjective_atomicStable_iff_nativePointLifts
    (V := V) (H := H) (p := p)
    (algebraicSourceProjector a i hi)).2
      (algebraicSourceProjector_hasNativePointLifts a ha i hi)

#check normalizedSourceRead
#check ambientSourceRead
#check algebraicSourceProjector
#check algebraicSourceProjector_fixes_source
#check exists_native_source_cycle
#check algebraicSourceProjector_hasNativePointLifts
#check algebraicSourceProjector_atomicStable

#print axioms algebraicSourceProjector_fixes_source
#print axioms exists_native_source_cycle
#print axioms algebraicSourceProjector_hasNativePointLifts
#print axioms algebraicSourceProjector_atomicStable

end GSTClassicalHodgeAlgebraicSourceProjector
