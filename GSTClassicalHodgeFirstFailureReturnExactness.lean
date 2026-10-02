import GSTClassicalHodgePrimitiveAtomicDefectReduction
import GSTClassicalHodgeTraceZeroPrimitiveTomographyGhost
import GSTClassicalHodgeAtomicSpan

/-!
# GST CLASSICAL HODGE — FIRST-FAILURE RETURN EXACTNESS

At a first bad successor weight p+1, the source weight p already has zero
atomic defect.  Consequently EVERY rational (p,p) Hodge class is algebraic,
and the genuine projective principal cut carries it to an algebraic class at
weight p+1.

This makes the much-used nonzero-scaled modulo-atomic return condition
completely transparent.  For a target Hodge class E, the existence of

    beta in Hodge_p,
    lambda != 0,
    L(beta) - lambda E in AtomicSpan_(p+1)

is equivalent to E itself lying in the atomic span.

Thus at first failure the residual return law is not a weaker auxiliary
geometric statement: after the already-proved lower-weight extinction, it is
EXACTLY the missing algebraicity of the target class.  Any correspondence
packet which implies such a return has necessarily solved the residual Hodge
step; it cannot be manufactured from lower-weight naturality alone.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeFirstFailureReturnExactness

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeAtomicDefectDuality
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgePrimitiveAtomicDefectReduction
open GSTClassicalHodgeTraceZeroPrimitiveTomographyGhost
open GSTClassicalHodgeAtomicDefectTraceNormalization
open GSTClassicalHodgeProjectiveDegreeTrace

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- The bare residual content of a first-ghost return: some lower Hodge class
returns under the genuine principal cut to a nonzero multiple of E modulo the
actual algebraic cycle-class span. -/
def HasNonzeroPrincipalCutReturnModuloAtomic
    (G : GeometricCycleClassSpine V H)
    (E : ClassicalHodgeFiber V H (p + 1)) : Prop :=
  ∃ beta : ClassicalHodgeFiber V H p,
  ∃ lambda : ℚ,
    lambda ≠ 0 ∧
      (principalCutHodgeMap G p beta).1 - lambda • E.1 ∈
        pointCycleClassSpan (p + 1) (H.cycleClass (p + 1))

/-- Source defect zero means every source Hodge class lies in the actual
cycle-class range. -/
theorem sourceHodge_mem_cycleClassRange_of_defect_zero
    (hsource : atomicDefectLinearMap V H p = 0)
    (beta : ClassicalHodgeFiber V H p) :
    beta.1 ∈ LinearMap.range (H.cycleClass p) := by
  have hspan :
      beta.1 ∈ pointCycleClassSpan p (H.cycleClass p) :=
    (atomicDefectLinearMap_eq_zero_iff V H p).1 hsource beta.2
  rw [smoothProjective_cycleClass_range_eq_atomic_span V H p]
  exact hspan

/-- The genuine projective principal cut sends every source Hodge class to an
actual target cycle class once the source defect has vanished. -/
theorem principalCutHodgeMap_mem_atomic_of_source_defect_zero
    (G : GeometricCycleClassSpine V H)
    (hsource : atomicDefectLinearMap V H p = 0)
    (beta : ClassicalHodgeFiber V H p) :
    (principalCutHodgeMap G p beta).1 ∈
      pointCycleClassSpan (p + 1) (H.cycleClass (p + 1)) := by
  rcases sourceHodge_mem_cycleClassRange_of_defect_zero
      (V := V) (H := H) hsource beta with ⟨Z, hZ⟩
  have htargetRange :
      (principalCutHodgeMap G p beta).1 ∈
        LinearMap.range (H.cycleClass (p + 1)) := by
    refine ⟨(G.principalCutPair p).cycleOperator Z, ?_⟩
    rw [(G.principalCutPair p).cycleClass_natural]
    simpa [principalCutHodgeMap_coe, hZ]
  rw [← smoothProjective_cycleClass_range_eq_atomic_span V H (p + 1)]
  exact htargetRange

/-- **FIRST-FAILURE RETURN EXACTNESS.**
Once weight p has zero defect, a nonzero-scaled principal-cut return modulo
algebraic classes exists if and only if the target Hodge class is itself
algebraic. -/
theorem nonzeroPrincipalCutReturnModuloAtomic_iff_target_atomic
    (G : GeometricCycleClassSpine V H)
    (hsource : atomicDefectLinearMap V H p = 0)
    (E : ClassicalHodgeFiber V H (p + 1)) :
    HasNonzeroPrincipalCutReturnModuloAtomic (p := p) G E ↔
      E.1 ∈ pointCycleClassSpan (p + 1) (H.cycleClass (p + 1)) := by
  constructor
  · rintro ⟨beta, lambda, hlambda, hreturn⟩
    let A := pointCycleClassSpan (p + 1) (H.cycleClass (p + 1))
    have hL : (principalCutHodgeMap G p beta).1 ∈ A :=
      principalCutHodgeMap_mem_atomic_of_source_defect_zero G hsource beta
    have hscaled0 :
        (principalCutHodgeMap G p beta).1 -
            ((principalCutHodgeMap G p beta).1 - lambda • E.1) ∈ A :=
      A.sub_mem hL hreturn
    have hscaled : lambda • E.1 ∈ A := by
      convert hscaled0 using 1 <;> abel
    have hunscale := A.smul_mem lambda⁻¹ hscaled
    simpa [smul_smul, hlambda] using hunscale
  · intro hE
    refine ⟨0, 1, one_ne_zero, ?_⟩
    have hneg : -E.1 ∈
        pointCycleClassSpan (p + 1) (H.cycleClass (p + 1)) :=
      (pointCycleClassSpan (p + 1) (H.cycleClass (p + 1))).neg_mem hE
    simpa using hneg

/-- Defect form of the same exactness theorem. -/
theorem nonzeroPrincipalCutReturnModuloAtomic_iff_target_defect_zero
    (G : GeometricCycleClassSpine V H)
    (hsource : atomicDefectLinearMap V H p = 0)
    (E : ClassicalHodgeFiber V H (p + 1)) :
    HasNonzeroPrincipalCutReturnModuloAtomic (p := p) G E ↔
      atomicDefectLinearMap V H (p + 1) E = 0 := by
  rw [nonzeroPrincipalCutReturnModuloAtomic_iff_target_atomic G hsource E]
  rw [atomicDefectLinearMap_apply]
  exact (Submodule.Quotient.mk_eq_zero
    (pointCycleClassSpan (p + 1) (H.cycleClass (p + 1)))).symm

/-- Therefore the canonical trace-zero first ghost at a genuinely first bad
weight cannot admit even the bare scaled principal-cut return.  This is the
content hidden inside every stronger correspondence-return packet. -/
theorem firstGhost_forbids_bare_nonzero_return
    {G : GeometricCycleClassSpine V H}
    {D : LefschetzPrimitiveDecomposition G}
    {T : ProjectiveDegreeTraceSemantics V H}
    {A : TraceAnchor G T (p + 1)}
    (hsource : atomicDefectLinearMap V H p = 0)
    (E : TraceZeroPrimitiveTomographyGhost A D) :
    ¬ HasNonzeroPrincipalCutReturnModuloAtomic (p := p) G E.traceZeroClass := by
  intro hreturn
  have hzero : atomicDefectLinearMap V H (p + 1) E.traceZeroClass = 0 :=
    (nonzeroPrincipalCutReturnModuloAtomic_iff_target_defect_zero
      G hsource E.traceZeroClass).1 hreturn
  exact E.defect_ne_zero hzero

/-- Conversely, proving the bare return for every target Hodge class at the
first successor immediately kills that entire target defect map. -/
theorem targetDefect_zero_of_all_nonzeroPrincipalCutReturns
    (G : GeometricCycleClassSpine V H)
    (hsource : atomicDefectLinearMap V H p = 0)
    (hreturn : ∀ E : ClassicalHodgeFiber V H (p + 1),
      HasNonzeroPrincipalCutReturnModuloAtomic (p := p) G E) :
    atomicDefectLinearMap V H (p + 1) = 0 := by
  apply LinearMap.ext
  intro E
  exact (nonzeroPrincipalCutReturnModuloAtomic_iff_target_defect_zero
    G hsource E).1 (hreturn E)

#check HasNonzeroPrincipalCutReturnModuloAtomic
#check sourceHodge_mem_cycleClassRange_of_defect_zero
#check principalCutHodgeMap_mem_atomic_of_source_defect_zero
#check nonzeroPrincipalCutReturnModuloAtomic_iff_target_atomic
#check nonzeroPrincipalCutReturnModuloAtomic_iff_target_defect_zero
#check firstGhost_forbids_bare_nonzero_return
#check targetDefect_zero_of_all_nonzeroPrincipalCutReturns

#print axioms nonzeroPrincipalCutReturnModuloAtomic_iff_target_atomic
#print axioms nonzeroPrincipalCutReturnModuloAtomic_iff_target_defect_zero
#print axioms firstGhost_forbids_bare_nonzero_return
#print axioms targetDefect_zero_of_all_nonzeroPrincipalCutReturns

end GSTClassicalHodgeFirstFailureReturnExactness
