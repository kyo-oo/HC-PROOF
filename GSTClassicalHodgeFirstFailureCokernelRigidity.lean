import GSTClassicalHodgeHodgeDefectImageFunctoriality
import GSTClassicalHodgeDefectModuloAtomicReciprocity
import GSTClassicalHodgePolarizedAdjointReciprocity
import GSTClassicalHodgeTraceZeroPrimitiveTomographyGhost

/-!
# GST CLASSICAL HODGE — FIRST-FAILURE COKERNEL RIGIDITY

At the least nonzero Hodge-defect weight `p+1`, the previous Hodge-defect map is
zero.  Therefore every genuine principal-cut image from weight `p` has zero
atomic defect.  Any nonzero-defect Hodge class at weight `p+1` is consequently
outside the image of the actual projective principal cut.

This makes the primitive residual a literal geometric cokernel obstruction.
It also gives a sharp reciprocity no-go: if the first bad weight admitted a
genuine Hodge-stable transport down to any lower weight together with a return
whose round trip was a nonzero scalar modulo atomic classes, the lower defect
vanishing would propagate back and contradict firstness.  The same statement
is derived from perfect-pairing adjointness plus a scaled pairing law.

Thus any surviving first counterexample must simultaneously evade:

* the genuine principal-cut image;
* every nonzero-scaled modulo-atomic down/up reciprocity to a lower weight;
* every polarized adjoint realization of such reciprocity.

No Hodge-strength irreducibility assumption is used.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeFirstFailureCokernelRigidity

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeAtomicDefectDuality
open GSTClassicalHodgeCrossWeightAtomicDefectDescent
open GSTClassicalHodgePrimitiveAtomicDefectReduction
open GSTClassicalHodgeTraceZeroPrimitiveTomographyGhost
open GSTClassicalHodgeFirstPrimitiveProjectiveFailure
open GSTClassicalHodgeHodgeDefectImageFunctoriality
open GSTClassicalHodgeDefectModuloAtomicReciprocity
open GSTClassicalHodgePolarizedHodgeGhost
open GSTClassicalHodgePolarizedDefectReciprocity
open GSTClassicalHodgePolarizedAdjointReciprocity

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Any Hodge vector with nonzero atomic defect is outside the genuine
principal-cut image once the preceding weight has zero Hodge defect. -/
theorem nonzeroDefect_not_mem_principalCutHodgeMap_range
    (G : GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (p : Nat)
    (hsource : atomicDefectLinearMap V H p = 0)
    (beta : ClassicalHodgeFiber V H (p + 1))
    (hbeta : atomicDefectLinearMap V H (p + 1) beta ≠ 0) :
    beta ∉ LinearMap.range (principalCutHodgeMap G p) := by
  intro hmem
  rcases hmem with ⟨alpha, halpha⟩
  have halphaDef : atomicDefectLinearMap V H p alpha = 0 := by
    rw [hsource]
    rfl
  have hcut :
      atomicDefectLinearMap V H (p + 1) (principalCutHodgeMap G p alpha) = 0 := by
    rw [atomicDefect_principalCutHodgeMap G p alpha, halphaDef]
    exact map_zero _
  apply hbeta
  rw [← halpha]
  exact hcut

/-- The normalized trace-zero primitive ghost at a local first failure is a
literal cokernel class for the genuine principal cut. -/
theorem traceZeroGhost_not_mem_principalCutHodgeMap_range
    {G : GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H}
    {D : LefschetzPrimitiveDecomposition G}
    {T : GSTClassicalHodgeProjectiveDegreeTrace.ProjectiveDegreeTraceSemantics V H}
    {p : Nat}
    {A : GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor G T (p + 1)}
    (E : TraceZeroPrimitiveTomographyGhost A D)
    (hsource : atomicDefectLinearMap V H p = 0) :
    E.traceZeroClass ∉ LinearMap.range (principalCutHodgeMap G p) :=
  nonzeroDefect_not_mem_principalCutHodgeMap_range
    G p hsource E.traceZeroClass E.defect_ne_zero

/-- At a globally least bad successor weight, every nonzero-defect Hodge class
is outside the preceding principal-cut image. -/
theorem firstFailure_nonzeroDefect_outside_principalCut
    (F : FirstAtomicDefectWeight V H)
    {p : Nat}
    (hp : F.weight = p + 1)
    (G : GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (beta : ClassicalHodgeFiber V H (p + 1))
    (hbeta : atomicDefectLinearMap V H (p + 1) beta ≠ 0) :
    beta ∉ LinearMap.range (principalCutHodgeMap G p) := by
  apply nonzeroDefect_not_mem_principalCutHodgeMap_range G p
  · exact firstAtomicDefect_predecessor_zero F hp
  · exact hbeta

/-- **FIRST-FAILURE MODULO-ATOMIC RECIPROCITY NO-GO.**
No least bad weight can admit a nonzero-scaled genuine Hodge-defect round trip
to a strictly lower weight. -/
theorem firstFailure_forbids_lower_modAtomic_reciprocity
    (F : FirstAtomicDefectWeight V H)
    (q : Nat)
    (hq : q < F.weight)
    (R : HodgeDefectReturnModuloAtomic V H F.weight q) : False := by
  have htarget : atomicDefectLinearMap V H q = 0 := F.lower_zero q hq
  have hsource : atomicDefectLinearMap V H F.weight = 0 :=
    R.source_hodge_of_target_hodge htarget
  exact F.defect_ne_zero hsource

/-- Equivalently, the existence of any such genuine nonzero-scaled return law
at the first failure is impossible. -/
theorem firstFailure_no_lower_modAtomic_reciprocity
    (F : FirstAtomicDefectWeight V H)
    (q : Nat)
    (hq : q < F.weight) :
    ¬ Nonempty (HodgeDefectReturnModuloAtomic V H F.weight q) := by
  intro hR
  exact firstFailure_forbids_lower_modAtomic_reciprocity
    F q hq (Classical.choice hR)

/-- **POLARIZED FIRST-FAILURE NO-GO.**
For a genuine Hodge-stable down/up graded pair from the first bad weight to a
lower weight, perfect-pairing adjointness and a nonzero-scaled pairing law
cannot both hold. -/
theorem firstFailure_forbids_adjoint_scaled_lower_return
    (F : FirstAtomicDefectWeight V H)
    (q : Nat)
    (hq : q < F.weight)
    (R : HodgeStableGradedReturnData V H F.weight q)
    (P : PerfectHodgeFiberPairing (V := V) (H := H) F.weight)
    (Q : PerfectHodgeFiberPairing (V := V) (H := H) q) :
    ¬ (R.PairingAdjointLaw P Q ∧ R.ScaledPairingLaw P Q) := by
  intro hboth
  rcases hboth with ⟨hadj, hscale⟩
  have htarget : atomicDefectLinearMap V H q = 0 := F.lower_zero q hq
  have hsource : atomicDefectLinearMap V H F.weight = 0 :=
    R.source_hodge_of_adjoint_scaled_target_hodge P Q hadj hscale htarget
  exact F.defect_ne_zero hsource

/-- A useful disjunctive reading: at the first failure, every candidate
polarized geometric return must fail adjointness or fail the scaled Lefschetz
pairing identity. -/
theorem firstFailure_adjoint_or_scaled_law_must_fail
    (F : FirstAtomicDefectWeight V H)
    (q : Nat)
    (hq : q < F.weight)
    (R : HodgeStableGradedReturnData V H F.weight q)
    (P : PerfectHodgeFiberPairing (V := V) (H := H) F.weight)
    (Q : PerfectHodgeFiberPairing (V := V) (H := H) q) :
    ¬ R.PairingAdjointLaw P Q ∨ ¬ R.ScaledPairingLaw P Q := by
  by_cases hadj : R.PairingAdjointLaw P Q
  · right
    intro hscale
    exact firstFailure_forbids_adjoint_scaled_lower_return
      F q hq R P Q ⟨hadj, hscale⟩
  · exact Or.inl hadj

#check nonzeroDefect_not_mem_principalCutHodgeMap_range
#check traceZeroGhost_not_mem_principalCutHodgeMap_range
#check firstFailure_nonzeroDefect_outside_principalCut
#check firstFailure_forbids_lower_modAtomic_reciprocity
#check firstFailure_no_lower_modAtomic_reciprocity
#check firstFailure_forbids_adjoint_scaled_lower_return
#check firstFailure_adjoint_or_scaled_law_must_fail

#print axioms nonzeroDefect_not_mem_principalCutHodgeMap_range
#print axioms traceZeroGhost_not_mem_principalCutHodgeMap_range
#print axioms firstFailure_forbids_lower_modAtomic_reciprocity
#print axioms firstFailure_forbids_adjoint_scaled_lower_return
#print axioms firstFailure_adjoint_or_scaled_law_must_fail

end GSTClassicalHodgeFirstFailureCokernelRigidity
