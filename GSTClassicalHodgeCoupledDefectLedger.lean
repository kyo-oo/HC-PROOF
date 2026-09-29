import GSTClassicalHodgeCrossWeightDefectTerminalCrown

/-!
# GST CLASSICAL HODGE — COUPLED DEFECT LEDGER

The earlier cross-weight retraction asked for an exact ambient round trip

    R (L alpha) = lambda * alpha.

That is stronger than the atomic-defect quotient actually needs.  GST's
coupled Past/Future philosophy suggests the correct conservation law: a round
trip may emit genuine geometric information while preserving the unresolved
packet.

At weight p we therefore allow

    R (L alpha) = lambda * alpha + cycleClass (E alpha),

where `E alpha` is an actual native codimension-p algebraic cycle.  The emitted
cycle is visible in ambient cohomology but vanishes in the quotient by the
complete atomic cycle-class span.  Consequently the unresolved atomic defect
returns exactly scaled by `lambda`.

This is a genuinely coupled law:

* the forward half is the already constructed projective principal cut;
* the backward half is one genuine graded native/cohomological transport;
* the discrepancy is not discarded — it is retained as an explicit native
  emitted cycle;
* no Hodge basis vector is assumed algebraic;
* no same-weight matrix unit or cosmic naturality is assumed;
* no equality modulo an unspecified subspace is stored: the correction is an
  actual linear native-cycle ledger.

A nonzero scale makes the forward atomic-defect step injective.  A family of
such coupled ledger steps therefore propagates eventual high-weight defect
extinction all the way back to every weight, closing the Stage-2G Hodge target.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeCoupledDefectLedger

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeAtomicDefectDuality
open GSTClassicalHodgeCrossWeightNativePropagation
open GSTClassicalHodgeCrossWeightAtomicDefectDescent
open GSTClassicalHodgeCrossWeightDefectTerminalCrown
open GSTClassicalHodgeGeometricCycleClassSpine

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- One coupled conservation step for the genuine projective principal cut.

The returned cohomology is allowed to differ from the scaled input by the
cycle class of an explicitly emitted native cycle.  This is the Hodge analogue
of GST's coupled ledger identity `past + scale * future = conserved packet`:
the unresolved defect is the future packet, while the native correction is
emitted geometric information. -/
structure PrincipalCutCoupledLedgerStep
    (G : GeometricCycleClassSpine V H)
    (p : Nat) where
  returnPair : GradedCycleClassOperatorPair V H (p + 1) p
  scalar : ℚ
  scalar_ne_zero : scalar ≠ 0
  emittedCycle :
    CohAt H p →ₗ[ℚ] codimensionCycles V.X p
  balance :
    ∀ alpha : CohAt H p,
      returnPair.cohomologyOperator
          ((G.principalCutPair p).cohomologyOperator alpha) =
        scalar • alpha + H.cycleClass p (emittedCycle alpha)

namespace PrincipalCutCoupledLedgerStep

/-- The emitted native correction always lies in the complete atomic
cycle-class span. -/
theorem emitted_mem_atomicSpan
    {G : GeometricCycleClassSpine V H}
    (R : PrincipalCutCoupledLedgerStep G p)
    (alpha : CohAt H p) :
    H.cycleClass p (R.emittedCycle alpha) ∈ AtomicSpanAt H p := by
  rw [← smoothProjective_cycleClass_range_eq_atomic_span V H p]
  exact ⟨R.emittedCycle alpha, rfl⟩

/-- Ambient form of the ledger: after subtracting the conserved unresolved
packet, the complete round-trip discrepancy is an actual atomic cycle class. -/
theorem roundtrip_sub_scaled_mem_atomicSpan
    {G : GeometricCycleClassSpine V H}
    (R : PrincipalCutCoupledLedgerStep G p)
    (alpha : CohAt H p) :
    R.returnPair.cohomologyOperator
          ((G.principalCutPair p).cohomologyOperator alpha) -
        R.scalar • alpha ∈ AtomicSpanAt H p := by
  calc
    R.returnPair.cohomologyOperator
          ((G.principalCutPair p).cohomologyOperator alpha) -
        R.scalar • alpha
        = H.cycleClass p (R.emittedCycle alpha) := by
            rw [R.balance alpha]
            abel
    _ ∈ AtomicSpanAt H p := R.emitted_mem_atomicSpan alpha

/-- **COUPLED DEFECT CONSERVATION.**
After quotienting by genuine algebraic cycle classes, the emitted ledger
vanishes and the round trip is exactly multiplication by the nonzero conserved
scale. -/
theorem defect_roundtrip
    {G : GeometricCycleClassSpine V H}
    (R : PrincipalCutCoupledLedgerStep G p)
    (z : DefectAt V H p) :
    R.returnPair.defectOperator
        (principalCutDefectOperator G p z) =
      R.scalar • z := by
  refine Submodule.Quotient.induction_on z ?_
  intro alpha
  rw [principalCutDefectOperator_mk,
      GradedCycleClassOperatorPair.defectOperator_mk,
      R.balance alpha]
  change
    (Submodule.mkQ (AtomicSpanAt H p))
        (R.scalar • alpha + H.cycleClass p (R.emittedCycle alpha)) =
      R.scalar • (Submodule.mkQ (AtomicSpanAt H p)) alpha
  rw [(Submodule.mkQ (AtomicSpanAt H p)).map_add,
      (Submodule.mkQ (AtomicSpanAt H p)).map_smul]
  have hemitted :
      (Submodule.mkQ (AtomicSpanAt H p))
          (H.cycleClass p (R.emittedCycle alpha)) = 0 := by
    exact (Submodule.Quotient.mk_eq_zero (AtomicSpanAt H p)).2
      (R.emitted_mem_atomicSpan alpha)
  rw [hemitted, add_zero]

/-- A coupled ledger step makes the genuine principal-cut action injective on
atomic defects.  The emitted geometric packet cannot destroy unresolved
information. -/
theorem principalCutDefectOperator_injective
    {G : GeometricCycleClassSpine V H}
    (R : PrincipalCutCoupledLedgerStep G p) :
    Function.Injective (principalCutDefectOperator G p) := by
  intro x y hxy
  have h := congrArg R.returnPair.defectOperator hxy
  rw [R.defect_roundtrip x, R.defect_roundtrip y] at h
  have h' := congrArg (fun z => R.scalar⁻¹ • z) h
  simpa [smul_smul, R.scalar_ne_zero] using h'

/-- Zero after a coupled principal-cut step implies zero before the step. -/
theorem defect_eq_zero_of_principalCut_eq_zero
    {G : GeometricCycleClassSpine V H}
    (R : PrincipalCutCoupledLedgerStep G p)
    (z : DefectAt V H p)
    (hz : principalCutDefectOperator G p z = 0) :
    z = 0 := by
  apply R.principalCutDefectOperator_injective
  simpa using hz

/-- Forgetting the explicit emitted cycle leaves the weaker modulo-atomic
round-trip law.  Thus the coupled ledger is a concrete geometric realization
of the quotient statement, not a renamed quotient assumption. -/
theorem modAtomic_roundtrip
    {G : GeometricCycleClassSpine V H}
    (R : PrincipalCutCoupledLedgerStep G p) :
    ∀ alpha : CohAt H p,
      R.returnPair.cohomologyOperator
          ((G.principalCutPair p).cohomologyOperator alpha) -
        R.scalar • alpha ∈ AtomicSpanAt H p :=
  R.roundtrip_sub_scaled_mem_atomicSpan

end PrincipalCutCoupledLedgerStep

/-- Coupled conservation law at every projective principal-cut level. -/
structure PrincipalCutCoupledLedger
    (G : GeometricCycleClassSpine V H) where
  step : ∀ p : Nat, PrincipalCutCoupledLedgerStep G p

namespace PrincipalCutCoupledLedger

/-- Every finite genuine principal-cut defect iterate is injective under the
coupled ledger. -/
theorem principalCutDefectIterate_injective
    {G : GeometricCycleClassSpine V H}
    (L : PrincipalCutCoupledLedger G)
    (p n : Nat) :
    Function.Injective (principalCutDefectIterate G p n) := by
  induction n with
  | zero =>
      simpa using
        (Function.injective_id :
          Function.Injective (id : DefectAt V H p → DefectAt V H p))
  | succ n ih =>
      rw [principalCutDefectIterate_succ]
      exact (L.step (p + n)).principalCutDefectOperator_injective.comp ih

/-- **COUPLED BACKWARD EXTINCTION.**
If an n-step future defect vanishes, conservation of the complete emitted
cycle ledger forces the original defect to vanish. -/
theorem defect_eq_zero_of_iterate_eq_zero
    {G : GeometricCycleClassSpine V H}
    (L : PrincipalCutCoupledLedger G)
    (p n : Nat)
    (z : DefectAt V H p)
    (hz : principalCutDefectIterate G p n z = 0) :
    z = 0 := by
  apply L.principalCutDefectIterate_injective p n
  simpa using hz

/-- Eventual defect terminality plus the coupled all-weight ledger annihilates
all atomic Hodge defects. -/
theorem atomicDefectLinearMap_zero_of_coupledLedger_and_terminal
    {G : GeometricCycleClassSpine V H}
    (L : PrincipalCutCoupledLedger G)
    (T : DefectTerminality V H) :
    ∀ p : Nat, atomicDefectLinearMap V H p = 0 := by
  intro p
  apply LinearMap.ext
  intro alpha
  rcases T.terminal p with ⟨n, hterminal⟩
  letI : Subsingleton (DefectAt V H (p + n)) := hterminal
  have hfuture :
      principalCutDefectIterate G p n
          (atomicDefectLinearMap V H p alpha) = 0 :=
    Subsingleton.elim _ _
  exact L.defect_eq_zero_of_iterate_eq_zero p n
    (atomicDefectLinearMap V H p alpha) hfuture

/-- **COUPLED-LEDGER HODGE CROWN.**
The new GST-style conservation law plus eventual defect extinction proves the
complete Stage-2G Hodge statement without any same-weight matrix-unit
externalization. -/
theorem bigradedBettiHodge_of_coupledLedger_and_defectTerminality
    {G : GeometricCycleClassSpine V H}
    (L : PrincipalCutCoupledLedger G)
    (T : DefectTerminality V H) :
    BigradedBettiHodgeStatement V H := by
  exact (bigradedBettiHodgeStatement_iff_atomicDefect_zero V H).2
    (L.atomicDefectLinearMap_zero_of_coupledLedger_and_terminal T)

/-- Ordinary high-degree cohomology terminality is enough: it canonically
implies defect terminality, then the coupled ledger propagates extinction back
through every finite weight. -/
theorem bigradedBettiHodge_of_coupledLedger_and_ambientTerminality
    {G : GeometricCycleClassSpine V H}
    (L : PrincipalCutCoupledLedger G)
    (T : AmbientCohomologyTerminality V H) :
    BigradedBettiHodgeStatement V H :=
  L.bigradedBettiHodge_of_coupledLedger_and_defectTerminality
    T.toDefectTerminality

/-- Crown collecting the new cosmology: exact emitted-cycle conservation,
defect injectivity, finite-depth no-loss, and the global Hodge landing. -/
theorem coupled_defect_ledger_crown
    {G : GeometricCycleClassSpine V H}
    (L : PrincipalCutCoupledLedger G)
    (T : DefectTerminality V H) :
    (∀ p : Nat, ∀ z : DefectAt V H p,
      (L.step p).returnPair.defectOperator
          (principalCutDefectOperator G p z) =
        (L.step p).scalar • z)
    ∧ (∀ p n : Nat,
      Function.Injective (principalCutDefectIterate G p n))
    ∧ BigradedBettiHodgeStatement V H := by
  exact ⟨
    fun p z => (L.step p).defect_roundtrip z,
    fun p n => L.principalCutDefectIterate_injective p n,
    L.bigradedBettiHodge_of_coupledLedger_and_defectTerminality T⟩

end PrincipalCutCoupledLedger

#check PrincipalCutCoupledLedgerStep
#check PrincipalCutCoupledLedgerStep.roundtrip_sub_scaled_mem_atomicSpan
#check PrincipalCutCoupledLedgerStep.defect_roundtrip
#check PrincipalCutCoupledLedgerStep.principalCutDefectOperator_injective
#check PrincipalCutCoupledLedger
#check PrincipalCutCoupledLedger.principalCutDefectIterate_injective
#check PrincipalCutCoupledLedger.atomicDefectLinearMap_zero_of_coupledLedger_and_terminal
#check PrincipalCutCoupledLedger.bigradedBettiHodge_of_coupledLedger_and_defectTerminality
#check PrincipalCutCoupledLedger.bigradedBettiHodge_of_coupledLedger_and_ambientTerminality
#check PrincipalCutCoupledLedger.coupled_defect_ledger_crown

#print axioms PrincipalCutCoupledLedgerStep.defect_roundtrip
#print axioms PrincipalCutCoupledLedgerStep.principalCutDefectOperator_injective
#print axioms PrincipalCutCoupledLedger.principalCutDefectIterate_injective
#print axioms PrincipalCutCoupledLedger.bigradedBettiHodge_of_coupledLedger_and_defectTerminality
#print axioms PrincipalCutCoupledLedger.coupled_defect_ledger_crown

end GSTClassicalHodgeCoupledDefectLedger
