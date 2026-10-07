import GSTClassicalHodgeOmniversalNativeOrbitSeparation
import GSTClassicalHodgeOmniversalSeparatorGhostCrown
import GSTClassicalHodgeBranchPacketPlaneRealization
import GSTClassicalHodgeProjectiveDegreeTrace
import GSTClassicalHodgeRelativeSuccessorExactStratum

/-!
# GST CLASSICAL HODGE — SHEET SIEGE ROUTE (ROUTE S)

Companion module to `docs/GST_ROUTE_S_SIEGE_STUDY_20261007.tex`.

## STATUS (AUTHORITY 005 AUDIT — READ BEFORE USING)

This module decommissions the branch-packet law D
(`GSTBranchPacketPlaneRealization` = `GhostSeedTargetStrictClosure`, `rfl`)
as a *proof target* and installs the sheet siege in its place.  Nothing here
assumes D, and nothing here quantifies over ghosts in a premise.

| Statement in this file | Status |
|---|---|
| `hodge_of_geometricPlaneCompleteness` | CITATION-COMPLETE (proof = two existing theorems) |
| `sheetSiege_sheet_mem_orbitSet` | CITATION-COMPLETE (orbit membership by definition) |
| `sheetSiege_sheet_mem_orbitModule` | CITATION-COMPLETE (span + subset_span) |
| `sheetSiege_conditional_noGhost_of_monomialSaturation` | CONDITIONAL on the UNPROVEN saturation premise; proof = V3 monomial kill |
| `sheetSiege_conditional_hodge_of_monomialSaturation` | CONDITIONAL, same premise; proof = ghost iff |
| `SheetSiegeCoheightAdditivity` (L1) | UNPROVEN PREMISE — see docstring for the exact obstruction |
| `SheetSiegeLiveWeightSeeds` (L2) | UNPROVEN PREMISE — see docstring |
| `SheetSiegeDegreeTraceConstructed` (L3-a) | UNPROVEN PREMISE — a construction obligation |

L3-b (word nativity) is NOT stated here: stating it correctly requires the
`GradedGeometricProgram` word-level interface, and a wrong statement would be
worse than an honest TODO.  It is specified in the study, §6.

META-DESIGN LEVEL (AUTHORITY 002): no local Lean.  Namespace resolution and
the two orientation-sensitive proof lines marked `-- COMPARE:` belong to the
brother's compile pass.  Every citation below is pinned to the V3 audit state
`2926a33` with file:line.
-/

set_option maxHeartbeats 120000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeSheetSiegeRoute

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeGradedGeometricProgramOrbit
open GSTClassicalHodgeGradedGeometricOrbitAlgebra
open GSTClassicalHodgeOmniversalNativeOrbitSeparation
open GSTClassicalHodgeOmniversalSeparatorGhostCrown
open GSTClassicalHodgeSynchronizedDefectOrbit
open GSTClassicalHodgeRankFreeArsenalIrreducibility

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-! ## §1. The assembly — citation-complete

`GeometricGSTPlaneCompleteness` (every basis sheet of every weight is the
exact output of one verified program from the geometric origin;
`GSTClassicalHodgeOmniversalNativeOrbitSeparation.lean:65--70`) implies
Hodge through the existing four-link chain:

  coverage → orbit cyclicity (`orbitCyclic_of_geometricPlane`, same file :86)
          → ghost extinction (`no_omniversalSeparatorGhost_of_gradedGeo…`,
            `GSTClassicalHodgeOmniversalSeparatorGhostCrown.lean:235`)
          → Hodge (`hodge_of_gradedGeometricOrbitModuleCyclic_noGhost`,
            same file :246).

The previous plan never stated this assembly because it was staring through
the law D.  This theorem is the siege's front door.
-/

/-- **ROUTE S ASSEMBLY (CITATION-COMPLETE).**
Per-sheet program coverage of the classical plane implies the exact
finite rational Hodge statement.  The proof is two existing theorems. -/
theorem hodge_of_geometricPlaneCompleteness
    (G : GeometricCycleClassSpine V H)
    (hcov : GeometricGSTPlaneCompleteness G) :
    BigradedBettiHodgeStatement V H :=
  hodge_of_gradedGeometricOrbitModuleCyclic_noGhost G
    (orbitCyclic_of_geometricPlane G hcov)

/-- **ONE WON SHEET IS AN UNCONDITIONAL THEOREM (orbit-set form).**
A single program witnessing one basis sheet banks that sheet into the
verified orbit.  Partial credit: each battle is independent. -/
theorem sheetSiege_sheet_mem_orbitSet
    (G : GeometricCycleClassSpine V H)
    (q : Nat) (j : ClassicalHodgeBasisIndex V H q)
    (P : GradedGeometricProgram V 0 q)
    (hP : P.cohomologyEval G (geometricOriginClass V H) =
      (classicalHodgeBasis V H q j).1) :
    (classicalHodgeBasis V H q j).1 ∈ geometricProgramOrbitSet G q :=
  ⟨P, hP⟩
  -- COMPARE: if membership orients the other way, use `hP.symm`
  -- (the GhostCrown proof at :219--224 destructures with ⟨P, hP⟩).

/-- **ONE WON SHEET IS AN UNCONDITIONAL THEOREM (module form).** -/
theorem sheetSiege_sheet_mem_orbitModule
    (G : GeometricCycleClassSpine V H)
    (q : Nat) (j : ClassicalHodgeBasisIndex V H q)
    (P : GradedGeometricProgram V 0 q)
    (hP : P.cohomologyEval G (geometricOriginClass V H) =
      (classicalHodgeBasis V H q j).1) :
    (classicalHodgeBasis V H q j).1 ∈ geometricProgramOrbitModule G q := by
  rw [← geometricProgramOrbitSubspace_eq_module G q]
  exact Submodule.subset_span (sheetSiege_sheet_mem_orbitSet G q j P hP)

/-! ## §2. The siege premises — UNPROVEN, honestly flagged

These are the three load-bearing lemmas of the study (§6 there).  None is
proven; none quantifies over ghosts; all are codimension-sensitive (they fail
on the zero-cycle world, which the firewall DEMANDS of any Hodge-sufficient
premise).  They are stated as `Prop` definitions with their exact
obstructions, per AUTHORITY 005's honest-naming rule.
-/

/-- **UNPROVEN PREMISE L1 — COHEIGHT ADDITIVITY.**
Every live codimension-`p` point has separator successors of ambient
coheight exactly `p + 1`.

Obstruction: `RelativeSuccessorAmbientExact`
(`GSTClassicalHodgeRelativeSuccessorExactStratum.lean:46--52`) is a premise in
every exact-stratum and successor-seed theorem; it has never been discharged.
Ingredients are unconditional: `separatorClass_height_one`
(`ProjectiveSeparatorHeightOne.lean:61--63`),
`separator_minimalPrime_prime_height_one` (:80--84),
`finite_principal_cut_coheight_one`
(`ProperCutCodimensionOne.lean:196--200`).  The missing piece is the
bookkeeping bridge from ideal height 1 to ambient `Order.coheight` —
Krull principal ideal theorem level, not Hodge-coded content.

Kill-switch: failure on smooth projective irreducible worlds kills Route S
at L1. -/
def SheetSiegeCoheightAdditivity (V : SmoothProjectiveComplexScheme) : Prop :=
  ∀ (p : Nat) (x : CodimensionPoint V.X p),
    ProjectivelyLiveSource V.projective.n (V.projective.immersion x) →
      GSTClassicalHodgeRelativeSuccessorExactStratum.RelativeSuccessorAmbientExact V p x

/-- **UNPROVEN PREMISE L2 — LIVE WEIGHT SEEDS (escape-free chains).**
Every weight carries a native Hodge orbit seed.

Obstruction: the escape dichotomy
(`SuccessorSeedEscapeDichotomy.lean:120--131`) yields `Nonempty
(NativeHodgeOrbitSeed (p+1)) ∨ Nonempty (PositiveCosmicHomologyEscape (p+1))`;
`separator_successor_seed_of_no_escape` (:179--194) needs L1 + `hlive` +
global no-escape.  Discharging the escape branch is where the residual Hodge
content concentrates (study §6, L2).  This restatement in terms of seeds
(rather than the escape type) keeps the premise ghost-free and
signature-stable.

Kill-switch: if proving this requires per-sheet algebraicity hypotheses,
L2 is D in disguise; abort and re-audit. -/
def SheetSiegeLiveWeightSeeds
    (V : SmoothProjectiveComplexScheme) (H : HodgeBigradedBettiData V) : Prop :=
  ∀ q : Nat,
    Nonempty (NativeHodgeOrbitSeed (V := V) (H := H) (p := q))

/-- **UNPROVEN PREMISE L3-a — DEGREE-TRACE CONSTRUCTION.**
The projective degree-trace semantics is constructed, not assumed.

Obstruction: `ProjectiveDegreeTraceSemantics`
(`ProjectiveDegreeTrace.lean:63--73`) is structure data: trace functionals
plus positive point degrees.  The classical recipe (cup with hyperplane
power, integrate over the fundamental class) is a construction task from
Poincare duality + ampleness.  It is impossible on the zero-cycle world
(`no_degreeTrace_for_zeroCycleClass_at_point`,
`NativePointSeedDegreeUpgrade.lean:98--111`) — exactly as the firewall
demands, so it must be BUILT from genuine geometry, never assumed.

Kill-switch: if the construction needs input beyond Poincare duality and
ampleness, the debt is larger than priced; re-audit. -/
def SheetSiegeDegreeTraceConstructed
    (V : SmoothProjectiveComplexScheme) (H : HodgeBigradedBettiData V) : Prop :=
  Nonempty (GSTClassicalHodgeProjectiveDegreeTrace.ProjectiveDegreeTraceSemantics V H)

/-! ## §3. Conditional corollaries — the starvation engine, wired

The V3 monomial kill (`false_of_ghost_monomialSheetSeed`,
`BranchPacketPlaneRealization.lean:725--741`) is sheet-generic and
unconditional in its logic.  Full monomial saturation of the seed supply
starves every ghost: no sheet remains where a synchronized native seed can
be forced off-diagonal.  These corollaries are CONDITIONAL on the saturation
premise (which is NOT proven and is not claimed); their proofs are citations.
-/

/-- **CONDITIONAL — ghost starvation under full monomial saturation.**
If every sheet of every weight carries a synchronized native seed that is a
live multiple of that sheet, every omniversal separator ghost is refuted by
the V3 monomial kill.  The premise is UNPROVEN; the implication is not. -/
theorem sheetSiege_conditional_noGhost_of_monomialSaturation
    (G : GeometricCycleClassSpine V H)
    (hsat : ∀ (q : Nat) (j : ClassicalHodgeBasisIndex V H q),
      ∃ S : NativeHodgeOrbitSeed (V := V) (H := H) (p := q),
        hodgeMatrixUnit S.sourceIndex j S.hodge = S.hodge) :
    IsEmpty (OmniversalSeparatorGhost G) := by
  refine ⟨?_⟩
  intro E
  obtain ⟨S, hmono⟩ := hsat E.weight E.sheet
  exact GSTClassicalHodgeBranchPacketPlaneRealization.false_of_ghost_monomialSheetSeed
    G E S (congrArg Subtype.val hmono)

/-- **CONDITIONAL — Hodge under full monomial saturation.**
Same premise; closes through the ghost equivalence
(`hodge_iff_no_omniversalSeparatorGhost`, `GhostCrown.lean:116`). -/
theorem sheetSiege_conditional_hodge_of_monomialSaturation
    (G : GeometricCycleClassSpine V H)
    (hsat : ∀ (q : Nat) (j : ClassicalHodgeBasisIndex V H q),
      ∃ S : NativeHodgeOrbitSeed (V := V) (H := H) (p := q),
        hodgeMatrixUnit S.sourceIndex j S.hodge = S.hodge) :
    BigradedBettiHodgeStatement V H :=
  (hodge_iff_no_omniversalSeparatorGhost G).2
    (sheetSiege_conditional_noGhost_of_monomialSaturation G hsat)

#check hodge_of_geometricPlaneCompleteness
#check sheetSiege_sheet_mem_orbitSet
#check sheetSiege_sheet_mem_orbitModule
#check SheetSiegeCoheightAdditivity
#check SheetSiegeLiveWeightSeeds
#check SheetSiegeDegreeTraceConstructed
#check sheetSiege_conditional_noGhost_of_monomialSaturation
#check sheetSiege_conditional_hodge_of_monomialSaturation

#print axioms hodge_of_geometricPlaneCompleteness
#print axioms sheetSiege_sheet_mem_orbitSet
#print axioms sheetSiege_sheet_mem_orbitModule
#print axioms sheetSiege_conditional_noGhost_of_monomialSaturation
#print axioms sheetSiege_conditional_hodge_of_monomialSaturation

end GSTClassicalHodgeSheetSiegeRoute
