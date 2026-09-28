# GLM LIVE HANDOFF — Hodge two-burst execution

Target branch: `sol/hodge-single-separator-successor`

## Current mathematical route

Do NOT revive the old projective-detector-visibility route as an unconditional theorem. The branch proves that ordinary cycle-natural projective correspondence outputs remain algebraic and are therefore annihilated by an omniversal separator ghost. `ProjectiveOrbitIrreducibility` is retained only as a conditional/audit certificate and is Hodge-strength.

The active noncircular route is now:

1. `GenuineCycleClassGeometry` excludes the Stage-2G zero-cycle-class countermodel using positive projective-degree trace semantics.
2. A hypothetical Hodge failure gives an `OmniversalSeparatorGhost` and, more sharply, a synchronized nonzero `AtomicDefectTomographyGhost` in the genuine quotient
   `H^(2p)(X,Q) / span{point-cycle classes}` together with a nonzero finite GST Lefschetz-tomography moment on the same sheet.
3. `GSTClassicalHodgeAtomicDefectOperatorDescent` proves every ambient cohomological operator preserving the atomic span descends canonically to that defect quotient; genuine projective-correspondence operators are included.
4. NEW splice: `GSTClassicalHodgeAtomicDefectEquivariantIrreducibility` defines `AtomicNaturalHodgeOperator`, proves defect equivariance and preservation of `AlgebraicHodgeSubspace`, closes these operators under identity/rational scaling/addition/composition, and packages an `AtomicNaturalMatrixArsenal`. Its crown `bigradedBettiHodge_of_atomicNaturalMatrixArsenal` composes these independently geometric operators with the existing rank-free GST irreducibility theorem.
5. The assistant lane is now compressing the remaining geometric obligation from all matrix units to the already-proved two-slot Lefschetz–Poincare primitive generation. The target is NOT to assume matrix-unit naturality; it is to show independently constructed atomic-natural primitive operators generate the required Hodge actions.

The cohomological/polarized pairing files remain useful obstruction translations/audits, but do not assert `orthogonal complement = 0`; universal algebraic pairing separation is audited as Hodge-equivalent.

## New files/theorems for immediate GLM repair

### `GSTClassicalHodgeAtomicDefectTomographyGhost.lean`
- `ghostAtomicDefect_ne_zero`
- `ghost_basis_has_nonzero_lefschetzMoment`
- `failure_yields_atomicDefectTomographyGhost`
- `not_hodge_iff_nonempty_atomicDefectTomographyGhost`

### `GSTClassicalHodgeAtomicDefectOperatorDescent.lean`
- `atomicDefectOperator`
- `atomicDefectOperator_mk`
- `atomicDefectOperator_comp`
- `projectiveCorrespondence_atomicSpanStable`
- `projectiveDefectOperator`
- `ghostDefectDetector_projectiveDefectOperator`

### `GSTClassicalHodgeAtomicDefectEquivariantIrreducibility.lean`
- `AtomicNaturalHodgeOperator`
- `AtomicNaturalHodgeOperator.defect_equivariant`
- `AtomicNaturalHodgeOperator.preserves_algebraicHodge`
- `AtomicNaturalHodgeOperator.id`
- `AtomicNaturalHodgeOperator.smul`
- `AtomicNaturalHodgeOperator.add`
- `AtomicNaturalHodgeOperator.comp`
- `AtomicNaturalMatrixArsenal`
- `AtomicNaturalMatrixArsenal.rankFreeInvariant`
- `AtomicNaturalMatrixArsenal.atomicDefect_eq_zero`
- `bigradedBettiHodge_of_atomicNaturalMatrixArsenal`

Latest assistant mathematics commit introducing the equivariant splice: `ffbd51353dbcab735ffcf332a3c6482505fa4831` (the branch may have advanced after this; repair the live head).

## Files that must remain intact

- `GSTClassicalHodgeStage2GSemanticRigidity.lean`
- `GSTClassicalHodgeSpineSemanticSeparation.lean`
- `GSTClassicalHodgeGenuineCycleClassGeometry.lean`
- `GSTClassicalHodgeAtomicDefectTomographyGhost.lean`
- `GSTClassicalHodgeAtomicDefectTomographySynchronization.lean`
- `GSTClassicalHodgeAtomicDefectOperatorDescent.lean`
- `GSTClassicalHodgeAtomicDefectEquivariantIrreducibility.lean`
- `GSTClassicalHodgeMultiplicityForgettingKernel.lean`
- `GSTClassicalHodgeArsenalNonCircularity.lean`
- `GSTClassicalHodgeBareLefschetzNonCircularity.lean`
- `GSTClassicalHodgeProjectiveOrbitIrreducibilityAudit.lean`
- `GSTClassicalHodgeCohomologicalPairingFrontier.lean`
- `GSTClassicalHodgePolarizedOrthogonalExtinctionAudit.lean`
- `GSTClassicalHodgeTwoBurstClosureReceipt.lean`

## GLM lane

Repair parser/elaboration/namespace/Mathlib/tactic/API failures only. Keep theorem statements and the noncircular mathematical route unless a theorem is formally inconsistent. In particular:

- do not replace `AtomicSpanStable` by a stronger matrix-unit/Hodge assumption;
- do not insert a basis-cycle bridge;
- do not add `source_action`, `acts_as_GST`, exact cosmic matrix-unit realization, or arbitrary point-transition kernels as axioms;
- do not delete semantic-rigidity or noncircularity audits;
- if `Submodule.liftQ`, quotient induction, linear-map coercions, or namespace APIs differ in pinned Mathlib, repair those bodies surgically while preserving statements.

The assistant lane continues the Lefschetz–Poincare primitive compression and higher-level integration in parallel.

## CI target

The branch workflow `.github/workflows/hodge-conjecture.yml` should compile the transformed defect layers explicitly. Prioritize failures in the new quotient/equivariance files and preserve green older modules.
