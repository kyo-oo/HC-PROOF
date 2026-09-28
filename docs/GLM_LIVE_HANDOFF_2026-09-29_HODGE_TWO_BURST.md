# GLM LIVE HANDOFF — Hodge two-burst execution

Target branch: `sol/hodge-single-separator-successor`

## Current mathematical route

Do NOT revive the old projective-detector-visibility route as an unconditional theorem. The branch proves that ordinary cycle-natural projective correspondence outputs remain algebraic and are therefore annihilated by an omniversal separator ghost. `ProjectiveOrbitIrreducibility` is retained only as a conditional/audit certificate and is Hodge-strength.

The active noncircular route is now:

1. `GenuineCycleClassGeometry` excludes the Stage-2G zero-cycle-class countermodel using positive projective-degree trace semantics.
2. A hypothetical Hodge failure gives an `OmniversalSeparatorGhost` and a synchronized nonzero `AtomicDefectTomographyGhost` in the genuine quotient `H^(2p)(X,Q) / span{point-cycle classes}` together with a nonzero finite GST Lefschetz-tomography moment on the same sheet.
3. `GSTClassicalHodgeAtomicDefectOperatorDescent` proves every ambient cohomological operator preserving the atomic span descends canonically to that defect quotient; genuine projective-correspondence operators are included.
4. `GSTClassicalHodgeAtomicDefectEquivariantIrreducibility` packages a conditional `AtomicNaturalMatrixArsenal`; it is a compiler from independently proved atomic-natural actions to Hodge closure, not a construction of those actions.
5. `GSTClassicalHodgeAtomicNaturalLefschetzPoincareClosure` further compresses that conditional arsenal to atomic-natural Lefschetz and Poincare primitives on distinct two-sheet charts. The algebraic compression is valid.
6. CRITICAL CROSS-AUDIT: `GSTClassicalHodgeAtomicNaturalLefschetzNonCircularity` and `GSTClassicalHodgeLefschetzPoincarePrimitiveNonCircularity` prove that, on one live algebraic source, atomic naturality of the required bare two-slot `L^2` restriction already forces the target sheet algebraic. Therefore a separator which annihilates the atomic span and detects that target makes the entire `AtomicNaturalLefschetzPoincarePair` type empty.
7. Consequently the Lefschetz–Poincare compression must remain conditional. The missing theorem is still the independent geometric construction/restriction theorem below bare `L^2`; do NOT promote the primitive pair family to an automatic consequence of GST coordinates or ordinary cycle naturality.

The cohomological/polarized pairing files remain useful obstruction translations/audits, but do not assert `orthogonal complement = 0`; universal algebraic pairing separation is audited as Hodge-equivalent.

## New files/theorems for immediate GLM repair

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
- `AtomicNaturalMatrixArsenal`
- `AtomicNaturalMatrixArsenal.atomicDefect_eq_zero`
- `bigradedBettiHodge_of_atomicNaturalMatrixArsenal`

### `GSTClassicalHodgeAtomicNaturalLefschetzPoincareClosure.lean`
- `AtomicNaturalLefschetzPoincarePair`
- `AtomicNaturalLefschetzPoincarePair.code_hodge`
- `AtomicNaturalLefschetzPoincarePair.matrixWord_hodge`
- `atomicNaturalMatrixArsenal_of_lefschetzPoincare`
- `atomicDefect_eq_zero_of_lefschetzPoincare`
- `bigradedBettiHodge_of_atomicNaturalLefschetzPoincare`

These are CONDITIONAL compression theorems.

### `GSTClassicalHodgeAtomicNaturalLefschetzNonCircularity.lean`
- `bareTwoSlotLefschetzHodge_eq_scaled_matrixUnit`
- `targetBasis_algebraic_of_atomicNatural_bareLefschetz`
- `no_atomicNatural_bareLefschetz_to_separatorSheet`

### `GSTClassicalHodgeLefschetzPoincarePrimitiveNonCircularity.lean`
- `targetBasis_algebraic_of_lefschetzPoincarePair`
- `no_lefschetzPoincarePair_to_separatorSheet`
- `lefschetzPoincarePair_false_of_separator`

These are HARD FIREWALLS. Preserve their statements and use them to audit any future primitive construction.

## Files that must remain intact

- `GSTClassicalHodgeStage2GSemanticRigidity.lean`
- `GSTClassicalHodgeSpineSemanticSeparation.lean`
- `GSTClassicalHodgeGenuineCycleClassGeometry.lean`
- `GSTClassicalHodgeAtomicDefectTomographyGhost.lean`
- `GSTClassicalHodgeAtomicDefectTomographySynchronization.lean`
- `GSTClassicalHodgeAtomicDefectOperatorDescent.lean`
- `GSTClassicalHodgeAtomicDefectEquivariantIrreducibility.lean`
- `GSTClassicalHodgeAtomicNaturalLefschetzNonCircularity.lean`
- `GSTClassicalHodgeAtomicNaturalLefschetzPoincareClosure.lean`
- `GSTClassicalHodgeLefschetzPoincarePrimitiveNonCircularity.lean`
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
- do not promote bare `L^2`, the Lefschetz–Poincare pair family, or any equivalent target-crossing primitive to automatic atomic naturality;
- do not delete semantic-rigidity or noncircularity audits;
- repair `Submodule.liftQ`, quotient induction, linear-map coercions, `map_sub`, or namespace API differences surgically while preserving statements.

The assistant lane now holds the mathematics fixed at this audited frontier and reconciles CI/compiler feedback in parallel.

## CI target

Compile the transformed defect/equivariance layers, Lefschetz–Poincare conditional compression, both primitive noncircularity firewalls, and `GSTClassicalHodgeTwoBurstClosureReceipt.lean`. Preserve green older modules.