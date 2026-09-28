# GLM LIVE HANDOFF — Hodge two-burst execution

Target branch: `sol/hodge-single-separator-successor`

## Current mathematical route

Do NOT revive the old projective-detector-visibility route as an unconditional theorem. The branch proves that ordinary cycle-natural projective correspondence outputs remain algebraic and are therefore annihilated by an omniversal separator ghost. `ProjectiveOrbitIrreducibility` is retained only as a conditional/audit certificate and is Hodge-strength.

The active noncircular route is now:

1. `GenuineCycleClassGeometry` excludes the Stage-2G zero-cycle-class countermodel using positive projective-degree trace semantics.
2. A hypothetical Hodge failure gives an `OmniversalSeparatorGhost` and, more sharply, a synchronized nonzero `AtomicDefectTomographyGhost` in the genuine quotient `H^(2p)(X,Q) / span{point-cycle classes}` together with a nonzero finite GST Lefschetz-tomography moment on the same sheet.
3. `GSTClassicalHodgeAtomicDefectOperatorDescent` proves every ambient cohomological operator preserving the atomic span descends canonically to that defect quotient; genuine projective-correspondence operators are included.
4. `GSTClassicalHodgeAtomicDefectEquivariantIrreducibility` defines `AtomicNaturalHodgeOperator`, proves defect equivariance and preservation of `AlgebraicHodgeSubspace`, closes these operators under identity/rational scaling/addition/composition, and packages an `AtomicNaturalMatrixArsenal`. Its crown is a conditional irreducibility splice, not a geometric construction of the arsenal.
5. `GSTClassicalHodgeAtomicNaturalLefschetzNonCircularity` now audits the proposed primitive compression. On one live algebraic source, an atomic-natural operator whose Hodge restriction is the universal two-slot bare `L^2` primitive already forces the target basis sheet algebraic. Thus the bare-Lefschetz primitive CANNOT be inserted as an automatic geometry theorem on a ghost crossing.
6. Any actual closure must go below this interface: independently construct geometry whose Hodge restriction theorem is proved without assuming the target sheet or equivalent matrix-unit naturality.

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
- `AtomicNaturalMatrixArsenal`
- `AtomicNaturalMatrixArsenal.atomicDefect_eq_zero`
- `bigradedBettiHodge_of_atomicNaturalMatrixArsenal`

### `GSTClassicalHodgeAtomicNaturalLefschetzNonCircularity.lean`
- `bareTwoSlotLefschetzHodge`
- `bareTwoSlotLefschetzHodge_eq_scaled_matrixUnit`
- `targetBasis_algebraic_of_atomicNatural_bareLefschetz`
- `no_atomicNatural_bareLefschetz_to_separatorSheet`

This last file is a hard mathematical firewall. Preserve the theorem statements: it proves that primitive compression does not magically weaken the missing geometry.

## Files that must remain intact

- `GSTClassicalHodgeStage2GSemanticRigidity.lean`
- `GSTClassicalHodgeSpineSemanticSeparation.lean`
- `GSTClassicalHodgeGenuineCycleClassGeometry.lean`
- `GSTClassicalHodgeAtomicDefectTomographyGhost.lean`
- `GSTClassicalHodgeAtomicDefectTomographySynchronization.lean`
- `GSTClassicalHodgeAtomicDefectOperatorDescent.lean`
- `GSTClassicalHodgeAtomicDefectEquivariantIrreducibility.lean`
- `GSTClassicalHodgeAtomicNaturalLefschetzNonCircularity.lean`
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
- do not promote the bare `L^2` primitive to automatic native/atomic naturality: the new audit proves that would force target algebraicity;
- do not delete semantic-rigidity or noncircularity audits;
- if `Submodule.liftQ`, quotient induction, linear-map coercions, `map_sub`, or namespace APIs differ in pinned Mathlib, repair those bodies surgically while preserving statements.

The assistant lane now audits/derives only genuinely weaker geometric statements below the bare-Lefschetz interface and reconciles CI in parallel.

## CI target

The branch workflow `.github/workflows/hodge-conjecture.yml` should compile the transformed defect/equivariance layers explicitly and compile `GSTClassicalHodgeTwoBurstClosureReceipt.lean`, which imports the new bare-Lefschetz firewall. Preserve green older modules.