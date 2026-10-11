# HC-PROOF clean branch — all-history gap audit

Audit target: `clean/upgraded-advanced-only-20261009` at theorem snapshot
`59d4e4cf` (the subsequent CI-only commit does not change Lean sources).

This is a static Git-history and declaration inventory.  It does not install
or run Lean locally.  Lean validity is established only by GitHub Actions.

## Current result

The branch is a useful dependency-clean snapshot, but it is not yet an
all-history theorem consolidation.

- Lean files in the branch: **581**.
- Divergent remote refs inspected: **78**, representing **47 unique tips**.
- Absent paths that introduce declaration names not found in the clean branch:
  **218**.
- Retained paths whose divergent variants introduce declaration names not
  found in the clean branch: **140**.
- Absent unqualified declaration names detected: **2,282**.
  - **1,973** occur in absent paths.
  - **309** occur in historical variants of retained paths.
- After excluding the four intentional scratch/test debris files documented
  in `CLEAN_UPGRADED_THEOREM_MAP.md`, **214 absent source paths with missing
  declarations remain**.

Declaration-name comparison is a conservative routing heuristic, not a
semantic equivalence proof.  Renamed theorems can make the real migration
surface larger, while repeated unqualified names can make it look smaller.

## Proven canonical lineage

The separator/first-failure line is ordered by Git ancestry and file-set
changes:

1. `sol/hodge-single-separator-successor`
2. `sol/hodge-first-ghost-incidence-construction-20261002`
3. `sol/hodge-math-frontier-closure-20261002`
4. `sol/hodge-principal-cut-first-failure-bridge-20261004`

The canonical migration source is the final tip `ed02aa25`.  Compared with
the clean branch it contains **153 absent Lean paths**, or **149** after
excluding the four declared debris paths.  Of those 149 sources, **147**
introduce unqualified declaration names absent from the clean branch.  The
remaining two are receipts/smokes or repeat declarations present elsewhere.

The final lineage tip must be used instead of a raw union: the math-frontier
step intentionally deleted files from its predecessor, so unioning every tip
would restore superseded modules.

The eight explicit deletions are:

- `GSTClassicalHodgeCorrespondenceGhostGaugeFreedom.lean`
- `GSTClassicalHodgeCorrespondenceOrbitExactness.lean`
- `GSTClassicalHodgeCorrespondenceRangeRigidityFrontier.lean`
- `GSTClassicalHodgeFirstFailureReturnExactness.lean`
- `GSTClassicalHodgeFirstGhostPacketExactness.lean`
- `GSTClassicalHodgeOneExactSuccessorFlagNormal.lean`
- `GSTClassicalHodgeSchemeFiniteCorrespondenceFirewall.lean`
- `GSTClassicalHodgeSchemeFiniteFirstGhostGate.lean`

The current tree independently contains a newer, GitHub-focused-green
`GSTClassicalHodgeSchemeFiniteCorrespondenceFirewall.lean`; that canonical
upgrade stays.  The other seven deleted modules are explicit supersession
tombstones and must not be restored by an all-history union.

After fixing that supersession choice, a constrained set-cover audit routes
all **207** remaining absent source paths with missing declarations through
18 canonical/independent heads:

| Migration head | Newly covered paths |
|---|---:|
| principal-cut first-failure bridge | 147 |
| minimal-ghost single transport | 17 |
| strict-Betti total fusion | 7 |
| primitive geometric quotient | 6 |
| limitless genuine closure | 6 |
| GST cosmology strengthening | 5 |
| Hodge final integration | 3 |
| limitless phase 1 | 2 |
| limitless cosmology | 2 |
| cyclic omniversal closure | 2 |
| universal Pascal-Lefschetz | 2 |
| canonical successor non-erasure | 2 |
| cohomology faithfulness | 1 |
| legacy absorption | 1 |
| sharp spectrum | 1 |
| Lefschetz path | 1 |
| primitive algebraic annihilator | 1 |
| strict-Betti trace fusion | 1 |

This covers absent-file migration only.  The 140 retained-path historical
variants still need declaration-by-declaration semantic porting.

Highest-priority retained-path variants by absent declaration-name count:

| Retained canonical path | Missing names | Primary historical source |
|---|---:|---|
| `GSTGeometricRealizationStage2G.lean` | 18 | GST cosmology strengthening |
| `GSTTruncatedWorldCohomologyRing.lean` | 9 | GST cosmology strengthening |
| `GSTClassicalHodgeGeneralSpaceRealization.lean` | 8 | general-space cosmology |
| `GSTClassicalHodgeGeneratorwiseAtomicStability.lean` | 8 | Hodge branch family |
| `GSTGeneralSpace.lean` | 8 | general-space cosmology |
| `GSTGraphV2GeneralSpaceRealization.lean` | 8 | general-space cosmology |
| `CardinalWorldsV2.lean` | 7 | GST cosmology strengthening |
| `GSTClassicalHodgeRangeLiftedSpectralOperator.lean` | 7 | early Hodge engine |
| `waves/GSTWaveCohomology.lean` | 6 | GST cosmology strengthening |
| `waves/GSTNCohomologyV2.lean` | 6 | GST cosmology strengthening |
| `waves/GSTNCohomology.lean` | 6 | GST cosmology strengthening |
| `GSTClassicalHodgeGeneralSpaceSynchronization.lean` | 6 | general-space cosmology |
| `GSTClassicalHodgePointKernelOperatorLift.lean` | 6 | Hodge branch family |
| `GSTClassicalHodgeFiniteClosedCorrespondenceOperator.lean` | 6 | principal-cut lineage |
| `GSTGlobalPureHodgeCosmology.lean` | 6 | GST cosmology strengthening |

The concrete declaration names for the first migration wave are recorded in
[`CLEAN_RETAINED_VARIANT_MIGRATION.md`](CLEAN_RETAINED_VARIANT_MIGRATION.md).

At `ed02aa25`, 108 of the absent non-debris modules are registered Lake roots,
113 are imported by another module, and only 17 are neither.  Therefore most
of this gap is an active historical theorem surface, not unreferenced scratch.

## Independent migration heads

These histories are not ancestors of the principal-cut line and require
separate semantic classification:

- `sol/hodge-minimal-ghost-single-transport`
- `sol/hodge-primitive-quotient-attack`
- `sol/hodge-primitive-geometric-quotient`
- `sol/hodge-primitive-algebraic-annihilator`
- `sol/hodge-strict-betti-total-fusion-20261003`
- `sol/hodge-strict-betti-trace-fusion-20261003`
- `sol/hodge-strict-betti-trace-pushpull-20261003`
- `sol/hodge-general-space-cosmology-20261003`
- `sol/hodge-limitless-genuine-closure`
- `sol/hodge-cyclic-omniversal-closure`
- `sol/hodge-canonical-successor-nonerasure`
- `sol/limitless-cosmology-phase1`
- `sol/limitless-cosmology`
- `sol/limitless-universe-repo-upgrade`
- `sol/limitless-cosmology-universalization`
- the early sharp-spectrum, legacy-absorption, cohomology-faithfulness,
  universal-Pascal, and cosmology-next branches.

`GSTLimitlessWorld.lean` and `GSTLimitlessCosmology.lean` are parallel
foundations with different APIs (finite-window reconstruction versus compact
to global carrier transport); neither semantically replaces the other.

## Consolidation decision still required

For declarations superseded by a renamed or strengthened theorem, choose one
policy before source migration:

1. retain the historical theorem name as a thin alias/corollary inside the
   canonical upgraded module; or
2. remove the historical name and rewrite every consumer to the canonical
   theorem.

Both policies remove superseded implementation files.  The alias/corollary
policy is safer for a history-wide consolidation because it preserves theorem
discoverability and downstream API compatibility without retaining duplicate
proof bodies.
