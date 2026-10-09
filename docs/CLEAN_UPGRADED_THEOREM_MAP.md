# HC-PROOF — Clean Upgraded-Theorem Branch (2026-10-09)

**Branch:** `clean/upgraded-advanced-only-20261009`
**Advanced source snapshot:** `8451234` on `sol/hodge-strict-betti-correspondence-fusion-20261003` (the SB-138 cure state: astra's clean-branch cures + the 7-residual completion).
**History policy:** the content of 800+ development commits is presented in ONE consolidation commit based on `main`; no theorem statements or proof bodies are altered by this consolidation. The original development branches retain the full detailed history.

## The upgrade rule (what stays, what goes)

A file **stays** exactly when it is part of the *current* advanced dependency
closure — that is, when at least one of the following holds:

1. it is a registered Lake root (a named landing surface of the theory), or
2. some other current file imports it.

A file **goes** when it is neither: it is compiled by nothing, imported by
nothing, and registered nowhere. In this snapshot that applied to exactly
three debris items, which are removed:

| Removed | Reason |
|---|---|
| `fsb.lean` | 09-27 scratch experiment; no importer, no registration |
| `pi.lean` | 09-27 scratch experiment; no importer, no registration |
| `questions/deepmind_problem_406/` | 09-20 test debris; no importer, no registration |

**The V1/V2 law** (same as the sibling clean branch): a `V2` name never makes
its `V1` base deletable. `CardinalWorldsV2.lean` *imports* `CardinalWorlds.lean`;
the upgrade is an extension, and the import graph — not the filename — decides.
Old-looking files that are still imported by upgraded modules stay, because
deleting them would break the actual dependency closure.

## The 17 newly-mapped advanced modules

These advanced finale/landing modules existed in the development tree but were
never wired into any build (no importer, no Lake root, no workflow target).
This branch **registers all 17 as `HodgePureMath` Lake roots** so the hosted CI
compiles them for the first time — nothing advanced stays invisible:

`CanonicalCutSpineNormalization`, `GhostIndexedCriterionCircularity`,
`HandwrittenPiExplicitNativeCollapse`, `HandwrittenPiProgramLanding`,
`OmniversePointStrictRelationFinale`, `PiOneObservableOmniverseFinale`,
`PiPointFiniteCorrespondenceUltimateFinale`,
`PiPointRationalCorrespondenceUnboundedFinale`,
`PiPointTwoGeneratorUnboundedFinale`, `PiSpineMassUnboundedFinale`,
`PiSpineTwoGeneratorUnboundedFinale`, `PiStrictKernelCyclicOmniverseFinale`,
`PiStrictTraceCyclicOmniverseFinale`, `PointClosureIntegral`,
`RadicalPrincipalCutDimension`, `SheetSiegeRoute`, `StrictBettiApexL2Fusion`.

All 17 carry **zero `sorry`** in their statements' dependency surface as
authored; the hosted build is the sole verifier of that.

## Mathematical complexity map

| Lane | File/module families | Role |
|---|---|---|
| Foundations | `CardinalWorlds*`, `GSTGraphV2*`, `GSTWorldtrace*` | Ontology/address/digit/worldtrace primitives and refinements |
| Wave/operator universe | `waves/*`, `GSTUniversalLefschetz*`, `GSTWorld*` | Wave/cohomology, recoordination, operator structures |
| Geometric realization | `GSTGeometricRealizationStage2*`, `GSTProjectiveOverC`, `GSTNativeCodimensionCyclePresentation` | Smooth-projective/codimension-cycle interfaces |
| Correspondence engine | `GSTClassicalHodge*Correspondence*`, `*NativeOperator*`, `*KernelStableOperatorAlgebra*` | Operator actions, cycle-class naturality, kernel-stable block algebra, invertible triangular feedback |
| Point/projective geometry | `GSTClassicalHodge*Point*`, `*PrincipalCut*`, `*Projective*`, `*NativeMassBridgeAudit*` | Projective point constructions, cut/seed audits |
| Fibered native machinery | `*FiberedNative*`, `*SynchronizedSeedFiberedLanding*`, `*PointwiseNativeCosmicClosure*` | Fibered addresses, lifts, cosmic closure of native point lifts |
| GST plane/frontier | `*PlaneCompleteness*`, `*GSTProjectiveWordExactFinale*`, `*GSTRationalCorrespondenceExactFinale*`, `*FullCorrespondenceGSTPlaneCompletion*` | Highest-level landing obligations |
| Final integration | `HodgeConjecture.lean`, `GSTClassicalHodgeStrictBettiApexL2Fusion`, the 17 newly-registered finales | The landing surface compiled by the integration gate |

## Hosted verification

Only GitHub Actions runs Lean (the standing law of this mission: no local
toolchain). This branch triggers the **Hodge Conjecture Final Integration
Gate** on push. Compilation of the full library plus the finale surface is
claimed green **only when the associated GitHub Actions run completes
successfully**.
