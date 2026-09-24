# Limitless Universe Repository Upgrade Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Upgrade HC-PROOF from arbitrarily extensible finite worlds to a rigorously unbounded cosmology with exact finite-window recovery, unrestricted operators, functorial cohomology, strengthened Hodge/Lefschetz/duality structure, and first-class abstract algebraic geometry, while preserving the external semantics of Stage 2.

**Architecture:** Introduce a compact algebraic cosmos based on finitely supported fields over `Nat × Nat` and a distinct completed observational cosmos based on compatible finite windows. Existing finite `A × B` worlds become exact observations/quotients/specializations. The migration proceeds bottom-up so every batch has a real Lean compile gate before dependent layers move.

**Tech Stack:** Lean 4.33.0-rc2, Mathlib `v4.33.0-rc2`, Lake, GitHub Actions, existing HC comparator/gates.

**Spec:** `docs/superpowers/specs/2026-09-24-limitless-cosmology-repo-upgrade-design.md`

## Global Constraints

- No theorem weakening to fit the new architecture.
- No new `sorry`, `admit`, or custom axiom used to manufacture strength.
- No false identification between finite-support/direct-limit and completed/inverse-limit constructions.
- Finite boundary laws remain exact local/window theorems when mathematically real.
- The classical Hodge conjecture boundary remains explicit: internal GST results are not silently identified with arbitrary smooth projective complex varieties.
- Historical names remain compatibility theorems/corollaries until dependents compile against the stronger formulation.
- Work only in `kyo-oo/HC-PROOF`, branch `sol/limitless-universe-repo-upgrade`.
- Each task ends with a direct `lake build` target set and no-proof-escape scan before the next task begins.

## Review Focus

1. **Support escapes finite windows:** restriction/extension round-trips must require or prove the precise support hypothesis rather than silently truncate data.
2. **Zero-sized worlds:** definitions parameterized by finite dimensions must not assume positivity unless the theorem genuinely needs it.
3. **Compact versus completed confusion:** no theorem may derive unrestricted global data from finite support without an explicit embedding/closure argument.
4. **Operator/window naturality at the boundary:** shifts crossing a finite edge must be characterized as truncation, not falsely equal to global shift output.
5. **Stage-2 semantic leakage:** new GST coordinate or cohomology structures must not be treated as actual scheme cohomology without an explicit realization map.

---

## Repository Migration Matrix

### Foundations and local laws
`CardinalWorlds.lean`, `CardinalWorldsV2.lean`, `CardinalWorldsPrefixClassifier.lean`, `GSTWorldCosmology.lean`, `GSTRadixWorldDynamics.lean`, `GST2DMixedEmergence.lean`, `GST2DMixedEmergenceUpgrade.lean`, `GSTCanonicalCarryDynamics.lean`, `GSTCanonicalSevenAxisBridge.lean`, `GSTCanonicalTailLTE.lean`, `GSTCanonicalTailStateIso.lean`, `GSTGraphV2Ontological.lean`, `GSTGraphV2Production.lean`, `GSTGraphV2ProductionLaws.lean`, `GSTGraphV2ScaleEquivariance.lean`, `GSTGraphV2SixAdicOntologicalGeometry.lean`, `GSTGraphV2SixAdicOntologicalGeometryLaws.lean`, `GSTV2InfiniteCore.lean`.

### Address/recoordination/infinite reconstruction
`GSTWorldRecoordinationGroupoid.lean`, `GSTUniversalAddressBridge.lean`, `GSTCoherentCosmology.lean`, `GSTInfiniteWorldClassification.lean`, `GSTInfiniteBadTransport.lean`, `GSTInfiniteCollision.lean`, `GSTInfiniteCoupledLedger.lean`, `GSTInfiniteFourPowerNavigation.lean`, `GSTInfiniteGateTransport.lean`, `GSTClimbInfiniteFamily.lean`, `GSTClimbTruthValue.lean`, `GSTTowerAxis.lean`, `GSTTowerFire.lean`.

### Operators, graded algebra, quotient geometry
`GSTUniversalLefschetzCosmology.lean`, `GSTUniversalLefschetzDynamics.lean`, `GSTUniversalLefschetzPathFormula.lean`, `GSTUniversalLefschetzKernel.lean`, `GSTUniversalLefschetzCausalGeometry.lean`, `GSTGradedWorldAlgebra.lean`, `GSTTruncatedWorldCohomologyRing.lean`, `GSTWorldPoincareDuality.lean`, `GSTLefschetzPoincareReciprocity.lean`, `GSTPureHodgeLefschetzKernel.lean`, `GSTSquarePureHodgeDuality.lean`, `GSTWorldCrownBridge.lean`.

### Wave/topology/cohomology
`GSTBladeWave.lean`, `GSTTailFFourthDimension.lean`, `GSTTailFInfiniteRead.lean`, `GSTTailFOneLane.lean`, `GSTTailFProof.lean`, `GSTGraphV2OmegaWaveLaw.lean`, `GSTGraphV2CanonicalNWave.lean`, `GSTGraphV2CanonicalPhaseSteering.lean`, `GSTGraphV2CanonicalRenormalization.lean`, `GSTGraphV2CanonicalSheetTranslation.lean`, `GSTGraphV2NonEuclidean.lean`, `GSTGraphV2NonEuclideanLaws.lean`, `GSTGraphV2NonlocalCascade.lean`, `waves/CardinalWorldsPostulateLaw.lean`, `waves/CardinalWorldsPostulateLawV2.lean`, `waves/GSTWaveCohomology.lean`, `waves/GSTWaveCohomologyV2.lean`, `waves/GSTNCohomology.lean`, `waves/GSTNCohomologyV2.lean`, `waves/GSTVortexSingularity.lean`, `waves/GSTVortexSingularityV2.lean`.

### Hodge/analytic/finite-classification stack
`GSTDimensionFreeHodgeDiagonal.lean`, `GSTGlobalPureHodgeCosmology.lean`, `HodgeDeRhamBridge.lean`, `HodgeDeRhamBridgeV2.lean`, `GSTAnalyticAbsorption.lean`, `GSTAnalyticAbsorptionV2.lean`, `GSTLefschetzCrown.lean`, `GSTLefschetzCrownV2.lean`, `GSTHodgeAssault.lean`, `GSTHodgeAssaultV2.lean`, `GSTClayOfficial.lean`, `GSTClayOfficialV2.lean`, `GSTTransferBridge.lean`, `GSTTransferBridgeV2.lean`.

### Stage 2 / actual algebraic geometry
`GSTProjectiveOverC.lean`, `GSTGeometricRealizationStage2.lean`, `GSTGeometricRealizationStage2B.lean`, `GSTGeometricRealizationStage2C.lean`, `GSTGeometricRealizationStage2D.lean`, `GSTGeometricRealizationStage2E.lean`, `GSTGeometricRealizationStage2F.lean`, `GSTGeometricRealizationStage2G.lean`.

### Historical/specialized theorem families to audit after core migration
All `GSTFourPower*.lean`, `GSTPrefixOne*.lean`, `GSTU2D*.lean`, `GSTGraphV2Canonical*.lean`, `GSTGraphV2FourPower*.lean`, `GSTGraphV2Handwritten*.lean`, `GSTGraphV2PerfectPower*.lean`, `GSTGraphV2SixAdic*.lean`, `GSTGraphV2Unified*.lean`, `GSTFinal*.lean`, `GSTGhostRayExclusion.lean`, `GSTPerfectPowerTailNavigation.lean`, `GSTSeedOneShift.lean`, `GSTTheAct.lean`, `GSTTheActConstruction.lean`, `GSTWorldtraceArithmetic.lean`, `GSTWorldtraceMahlerRelativePrecision.lean`, scratch/information modules registered by `lakefile.toml`, comparator fixtures, `MonolithBoundary.lean`, and `HCProof.lean`.

---

### Task 1: Limitless world and exact finite-window interface

**Files:**
- Create: `GSTLimitlessWorld.lean`
- Modify: `GSTWorldCosmology.lean`
- Modify: `lakefile.toml`
- Modify: `HCProof.lean`

**Interfaces:**
- Produces `CosmicCell := Nat × Nat`, compact coefficient fields, finite-window inclusion/restriction, support-in-window predicate, and exact round-trip theorems.
- Existing `WorldCell A B` / `WorldCoef A B` remain stable APIs and become the finite-window face.

- [ ] Write compile-time theorem probes in `GSTLimitlessWorld.lean` for `restrict (extend f) = f`, support-controlled `extend (restrict g) = g`, zero-sized windows, and nested restriction coherence.
- [ ] Run `lake build GSTLimitlessWorld` and confirm RED before the definitions exist.
- [ ] Implement the compact cosmos and window maps using existing Mathlib finitely-supported functions and explicit `Fin` bounds.
- [ ] Integrate the new foundation into `GSTWorldCosmology.lean` without removing historical theorem names.
- [ ] Run `lake build GSTLimitlessWorld GSTWorldCosmology` and require PASS.
- [ ] Run `grep -nE '^[[:space:]]*(axiom|sorry|admit)[[:space:]]' GSTLimitlessWorld.lean GSTWorldCosmology.lean` and require no new proof escape.
- [ ] Commit: `feat: add limitless world and exact finite windows`.

### Task 2: Completed observational universe and reconstruction

**Files:**
- Create: `GSTCompletedWorld.lean`
- Modify: `GSTCoherentCosmology.lean`
- Modify: `GSTInfiniteWorldClassification.lean`
- Modify: `lakefile.toml`
- Modify: `HCProof.lean`

**Interfaces:**
- Consumes finite-window restriction from Task 1.
- Produces compatible finite observations, canonical compact-to-completed embedding, observation separation, and reconstruction hooks aligned with `WindowTower`.

- [ ] Add theorem probes for restriction compatibility and injectivity of the compact embedding.
- [ ] Run `lake build GSTCompletedWorld` and confirm RED.
- [ ] Implement the compatible-window object and canonical observation maps.
- [ ] Bridge current `WindowTower`/stream classification to the new observation layer without claiming an invalid compact/completed equivalence.
- [ ] Run `lake build GSTCompletedWorld GSTCoherentCosmology GSTInfiniteWorldClassification`.
- [ ] Commit: `feat: add completed observation cosmology`.

### Task 3: Limitless address geometry and chart calculus

**Files:**
- Modify: `GSTUniversalAddressBridge.lean`
- Modify: `GSTWorldRecoordinationGroupoid.lean`
- Modify: `GSTRadixWorldDynamics.lean`

**Interfaces:**
- Produces compact limitless address space, exact cell/address equivalence, finite-address restriction, and naturality under finite recoordination.

- [ ] Add probes for cosmic cell/address round-trips and finite-window compatibility.
- [ ] Run the three-module build expecting RED for new theorem names.
- [ ] Implement compact address equivalence and strengthen chart/reindexing laws.
- [ ] Preserve `Fin N → ℤ` and historical twelve-address theorems as specializations.
- [ ] Run `lake build GSTUniversalAddressBridge GSTWorldRecoordinationGroupoid GSTRadixWorldDynamics`.
- [ ] Commit: `feat: lift addresses and recoordination to limitless cosmos`.

### Task 4: Unrestricted shifts and limitless Lefschetz operator

**Files:**
- Modify: `GSTUniversalLefschetzCosmology.lean`
- Modify: `GSTUniversalLefschetzDynamics.lean`
- Modify: `GSTUniversalLefschetzPathFormula.lean`
- Modify: `GSTUniversalLefschetzKernel.lean`
- Modify: `GSTUniversalLefschetzCausalGeometry.lean`

**Interfaces:**
- Produces global commuting shifts on compact cosmic coefficients, unrestricted `L = H + V`, arbitrary-power path expansion, exact unbounded causal kernel, and finite-window truncation corollaries.

- [ ] Add theorem probes for additive iteration, commutation, non-nilpotence witness at arbitrary depth, path expansion, and exact kernel coefficient.
- [ ] Run the five-module build and confirm RED on new probes.
- [ ] Implement global operators by translation on `Nat × Nat` finite support.
- [ ] Re-express finite nilpotence as finite-window disappearance rather than global extinction.
- [ ] Run the five-module build plus `GSTWorldCosmology`.
- [ ] Commit: `feat: make Lefschetz evolution unbounded`.

### Task 5: Universal coordinate algebra and finite quotient geometry

**Files:**
- Create: `GSTUniversalCoordinateAlgebra.lean`
- Modify: `GSTGradedWorldAlgebra.lean`
- Modify: `GSTTruncatedWorldCohomologyRing.lean`
- Modify: `lakefile.toml`
- Modify: `HCProof.lean`

**Interfaces:**
- Produces the two-generator commutative coordinate algebra, bigrading, monomial/world-cell dictionary, finite truncation ideals, and quotient-specialization maps.

- [ ] Add probes that monomial `(C,d)` matches world basis cell `(C,d)`, and that finite quotient kills precisely boundary-crossing monomials.
- [ ] Run `lake build GSTUniversalCoordinateAlgebra GSTTruncatedWorldCohomologyRing` expecting RED.
- [ ] Implement the polynomial/monomial model using Mathlib polynomial APIs that compile under RC2.
- [ ] Prove generic truncation support criterion and connect existing finite cohomology ring.
- [ ] Run `lake build GSTUniversalCoordinateAlgebra GSTGradedWorldAlgebra GSTTruncatedWorldCohomologyRing`.
- [ ] Commit: `feat: add universal GST coordinate algebra`.

### Task 6: Topology of finite observation

**Files:**
- Create: `GSTObservationTopology.lean`
- Modify: `GSTCoherentCosmology.lean`
- Modify: `GSTInfiniteWorldClassification.lean`
- Modify: `lakefile.toml`
- Modify: `HCProof.lean`

**Interfaces:**
- Produces the observation topology, continuity of finite-window maps, separation of completed states, and topological compatibility with stream worlds where available.

- [ ] Add continuity/separation theorem probes.
- [ ] Run build expecting RED.
- [ ] Implement the weakest exact Mathlib topology sufficient for cylinder/finite-observation continuity; do not claim compactness unless proved.
- [ ] Run `lake build GSTObservationTopology GSTCoherentCosmology GSTInfiniteWorldClassification`.
- [ ] Commit: `feat: topologize finite observations`.

### Task 7: Functorial cohomology across windows

**Files:**
- Modify: `waves/GSTWaveCohomology.lean`
- Modify: `waves/GSTWaveCohomologyV2.lean`
- Modify: `waves/GSTNCohomology.lean`
- Modify: `waves/GSTNCohomologyV2.lean`
- Modify: `waves/GSTVortexSingularity.lean`
- Modify: `waves/GSTVortexSingularityV2.lean`
- Modify: `GSTBladeWave.lean`

**Interfaces:**
- Produces window extension/restriction maps commuting with coboundary/source/row-class transport, plus compact-support compatibility.

- [ ] Add naturality probes for coboundary and row-class maps under window inclusion.
- [ ] Run wave/cohomology targets expecting RED.
- [ ] Implement window-indexed maps and naturality theorems without changing existing finite cohomology results.
- [ ] Run all seven targets.
- [ ] Commit: `feat: make GST cohomology window-functorial`.

### Task 8: Omega/TailF/wave propagation without terminal chart walls

**Files:**
- Modify: `GSTGraphV2OmegaWaveLaw.lean`
- Modify: `GSTTailFFourthDimension.lean`
- Modify: `GSTTailFInfiniteRead.lean`
- Modify: `GSTTailFOneLane.lean`
- Modify: `GSTTailFProof.lean`
- Modify: `GSTGraphV2CanonicalNWave.lean`
- Modify: `GSTGraphV2CanonicalPhaseSteering.lean`
- Modify: `GSTGraphV2CanonicalRenormalization.lean`
- Modify: `GSTGraphV2CanonicalSheetTranslation.lean`

**Interfaces:**
- Produces arbitrary-depth propagation theorems and explicit window-loss formulations for effects previously phrased as terminal extinction.

- [ ] Add arbitrary-time/depth probes and finite-window compatibility probes.
- [ ] Run affected targets expecting RED.
- [ ] Lift propagation proofs using Tasks 1–7 structures; preserve local carry/current laws exactly.
- [ ] Run all affected targets.
- [ ] Commit: `feat: remove artificial terminal walls from wave cosmology`.

### Task 9: Infinite Hodge diagonal and pure sector

**Files:**
- Modify: `GSTDimensionFreeHodgeDiagonal.lean`
- Modify: `GSTGlobalPureHodgeCosmology.lean`
- Modify: `GSTPureHodgeLefschetzKernel.lean`
- Modify: `GSTSquarePureHodgeDuality.lean`

**Interfaces:**
- Produces a weight-`p` cosmic Hodge generator for every `p`, compact pure sector equivalence with finitely supported diagonal coordinates, and exact finite-window truncation recovery.

- [ ] Add probes for arbitrary `p`, rank-one cosmic weight class, pure-sector coordinate equivalence, and finite cutoff recovery.
- [ ] Run the four-module build expecting RED.
- [ ] Implement the infinite diagonal on the compact cosmos and connect it to global Lefschetz paths.
- [ ] Run the four-module build.
- [ ] Commit: `feat: extend Hodge cosmology to every weight`.

### Task 10: Honest duality in the limitless universe

**Files:**
- Modify: `GSTWorldPoincareDuality.lean`
- Modify: `GSTLefschetzPoincareReciprocity.lean`
- Modify: `GSTWorldCrownBridge.lean`

**Interfaces:**
- Produces translated/relative finite-window duality and, where Lean support is sufficient, compact-support/completed pairing; preserves every historical finite perfect pairing.

- [ ] Add translation/window naturality probes and complementary-sector pairing probes.
- [ ] Run targets expecting RED.
- [ ] Implement relative duality without inventing a global top cell.
- [ ] Run all three targets.
- [ ] Commit: `feat: make Poincare duality relative and limitless-compatible`.

### Task 11: Cardinal/local ontology migration

**Files:**
- Modify: `CardinalWorlds.lean`
- Modify: `CardinalWorldsV2.lean`
- Modify: `CardinalWorldsPrefixClassifier.lean`
- Modify: `GST2DMixedEmergence.lean`
- Modify: `GST2DMixedEmergenceUpgrade.lean`
- Modify: `GSTGraphV2ScaleEquivariance.lean`
- Modify: `GSTGraphV2Ontological.lean`
- Modify: `GSTGraphV2Production.lean`
- Modify: `GSTGraphV2ProductionLaws.lean`

**Interfaces:**
- Recasts local laws as natural laws over limitless/window embeddings while preserving exact 12-cell physics.

- [ ] Add naturality probes for local transition/current/emergence equations under finite-window embedding.
- [ ] Run target set expecting RED.
- [ ] Integrate limitless interfaces into existing theorem bodies rather than adding wrapper-only duplicates.
- [ ] Run target set.
- [ ] Commit: `refactor: integrate local GST ontology with limitless universe`.

### Task 12: Analytic, de Rham, finite Hodge, Clay, and transfer migration

**Files:**
- Modify: `HodgeDeRhamBridge.lean`
- Modify: `HodgeDeRhamBridgeV2.lean`
- Modify: `GSTAnalyticAbsorption.lean`
- Modify: `GSTAnalyticAbsorptionV2.lean`
- Modify: `GSTLefschetzCrown.lean`
- Modify: `GSTLefschetzCrownV2.lean`
- Modify: `GSTHodgeAssault.lean`
- Modify: `GSTHodgeAssaultV2.lean`
- Modify: `GSTClayOfficial.lean`
- Modify: `GSTClayOfficialV2.lean`
- Modify: `GSTTransferBridge.lean`
- Modify: `GSTTransferBridgeV2.lean`

**Interfaces:**
- Makes every finite certificate visibly a specialization/realization of the limitless structures while preserving exact historical finite statements and rational/integral distinctions.

- [ ] Add specialization probes from limitless Hodge/operator/address structures to current finite certificates.
- [ ] Run upgraded cosmology gate target list expecting RED on new probes.
- [ ] Rewrite internals to consume the stronger interfaces, preserving public theorem names.
- [ ] Run all 12 targets.
- [ ] Commit: `refactor: absorb limitless cosmology into Hodge and transfer stack`.

### Task 13: Abstract algebraic geometry and Stage-2 realization interfaces

**Files:**
- Modify: `GSTProjectiveOverC.lean`
- Modify: `GSTGeometricRealizationStage2.lean`
- Modify: `GSTGeometricRealizationStage2B.lean`
- Modify: `GSTGeometricRealizationStage2C.lean`
- Modify: `GSTGeometricRealizationStage2D.lean`
- Modify: `GSTGeometricRealizationStage2E.lean`
- Modify: `GSTGeometricRealizationStage2F.lean`
- Modify: `GSTGeometricRealizationStage2G.lean`
- Modify: `GSTUniversalCoordinateAlgebra.lean`

**Interfaces:**
- Produces explicit ring/quotient/geometric realization maps from finite GST coordinate sectors into the actual scheme/cohomology/cycle-class setting; does not alter external semantics or hide realization obligations.

- [ ] Add compile-time probes proving realization certificates consume arbitrary finite windows/diagonal ranges rather than hard-coded twelve-address data where that restriction is artificial.
- [ ] Run Stage-2 target set expecting RED.
- [ ] Strengthen coordinate-ring and quotient interfaces to actual Mathlib algebraic-geometry objects only where explicit maps compile.
- [ ] Preserve `Stage2*RealizationObligation` as named obligations unless a genuine proof discharges them.
- [ ] Run all Stage-2 modules plus `GSTProjectiveOverC`.
- [ ] Commit: `feat: strengthen GST algebraic geometry realization interfaces`.

### Task 14: Specialized theorem-family absorption audit

**Files:**
- Modify as required: every registered `GSTFourPower*.lean`, `GSTPrefixOne*.lean`, `GSTU2D*.lean`, `GSTGraphV2Canonical*.lean`, `GSTGraphV2FourPower*.lean`, `GSTGraphV2Handwritten*.lean`, `GSTGraphV2PerfectPower*.lean`, `GSTGraphV2SixAdic*.lean`, `GSTGraphV2Unified*.lean`, `GSTFinal*.lean`, `GSTGhostRayExclusion.lean`, `GSTPerfectPowerTailNavigation.lean`, `GSTSeedOneShift.lean`, `GSTTheAct.lean`, `GSTTheActConstruction.lean`, `GSTWorldtraceArithmetic.lean`, `GSTWorldtraceMahlerRelativePrecision.lean`, `MonolithBoundary.lean`, information/scratch modules registered by `lakefile.toml`.

**Interfaces:**
- Every specialized theorem either becomes stronger through the limitless interfaces or is explicitly retained as an exact finite/local theorem; no registered production module remains conceptually disconnected by accident.

- [ ] Enumerate every registered root from `lakefile.toml` and mark it `changed-strengthened`, `changed-integration`, or `already-unbounded/no semantic edit` in an audit document.
- [ ] For each file requiring migration, add the smallest theorem probe that demonstrates use of the new universal interfaces before implementation.
- [ ] Compile each changed module immediately after its edit.
- [ ] Run `lake build HCUniverse` after the family audit.
- [ ] Commit: `refactor: complete repo-wide limitless cosmology absorption`.

### Task 15: Full compiler, comparator, axiom, and documentation gate

**Files:**
- Modify: `HCProof.lean`
- Modify: `.github/workflows/cosmology-upgrade-gate.yml` only if needed to include new canonical modules in the permanent gate; do not add a temporary branch-only trigger to production history.
- Modify: `docs/HC_UNIVERSE_MAP.md`, `docs/GST_V2_OPERATING_MANUAL.md`, `README.md` only to reflect mathematics that is actually compiled.

**Interfaces:**
- Produces the final entry face and verification receipts.

- [ ] Run `git diff --check`.
- [ ] Run repository-wide no-proof-escape scan over production `.lean` files.
- [ ] Run `lake build HCUniverse`.
- [ ] Run `lake build HCProof`.
- [ ] Run `bash scripts/comparator.sh` and require literal `Your solution is okay!` and `=== COMPARATOR RESULT: PASS ===`.
- [ ] Inspect build/comparator logs for `sorryAx` in upgraded crowns.
- [ ] Update docs only after these receipts are green.
- [ ] Commit: `docs: publish limitless universe architecture and verification receipts`.

## Execution Rule

Use native/inline execution in the current session because no subagent execution tool is available. Do not pause between tasks unless an irreversible/destructive operation or shared-branch merge requires user action. Every compile failure is debugged on the same task before moving upward; no knowingly broken checkpoint is treated as complete.
