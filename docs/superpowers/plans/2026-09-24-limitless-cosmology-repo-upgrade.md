# Limitless Cosmology Repository Upgrade Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Refactor HC-PROOF so finite charts, finite Hodge ranges, truncated operator algebras, and bounded wave/cohomology structures become exact windows/quotients/specializations of a genuinely unbounded cosmology while preserving every valid finite theorem and strengthening the abstract algebraic-geometry interfaces.

**Architecture:** Build two infinite faces: a finite-support algebraic cosmos over `Nat × Nat` and a completed observational cosmos represented by coherent finite windows. Migrate addresses, chart changes, operators, cohomology, wave mechanics, Hodge/Lefschetz/duality, coordinate algebra, and Stage 2 realization upward from those foundations, with historical 4×3/Fin 12 theorems retained as exact specializations.

**Tech Stack:** Lean 4, Mathlib `v4.33.0-rc2`, Lake, GitHub Actions, existing HC-PROOF comparator/gate workflows.

**Spec:** `docs/superpowers/specs/2026-09-24-limitless-cosmology-repo-upgrade-design.md`

## Global Constraints

- Work only in `kyo-oo/HC-PROOF` on `sol/limitless-cosmology-universalization` until final integration.
- No new `sorry`, `axiom`, `opaque` proof escape, or custom hypothesis that manufactures theorem strength.
- Never weaken an existing exact theorem; preserve it or recover it as a specialization/corollary.
- Finite boundaries that encode real local geometry remain true as window/quotient/relative theorems; only artificial global ceilings are removed.
- Do not identify internal GST finite Hodge classification with arbitrary classical Hodge cohomology without actual Lean realization maps.
- Compile every coherent batch and run repository CI/gates before declaring it complete.

## Review Focus

- Empty/zero-sized windows: maps must remain total or carry explicit positivity hypotheses rather than silently using impossible `Fin` inhabitants.
- Support crossing a finite window: restriction-extension round trips must state the exact support condition and never claim an unconditional inverse.
- Infinite-vs-finite confusion: no theorem may infer global nilpotence or terminal Hodge weight from finite-window extinction.
- Reindexing/chart transport: grading, support, kernels, and Hodge diagonals must be natural only under maps that actually preserve the relevant structure.
- Stage 2 semantics: stronger GST algebra must not silently fill geometric realization obligations without constructing the required scheme/cohomology/cycle maps.

---

### Task 1: Limitless world foundation and finite-window calculus

**Files:**
- Create: `GSTLimitlessWorld.lean`
- Modify: `GSTWorldCosmology.lean`
- Modify: `HCProof.lean`
- Modify: `lakefile.toml`

**Interfaces:**
- Produces `CosmicCell := Nat × Nat`, `CosmicCoef R := CosmicCell →₀ R`, finite-window inclusion/restriction, support-in-window predicate, exact round trips, and 4×3 recovery.
- Consumed by Tasks 2–12.

- [ ] Add a compile probe importing `GSTLimitlessWorld` before the file exists; CI must fail because the module is missing.
- [ ] Implement the minimal limitless carrier and finite-window maps.
- [ ] Prove restriction-after-inclusion exactly; prove inclusion-after-restriction under support-in-window.
- [ ] Prove compatibility of nested restrictions and historical 4×3 recovery.
- [ ] Compile `GSTLimitlessWorld`, `GSTWorldCosmology`, and `HCProof`; then run the full cosmology upgrade gate.
- [ ] Commit the green batch.

### Task 2: Completed observation universe

**Files:**
- Create: `GSTCompletedWorld.lean`
- Modify: `GSTCoherentCosmology.lean`
- Modify: `GSTInfiniteWorldClassification.lean`
- Modify: `HCProof.lean`
- Modify: `lakefile.toml`

**Interfaces:**
- Consumes finite-window restriction from Task 1.
- Produces coherent rectangular observations, restriction coherence, global field-to-observation map, observation separation, and compact-to-completed embedding.

- [ ] Add compile probes for completed observation objects/theorems.
- [ ] Implement coherent window families without asserting an unjustified equivalence to finite-support data.
- [ ] Prove finite observations separate unrestricted global coefficient fields.
- [ ] Embed `CosmicCoef R` into the completed observation universe and prove injectivity.
- [ ] Relate the new construction to existing `WindowTower`/stream reconstruction where types genuinely align.
- [ ] Compile the affected modules and run the cosmology gate.
- [ ] Commit the green batch.

### Task 3: Limitless address and chart calculus

**Files:**
- Modify: `GSTUniversalAddressBridge.lean`
- Modify: `GSTWorldRecoordinationGroupoid.lean`
- Create: `GSTLimitlessAddress.lean`
- Modify: `HCProof.lean`
- Modify: `lakefile.toml`

**Interfaces:**
- Produces compact/completed address spaces, an explicit `Nat × Nat ≃ Nat` coding layer, finite address projections, and support-preserving chart transport.

- [ ] Add compile probes for infinite address round trips and finite-address specialization.
- [ ] Implement compact address equivalence and finite projection/reconstruction theorems.
- [ ] Add admissible reindexing transport and naturality statements for grading/projectors where valid.
- [ ] Recover `Fin 12 → ℤ` bridge exactly.
- [ ] Compile and run gate.
- [ ] Commit.

### Task 4: Unbounded shifts and limitless Lefschetz dynamics

**Files:**
- Create: `GSTLimitlessLefschetz.lean`
- Modify: `GSTUniversalLefschetzCosmology.lean`
- Modify: `GSTUniversalLefschetzDynamics.lean`
- Modify: `GSTUniversalLefschetzPathFormula.lean`
- Modify: `GSTUniversalLefschetzKernel.lean`
- Modify: `HCProof.lean`
- Modify: `lakefile.toml`

**Interfaces:**
- Produces unrestricted `H`, `V`, `L`, arbitrary iteration, commutation, exact binomial path expansion, exact causal kernel; finite nilpotence is recovered only after projection to a bounded window.

- [ ] Add compile probes showing arbitrarily deep global shifts and `L^n` are defined.
- [ ] Implement global shifts and prove iteration/commutation.
- [ ] Prove exact `L^n` binomial path formula.
- [ ] Prove limitless causal kernel with Manhattan time/binomial coefficient.
- [ ] Derive existing finite extinction/nilpotence from window restriction.
- [ ] Compile affected modules and run gate.
- [ ] Commit.

### Task 5: Universal coordinate algebra and quotient geometry

**Files:**
- Create: `GSTUniversalCoordinateAlgebra.lean`
- Modify: `GSTGradedWorldAlgebra.lean`
- Modify: `GSTTruncatedWorldCohomologyRing.lean`
- Modify: `HCProof.lean`
- Modify: `lakefile.toml`

**Interfaces:**
- Produces a two-generator commutative coordinate/operator algebra, bidegree/total degree, finite truncation ideals, quotient maps, and basis/world-cell correspondence.

- [ ] Add failing compile probes for generic truncation ideal membership and finite quotient recovery.
- [ ] Implement the coordinate algebra with Mathlib polynomial structures where robust.
- [ ] Prove generic support criterion for the ideal generated by finite horizontal/vertical bounds.
- [ ] Identify existing truncated world ring as the corresponding finite quotient/action.
- [ ] Compile and run gate.
- [ ] Commit.

### Task 6: Observation topology and completion

**Files:**
- Create: `GSTObservationTopology.lean`
- Modify: `GSTCoherentCosmology.lean`
- Modify: `GSTInfiniteWorldClassification.lean`
- Modify: `HCProof.lean`
- Modify: `lakefile.toml`

**Interfaces:**
- Produces cylinder/window observation topology, continuity of projections/translations where supported, and topological state separation.

- [ ] Add failing compile probes for continuity of finite observations.
- [ ] Implement the topology through existing Mathlib product/induced structures when practical.
- [ ] Prove observations separate states and continuity of core maps.
- [ ] Relate stream topology to existing ternary-stream world classification when available.
- [ ] Compile and run gate.
- [ ] Commit.

### Task 7: Cohomology and chain/cochain naturality

**Files:**
- Modify: `waves/GSTWaveCohomologyV2.lean`
- Modify: `waves/GSTNCohomologyV2.lean`
- Modify: `HodgeDeRhamBridge.lean`
- Modify: `HodgeDeRhamBridgeV2.lean`
- Create: `GSTLimitlessCohomology.lean`
- Modify: `HCProof.lean`
- Modify: `lakefile.toml`

**Interfaces:**
- Produces window-indexed chain/cochain compatibility, compact-support cohomological constructions where valid, and naturality under window/chart transport.

- [ ] Add failing probes for differential/restriction commuting laws.
- [ ] Generalize wave/cochain maps across window extension/restriction.
- [ ] Lift row classes/source decompositions/N-cohomology to the unbounded architecture where definitions support it.
- [ ] Prove naturality under address/recoordination maps.
- [ ] Compile and run wave/cohomology gates.
- [ ] Commit.

### Task 8: Wave, Omega, TailF, and coherent propagation

**Files:**
- Modify: `GSTBladeWave.lean`
- Modify: `GST2DMixedEmergence.lean`
- Modify: `GST2DMixedEmergenceUpgrade.lean`
- Modify: `GSTTailFFourthDimension.lean`
- Modify: `GSTTailFInfiniteRead.lean`
- Modify: `GSTTowerAxis.lean`
- Modify: `GSTTowerFire.lean`
- Modify: relevant `waves/*.lean` production modules imported by `HCProof.lean`

**Interfaces:**
- Consumes limitless world/operators/cohomology.
- Produces arbitrary-time/depth propagation laws, with finite chart death reinterpreted as observation loss.

- [ ] Add probes for propagation beyond historical finite windows.
- [ ] Lift local laws by naturality rather than rewriting their arithmetic content.
- [ ] Generalize propagation/cut/ignition statements to arbitrary windows/support envelopes.
- [ ] Preserve exact historical specializations.
- [ ] Compile wave stack and run gate.
- [ ] Commit.

### Task 9: Infinite Hodge diagonal and pure sector

**Files:**
- Modify: `GSTDimensionFreeHodgeDiagonal.lean`
- Modify: `GSTGlobalPureHodgeCosmology.lean`
- Modify: `GSTHodgeAssault.lean`
- Modify: `GSTHodgeAssaultV2.lean`
- Create: `GSTLimitlessHodge.lean`
- Modify: `HCProof.lean`
- Modify: `lakefile.toml`

**Interfaces:**
- Produces weight-`p` diagonal generator for every `p : Nat`, compact pure-Hodge equivalence with finitely supported diagonal coefficients, and exact finite truncation recovery.

- [ ] Add failing probes for arbitrary-weight diagonal classes beyond every fixed finite chart.
- [ ] Implement limitless diagonal/pure sector.
- [ ] Prove rank-one weight classification and finite-support pure-sector decomposition.
- [ ] Recover `min A B` finite coordinates and historical 4×3 classes by restriction.
- [ ] Compile and run Hodge/cosmology gates.
- [ ] Commit.

### Task 10: Poincare and Lefschetz–Hodge synthesis

**Files:**
- Modify: `GSTWorldPoincareDuality.lean`
- Modify: `GSTLefschetzPoincareReciprocity.lean`
- Modify: `GSTPureHodgeLefschetzKernel.lean`
- Modify: `GSTSquarePureHodgeDuality.lean`
- Modify: `GSTUniversalLefschetzCausalGeometry.lean`
- Modify: `GSTLefschetzCrown.lean`
- Modify: `GSTLefschetzCrownV2.lean`

**Interfaces:**
- Produces translated finite-window/relative duality, compact-support vs completed pairing where formalized, and universal bidegree/path compatibility.

- [ ] Add probes that prevent any fictional global top-cell theorem.
- [ ] Generalize finite duality naturally under translated/enlarged windows.
- [ ] Prove interaction with limitless Lefschetz paths and Hodge grading.
- [ ] Recover existing determinant/injectivity/non-surjectivity finite facts exactly.
- [ ] Compile and run gates.
- [ ] Commit.

### Task 11: Abstract algebraic-geometry interfaces

**Files:**
- Modify: `GSTProjectiveOverC.lean`
- Modify: `GSTWorldCrownBridge.lean`
- Modify: `GSTAnalyticAbsorption.lean`
- Modify: `GSTAnalyticAbsorptionV2.lean`
- Create: `GSTAbstractAlgebraicGeometry.lean`
- Modify: `HCProof.lean`
- Modify: `lakefile.toml`

**Interfaces:**
- Produces explicit ring-hom/spectrum/graded or Proj-compatible interfaces where Mathlib allows, tying finite quotient geometry to the limitless coordinate algebra without identifying it with arbitrary external schemes.

- [ ] Add compile probes for coordinate-ring morphisms and finite quotient maps.
- [ ] Implement exact algebraic interfaces using existing Mathlib APIs only.
- [ ] Prove compatibility with finite GST chart geometry.
- [ ] Keep external scheme identification behind explicit realization data.
- [ ] Compile Stage 2 foundations and run gates.
- [ ] Commit.

### Task 12: Clay/transfer and Stage 2 realization migration

**Files:**
- Modify: `GSTClayOfficial.lean`
- Modify: `GSTClayOfficialV2.lean`
- Modify: `GSTTransferBridge.lean`
- Modify: `GSTTransferBridgeV2.lean`
- Modify: `GSTGeometricRealizationStage2.lean`
- Modify: `GSTGeometricRealizationStage2B.lean`
- Modify: `GSTGeometricRealizationStage2C.lean`
- Modify: `GSTGeometricRealizationStage2D.lean`
- Modify: `GSTGeometricRealizationStage2E.lean`
- Modify: `GSTGeometricRealizationStage2F.lean`
- Modify: `GSTGeometricRealizationStage2G.lean`

**Interfaces:**
- Consumes limitless Hodge/coordinate/cohomology abstractions.
- Produces finite realization certificates parameterized by arbitrary finite windows/diagonal ranges while preserving actual Mathlib scheme, singular cohomology, algebraic-cycle and Hodge-bigrading semantics.

- [ ] Add probes for variable finite realization dimensions/windows.
- [ ] Remove artificial fixed-address assumptions where present.
- [ ] Thread stronger universal maps through E/F/G forgetful equivalences.
- [ ] Keep every unresolved external realization obligation explicit and named.
- [ ] Compile Stage 2 stack and run its workflow.
- [ ] Commit.

### Task 13: Historical/V2 absorption and repo-wide production audit

**Files:**
- Audit every production `.lean` file in the recursive repository tree.
- Modify only files whose definitions/imports/theorems genuinely need migration.
- Do not churn comparator fixtures unless interface migration requires it.

**Interfaces:**
- Produces a single canonical theorem hierarchy with V1/V2/historical names retained as compatibility results where needed.

- [ ] Classify every production Lean module against the spec categories.
- [ ] Remove duplicated implementation bodies only when the stronger canonical theorem subsumes them and dependents compile.
- [ ] Search for residual hard-coded `Fin 12`, `4×3`, terminal Hodge weights, fixed nilpotence ceilings, and fixed-rank realization assumptions; classify each occurrence as legitimate specialization or remaining wall.
- [ ] Patch every remaining artificial wall.
- [ ] Compile complete repository.
- [ ] Commit.

### Task 14: Verification, axiom audit, and documentation synchronization

**Files:**
- Modify: `README.md`
- Modify: `docs/HC_UNIVERSE_MAP.md`
- Modify: `docs/GST_V2_OPERATING_MANUAL.md`
- Modify: other docs only where they describe superseded architecture.
- Modify workflows only if new canonical modules need to be included in existing gates.

**Interfaces:**
- Produces audit-accurate documentation and verification receipts.

- [ ] Run full `lake build` in CI.
- [ ] Run cosmology, V2, comparator, coherent-wave, and Stage 2 workflows.
- [ ] Run repository searches for `sorry`, custom `axiom`, and stale boundary language.
- [ ] Check `#print axioms` receipts for new crown theorems.
- [ ] Update docs to describe limitless vs finite-window semantics and preserve Stage 2 scope warnings.
- [ ] Commit final verification/doc batch.

### Task 15: Whole-branch review

**Files:** none unless review finds defects.

- [ ] Compare branch against baseline `fad086313bb97ec9d53eac9be75407466eec52fc`.
- [ ] Review every changed theorem for accidental weakening, semantic overclaim, and hidden finite assumptions.
- [ ] Fix Critical/Important findings with new RED→GREEN compile cycles.
- [ ] Re-run full suite and record final green head.
