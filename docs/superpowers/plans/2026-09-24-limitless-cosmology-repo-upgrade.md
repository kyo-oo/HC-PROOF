# Limitless Cosmology Repository Upgrade Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace artificial global finite ceilings across HC-PROOF with a limitless Lean cosmology whose finite worlds, operators, cohomology, Hodge sectors, topology, and algebraic-geometric realizations are exact windows, quotients, or finite specializations.

**Architecture:** Build two honest infinite faces: a finite-support algebraic cosmos on `Nat × Nat`, and a coherent completed observational cosmos reconstructed from all finite windows. Upgrade world geometry, addresses, operators, cohomology, Hodge/Lefschetz/duality, and algebraic geometry from the lowest dependency layers upward; keep every legitimate finite theorem as an exact specialization. The historical 4×3 universe remains a verified chart, not a global ceiling.

**Tech Stack:** Lean 4.33.0-rc2, Mathlib v4.33.0-rc2, Lake, GitHub Actions, existing HC-PROOF theorem stack.

**Spec:** `docs/superpowers/specs/2026-09-24-limitless-cosmology-repo-upgrade-design.md`

## Global Constraints

- No new `sorry`, `admit`, or custom axiom used to manufacture strength.
- Existing exact finite theorems remain available as specializations or compatibility corollaries.
- `4×3`, `Fin 12`, finite Hodge ranges, truncation ideals, and finite top degrees must not remain global ceilings when they are chart artifacts.
- Finite-support algebraic infinity and completed observational infinity must remain distinct and explicitly related.
- Actual Mathlib `Scheme`, smooth/projective structures, singular cohomology, algebraic cycles, Hodge bigrading, and cycle-class maps remain semantically distinct from internal GST carriers.
- Every production `.lean` file is audited; only mathematically justified files are changed.
- Every implementation batch is compiler-checked on the branch with Lean 4.33.0-rc2 + pinned Mathlib.

## Review Focus

- Empty/zero-size finite windows: restriction/extension must remain total and round-trip claims must include the necessary support hypotheses.
- Boundary translation: a shift leaving a finite window must disappear only after observation/restriction, never in the unbounded operator itself.
- Compact-versus-completed confusion: no theorem may identify finitely supported functions with arbitrary global fields without an explicit hypothesis/equivalence proof.
- Degree/charge parity: bigraded Hodge coordinates must not silently assume every `(degree, charge)` pair corresponds to a natural cell.
- Stage-2 semantics: internal GST generalization must not silently become a theorem about arbitrary smooth projective complex schemes.

---

### Task 1: Branch compiler gate and RED smoke test

**Files:**
- Create: `.github/workflows/limitless-cosmology.yml`
- Create: `LimitlessCosmologySmoke.lean`

**Interfaces:**
- Consumes: existing `lakefile.toml` and pinned toolchain/dependencies.
- Produces: branch-scoped compiler receipt and a smoke file whose initial failure proves the new API does not pre-exist.

- [ ] **Step 1: Create a failing smoke test**

```lean
import GSTLimitlessCosmology

open GSTLimitlessCosmology

#check CosmicCell
#check CosmicCoef
#check digitShift
#check carryShift
#check lefschetz
#check windowRestrict
#check windowExtend
#check compactToGlobal
```

- [ ] **Step 2: Compile and verify RED**

Run in branch CI:

```bash
lake env lean LimitlessCosmologySmoke.lean
```

Expected: FAIL because module `GSTLimitlessCosmology` does not exist.

- [ ] **Step 3: Keep the branch compiler workflow active**

The workflow must install `leanprover/lean4:v4.33.0-rc2`, run `lake update`, `lake exe cache get`, reject `axiom|sorry|admit` in upgraded modules, and compile the smoke file plus each migrated module.

- [ ] **Step 4: Commit**

```bash
git add .github/workflows/limitless-cosmology.yml LimitlessCosmologySmoke.lean
git commit -m "test: establish limitless cosmology compiler gate"
```

### Task 2: Algebraic limitless world and finite-window bridge

**Files:**
- Create: `GSTLimitlessCosmology.lean`
- Modify: `GSTWorldCosmology.lean`
- Modify: `HCProof.lean`
- Test: `LimitlessCosmologySmoke.lean`

**Interfaces:**
- Produces:
  - `CosmicCell := Nat × Nat`
  - `CosmicCoef R := CosmicCell →₀ R`
  - unrestricted `digitShift`, `carryShift`, `lefschetz`
  - `windowExtend` from `WorldCoef A B` into compact cosmic coefficients
  - `windowRestrict` from compact cosmic coefficients into `WorldCoef A B`
  - support-sensitive round-trip theorems
  - historical 4×3 world as an exact finite window.

- [ ] **Step 1: Extend smoke test with finite-window round trip**

```lean
example (g : GSTWorldCosmology.WorldCoef A B) :
    windowRestrict A B (windowExtend A B g) = g := by
  simpa using windowRestrict_windowExtend (A := A) (B := B) g
```

Expected RED: names are missing.

- [ ] **Step 2: Implement the limitless carrier and unrestricted shifts**

Use `Finsupp` on `Nat × Nat`; define shifts by reindexing basis coordinates so no upper row/column exists. Prove zero/add/smul compatibility and iteration laws.

- [ ] **Step 3: Implement exact finite-window extension/restriction**

Extension sends `(i,j) : Fin A × Fin B` to `(i,j) : Nat × Nat`; restriction reads those coordinates back. Prove `windowRestrict_windowExtend` without positivity assumptions, including `A=0` or `B=0`.

- [ ] **Step 4: Recast old finite boundaries**

In `GSTWorldCosmology.lean`, retain finite shift-extinction theorems but state/document them as facts about a bounded `WorldCoef A B`. Add bridge theorems showing finite shifts agree with cosmic shifts followed by restriction whenever the translated coordinate remains inside the window.

- [ ] **Step 5: Compile GREEN**

```bash
lake build GSTLimitlessCosmology GSTWorldCosmology
lake env lean LimitlessCosmologySmoke.lean
```

Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add GSTLimitlessCosmology.lean GSTWorldCosmology.lean HCProof.lean LimitlessCosmologySmoke.lean
git commit -m "feat: add limitless world and finite-window bridge"
```

### Task 3: Completed observational cosmos and topology-facing reconstruction

**Files:**
- Modify: `GSTLimitlessCosmology.lean`
- Modify: `GSTCoherentCosmology.lean`
- Modify: `GSTInfiniteWorldClassification.lean`
- Test: `LimitlessCosmologySmoke.lean`

**Interfaces:**
- Produces `GlobalCoef R := CosmicCell → R`, finite observation maps, compatibility of nested observations, compact-to-global embedding, and point-separation by finite windows.

- [ ] **Step 1: Add failing tests** for `compactToGlobal`, nested-window restriction coherence, and separation of unequal global fields by one coordinate/window.
- [ ] **Step 2: Implement unrestricted global coefficient fields** and canonical embedding from `Finsupp`.
- [ ] **Step 3: Implement observation maps** `observe A B : GlobalCoef R → WorldCoef A B` and prove nested restriction laws.
- [ ] **Step 4: Connect coherent finite observation philosophy** in `GSTCoherentCosmology`/`GSTInfiniteWorldClassification` without identifying ternary `WindowTower` with arbitrary coefficient fields; prove the common finite-observation separation pattern through dedicated bridge theorems.
- [ ] **Step 5: Compile GREEN** with `lake build GSTLimitlessCosmology GSTCoherentCosmology GSTInfiniteWorldClassification` and the smoke file.
- [ ] **Step 6: Commit** `feat: add completed observational cosmology`.

### Task 4: Universal addresses, recoordination, and unrestricted operator algebra

**Files:**
- Modify: `GSTUniversalAddressBridge.lean`
- Modify: `GSTWorldRecoordinationGroupoid.lean`
- Modify: `GSTUniversalLefschetzCosmology.lean`
- Modify: `GSTUniversalLefschetzPathFormula.lean`
- Modify: `GSTUniversalLefschetzKernel.lean`
- Modify: `GSTUniversalLefschetzCausalGeometry.lean`
- Modify: `GSTTruncatedWorldCohomologyRing.lean`
- Modify: `GSTGradedWorldAlgebra.lean`
- Test: `LimitlessCosmologySmoke.lean`

**Interfaces:**
- Produces limitless cell/address equivalence, unrestricted `H`, `V`, `L`, exact arbitrary-time binomial path formula, exact global causal kernel, and finite quotient interpretation of `H^B=0`, `V^A=0`.

- [ ] **Step 1: Add failing operator tests** proving a far-away basis cell survives a large global shift while the same shift vanishes after restriction to a small window.
- [ ] **Step 2: Add a canonical pairing/equivalence** between `Nat × Nat` and a countable address carrier while preserving finite address specializations.
- [ ] **Step 3: Lift path and kernel formulas** to unrestricted cells, with coefficient `Nat.choose n m` at exact causal distance.
- [ ] **Step 4: Refactor finite Lefschetz nilpotence** into quotient/window theorems; do not remove existing finite theorem names.
- [ ] **Step 5: Strengthen truncated ring interpretation** so finite world cohomology is explicitly a quotient/truncation of the unrestricted commuting operator algebra.
- [ ] **Step 6: Compile GREEN** for all eight modules plus smoke file.
- [ ] **Step 7: Commit** `feat: lift addresses and Lefschetz algebra beyond finite walls`.

### Task 5: Cohomology, wave, Omega, TailF, and transport naturality

**Files:**
- Modify: `waves/GSTWaveCohomologyV2.lean`
- Modify: `waves/GSTNCohomologyV2.lean`
- Modify: `waves/GSTVortexSingularityV2.lean`
- Modify: `GST2DMixedEmergence.lean`
- Modify: `GST2DMixedEmergenceUpgrade.lean`
- Modify: `GSTBladeWave.lean`
- Modify: `GSTTailFFourthDimension.lean`
- Modify: `GSTTailFInfiniteRead.lean`
- Modify: `GSTWorldtraceArithmetic.lean`
- Modify: `GSTWorldtraceMahlerRelativePrecision.lean`

**Interfaces:**
- Produces naturality of source/coboundary/cohomology data under finite-window extension and observation; arbitrary-time propagation is stated in the unbounded cosmos while cut/window extinction stays local.

- [ ] **Step 1: Add RED examples** that transport a source-free/exact decomposition into a larger window and restrict it back.
- [ ] **Step 2: Prove wave differential/source naturality** under window maps.
- [ ] **Step 3: Lift arbitrary-depth propagation statements** where current terminal hypotheses are only finite-chart artifacts.
- [ ] **Step 4: Preserve Omega/TailF arithmetic hypotheses that are genuinely number-theoretic**, changing only representation ceilings.
- [ ] **Step 5: Compile GREEN** all modified wave/Omega/TailF modules.
- [ ] **Step 6: Commit** `feat: make wave cohomology natural across limitless observations`.

### Task 6: Infinite Hodge grading, pure sector, Lefschetz-Hodge synthesis, and relative duality

**Files:**
- Modify: `GSTDimensionFreeHodgeDiagonal.lean`
- Modify: `GSTGlobalPureHodgeCosmology.lean`
- Modify: `GSTPureHodgeLefschetzKernel.lean`
- Modify: `GSTSquarePureHodgeDuality.lean`
- Modify: `GSTWorldPoincareDuality.lean`
- Modify: `GSTLefschetzPoincareReciprocity.lean`
- Modify: `GSTWorldCrownBridge.lean`
- Modify: `GSTLefschetzCrownV2.lean`
- Modify: `GSTHodgeAssaultV2.lean`
- Modify: `GSTClayOfficialV2.lean`
- Modify: `GSTTransferBridgeV2.lean`

**Interfaces:**
- Produces a diagonal generator at every `p : Nat`, compact pure-Hodge coordinates as finitely supported diagonal sequences, global Lefschetz motion on grading, and honest finite/relative Poincare duality.

- [ ] **Step 1: Add RED tests** for a weight `p` chosen larger than any historical 4×3 weight and show the cosmic diagonal generator exists/nonzero.
- [ ] **Step 2: Define/prove all-weight compact Hodge classification** on the unbounded cosmos.
- [ ] **Step 3: Recover finite vanish-above-bound statements** solely after restriction to `A×B`.
- [ ] **Step 4: Refactor Poincare theorems** as finite-window/relative duality and add translation/window naturality; do not invent a global top cell.
- [ ] **Step 5: Preserve exact old determinant/integral-surjectivity facts** for the 4×3 chart.
- [ ] **Step 6: Compile GREEN** all Hodge/Lefschetz/duality modules.
- [ ] **Step 7: Commit** `feat: lift Hodge cosmology to every weight`.

### Task 7: Abstract algebraic geometry and completion interfaces

**Files:**
- Modify: `GSTRadixWorldDynamics.lean`
- Modify: `GSTWorldRecoordinationGroupoid.lean`
- Modify: `GSTGradedWorldAlgebra.lean`
- Modify: `GSTTruncatedWorldCohomologyRing.lean`
- Modify: `GSTProjectiveOverC.lean`
- Modify: `GSTGeometricRealizationStage2A.lean`
- Modify: `GSTGeometricRealizationStage2B.lean`
- Modify: `GSTGeometricRealizationStage2C.lean`
- Modify: `GSTGeometricRealizationStage2D.lean`
- Modify: `GSTGeometricRealizationStage2E.lean`
- Modify: `GSTGeometricRealizationStage2F.lean`
- Modify: `GSTGeometricRealizationStage2G.lean`

**Interfaces:**
- Produces explicit universal coordinate-algebra/finite-quotient interfaces, ring-hom/spectrum-compatible maps where Mathlib provides the needed API, and realization certificates parameterized by finite windows/ranks rather than historical fixed carriers.

- [ ] **Step 1: Add RED algebra tests** for generic truncation ideals and monomial survival/vanishing.
- [ ] **Step 2: Generalize quotient geometry** behind the existing truncated world ring using actual Mathlib polynomial/quotient structures where this does not destabilize current APIs.
- [ ] **Step 3: Add explicit ring-hom interfaces** into the existing `Scheme`/projective layer; only state `Spec`/`Proj` compatibility when Lean maps are constructed.
- [ ] **Step 4: Generalize Stage-2 realization inputs** to arbitrary finite windows/diagonal ranges without adding surjectivity/algebraicity assumptions to data structures.
- [ ] **Step 5: Compile GREEN** all Stage-2 modules and the official comparator targets.
- [ ] **Step 6: Commit** `feat: integrate limitless GST with abstract algebraic geometry`.

### Task 8: Repository-wide migration audit, API absorption, and verification

**Files:**
- Modify: every remaining production `.lean` file whose strongest theorem is still restricted by an artificial finite representation ceiling.
- Modify: `HCProof.lean`
- Modify: `lakefile.toml` only if new library roots require registration.
- Modify: documentation maps to identify canonical universal theorems and finite specializations.

**Interfaces:**
- Produces a clean public universe entry face and removes accidental V1/V2 duplication without deleting historically used theorem names.

- [ ] **Step 1: Classify every production Lean file** as foundation/local law/window/universal/operator/cohomology/Hodge/abstract geometry/Stage2/verification and record the result in the plan ledger.
- [ ] **Step 2: Search for hard-coded ceilings** (`Fin 12`, literal `4×3` encodings, terminal weights, truncation powers, fixed address counts) and decide each occurrence as legitimate local specialization or migration target.
- [ ] **Step 3: Edit each genuine migration target** so the strongest theorem lives at the unbounded level and the old theorem is an exact specialization.
- [ ] **Step 4: Run full proof-escape audit** over production Lean files.
- [ ] **Step 5: Run full compiler suite**:

```bash
lake build
lake env lean LimitlessCosmologySmoke.lean
```

and execute the existing cosmology, V2, Stage2, and official-comparator workflows.

- [ ] **Step 6: Verify no `sorryAx` in crown logs** and inspect `#print axioms` receipts.
- [ ] **Step 7: Commit** `refactor: complete limitless cosmology migration`.

## Execution ruling

The user explicitly selected native/inline execution by instructing the assistant to continue, edit the Lean files, and run the compiler. Execute continuously on `sol/limitless-cosmology`; do not merge to `main` without separate explicit approval.
