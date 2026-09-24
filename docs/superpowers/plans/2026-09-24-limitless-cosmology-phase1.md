# Limitless Cosmology Phase 1 Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Introduce the first compile-checked limitless layer: an unbounded finite-support GST world, exact finite-window maps, unrestricted commuting axis operators, and a global Lefschetz/path calculus whose existing finite worlds are exact specializations.

**Architecture:** The algebraic limitless universe is `Nat × Nat` with finite-support integer coefficients. Existing `WorldCell A B` / `WorldCoef A B` remain finite observations. New maps extend a finite world into the limitless field and restrict limitless fields back to a finite window. Global horizontal/vertical shifts act without terminal extinction; the existing finite shifts become window-truncated shadows. Global Lefschetz evolution is then defined from those unrestricted shifts and related to the existing finite universal Lefschetz layer.

**Tech Stack:** Lean 4.33.0-rc2, Mathlib v4.33.0-rc2, `Finsupp`, existing HC-PROOF world/Lefschetz APIs, GitHub Actions `lake build`.

**Spec:** `docs/superpowers/specs/2026-09-24-limitless-cosmology-repo-upgrade-design.md`

## Global Constraints

- No new `sorry`, `admit`, or custom axioms.
- Existing finite theorems remain true and available.
- Finite boundaries become observation/quotient facts, not global extinction laws.
- No false equivalence between finite-support algebraic data and completed unrestricted observations.
- The historical `4 × 3` chart remains an exact finite specialization.
- Every new crown theorem receives compiler and axiom-audit receipts.
- Work only in `kyo-oo/HC-PROOF` on branch `sol/limitless-cosmology-phase1`.

## Review Focus

- Zero-sized windows (`A = 0` or `B = 0`) must not create invalid `Fin` witnesses.
- Finite extension followed by restriction must be definitionally/extentionally exact.
- Restriction after global shift must agree with existing finite shift where the source coordinate lies in-window, and truncate exactly otherwise.
- Global shifts must compose and commute for all natural depths with no terminal extinction theorem.
- Global Lefschetz basis coefficients must use exact binomial/path counts and specialize to the existing finite kernel when the entire path remains visible.

---

### Task 1: Compiler gate for the branch

**Files:**
- Modify: `.github/workflows/cosmology-upgrade-gate.yml`

**Interfaces:**
- Consumes: existing cosmology upgrade workflow.
- Produces: branch-triggered compiler gate covering the new Phase-1 modules.

- [ ] **Step 1: Add the isolated branch to the push trigger**

Add `sol/limitless-cosmology-phase1` beside `main` and add paths for `GSTLimitlessWorld.lean` and `GSTLimitlessWorldTest.lean`.

- [ ] **Step 2: Add the new modules to proof-escape and compile checks**

The workflow must reject `axiom|sorry|admit` in the new production/test modules and execute:

```bash
lake build GSTLimitlessWorld GSTLimitlessWorldTest GSTWorldCosmology GSTUniversalLefschetzCosmology GSTUniversalLefschetzPathFormula GSTUniversalLefschetzKernel
```

Expected: the workflow itself remains valid and future pushes to the branch create a compiler run.

- [ ] **Step 3: Commit**

Commit message: `ci: compile limitless cosmology phase 1`

---

### Task 2: RED test for the limitless carrier and axis laws

**Files:**
- Create: `GSTLimitlessWorldTest.lean`
- Modify: `lakefile.toml`

**Interfaces:**
- Consumes: planned `GSTLimitlessWorld` API.
- Produces: compiler-level contract for `CosmicCell`, `CosmicCoef`, `cosmicDigitShiftN`, `cosmicCarryShiftN`, and finite-window round trips.

- [ ] **Step 1: Write the failing compiler test**

Create a module importing `GSTLimitlessWorld` and checking/proving:

```lean
#check CosmicCell
#check CosmicCoef
#check cosmicDigitShiftN
#check cosmicCarryShiftN
#check cosmic_axes_commute
#check cosmic_digitShiftN_add
#check cosmic_carryShiftN_add
#check extendWorld
#check restrictWorld
#check restrictWorld_extendWorld
```

Include concrete examples showing a coefficient can be shifted to coordinates beyond every historical `4 × 3` bound.

- [ ] **Step 2: Register both new roots**

Add `GSTLimitlessWorld` and `GSTLimitlessWorldTest` to the `HCUniverse` root registry.

- [ ] **Step 3: Run the compiler gate and observe RED**

Expected: FAIL because `GSTLimitlessWorld` does not exist yet.

- [ ] **Step 4: Commit the RED test**

Commit message: `test: specify limitless world algebra`

---

### Task 3: Implement the unbounded finite-support world

**Files:**
- Create: `GSTLimitlessWorld.lean`

**Interfaces:**
- Produces:
  - `abbrev CosmicCell := Nat × Nat`
  - `abbrev CosmicCoef := CosmicCell →₀ ℤ`
  - `cosmicDigitShiftN : Nat → CosmicCoef → CosmicCoef`
  - `cosmicCarryShiftN : Nat → CosmicCoef → CosmicCoef`
  - additive composition and commutation theorems
  - `extendWorld` / `restrictWorld`
  - exact `restrictWorld_extendWorld`
  - support-bounded reverse theorem for `extendWorld_restrictWorld`.

- [ ] **Step 1: Implement coordinate translations through `Finsupp.mapDomain`/explicit finite-support transport**

Global digit shift sends `(C,d)` to `(C,d+n)` and global carry shift sends `(C,d)` to `(C+n,d)` with no bound checks.

- [ ] **Step 2: Prove identity/composition/commutation**

Required crowns:

```lean
cosmic_digitShiftN_zero
cosmic_carryShiftN_zero
cosmic_digitShiftN_add
cosmic_carryShiftN_add
cosmic_axes_commute
```

- [ ] **Step 3: Implement finite-window extension/restriction**

`extendWorld` maps every `(Fin A, Fin B)` coefficient into the corresponding natural coordinate. `restrictWorld` evaluates at natural coordinates coming from a finite cell.

- [ ] **Step 4: Prove exact round trip**

```lean
theorem restrictWorld_extendWorld (g : WorldCoef A B) :
  restrictWorld A B (extendWorld g) = g
```

Also prove the reverse equality under a support-inside-window hypothesis.

- [ ] **Step 5: Run compiler gate**

Expected: `GSTLimitlessWorld` and `GSTLimitlessWorldTest` PASS with no `sorryAx`.

- [ ] **Step 6: Commit**

Commit message: `feat: add limitless finite-support GST universe`

---

### Task 4: Recast finite worlds as exact observations

**Files:**
- Modify: `GSTWorldCosmology.lean`
- Modify: `GSTLimitlessWorldTest.lean`

**Interfaces:**
- Consumes: `extendWorld`, `restrictWorld`, global shifts.
- Produces: compatibility theorems between existing finite shifts and global shifts.

- [ ] **Step 1: Write RED compatibility tests**

Specify exact evaluation theorems asserting that restricting a globally shifted extended world equals the existing finite shift at every finite coordinate.

- [ ] **Step 2: Import the limitless layer into `GSTWorldCosmology`**

Do not replace the finite definitions. Reinterpret their extinction theorems explicitly as window/observation truncation.

- [ ] **Step 3: Prove shift specialization**

Required laws:

```lean
restrict_cosmicDigitShift_extend
restrict_cosmicCarryShift_extend
```

and a theorem that the old `4 × 3` wave chart embeds into the limitless universe through `liftWave` then `extendWorld` without information loss.

- [ ] **Step 4: Compile and commit**

Expected: green cosmology gate.
Commit message: `feat: make finite GST worlds exact limitless observations`

---

### Task 5: Unrestricted Lefschetz evolution

**Files:**
- Modify: `GSTUniversalLefschetzCosmology.lean`
- Modify: `GSTUniversalLefschetzPathFormula.lean`
- Modify: `GSTUniversalLefschetzKernel.lean`
- Modify: `GSTLimitlessWorldTest.lean`

**Interfaces:**
- Consumes: unrestricted global shifts.
- Produces: global linear endomorphisms `cosmicH`, `cosmicV`, `cosmicL`, arbitrary-power path expansion, and exact basis transition kernel.

- [ ] **Step 1: Write RED operator tests**

Require `cosmicH`, `cosmicV`, `cosmicL`, `cosmic_HV_commute`, and arbitrary-depth non-extinction witness on basis states.

- [ ] **Step 2: Define global linear operators**

Construct integer-linear endomorphisms from the global shifts and prove `H`/`V` commute.

- [ ] **Step 3: Prove unrestricted binomial path formula**

For all `n`, express `cosmicL ^ n` as the binomial sum of commuting horizontal/vertical paths.

- [ ] **Step 4: Prove exact basis kernel**

From source `(C,d)` to target `(C+a,d+b)`, coefficient at time `a+b` is `Nat.choose (a+b) b`; noncausal targets have coefficient zero.

- [ ] **Step 5: Prove finite specialization**

Where the full path remains inside an `A × B` window, restricting global evolution reproduces the existing finite universal Lefschetz/path/kernel statements. Existing finite nilpotence stays unchanged and is documented as observation extinction.

- [ ] **Step 6: Compile and commit**

Expected: all six phase modules green, existing cosmology gate green, no proof escapes.
Commit message: `feat: lift Lefschetz dynamics beyond finite walls`

---

### Task 6: Phase-1 integration receipt

**Files:**
- Modify: `HCProof.lean`
- Modify: `docs/HC_UNIVERSE_MAP.md`

**Interfaces:**
- Consumes: all Phase-1 modules.
- Produces: canonical entry-face import and architecture documentation.

- [ ] **Step 1: Import `GSTLimitlessWorld` from the universe entry face**

- [ ] **Step 2: Document finite worlds as observations of the limitless algebraic cosmos**

State explicitly that finite-support and completed observational infinities remain distinct; Phase 1 implements only the algebraic finite-support face plus finite observations.

- [ ] **Step 3: Run the full cosmology gate and the default `lake build HCProof` if the workflow budget permits**

Expected: green; no `sorryAx` from new crowns.

- [ ] **Step 4: Commit**

Commit message: `docs: expose limitless cosmology phase 1`
