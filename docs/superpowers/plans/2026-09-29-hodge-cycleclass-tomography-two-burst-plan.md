# Hodge Cycle-Class / Tomography Two-Burst Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Strengthen the current Stage-2G landing with genuine cycle-class geometry that excludes the zero-map model and proves projective detector visibility strongly enough for the existing tomography/ghost collision machinery to eliminate every surviving Hodge ghost.

**Architecture:** Keep the existing GST/tomography/ghost route intact. Add one stronger geometric semantic package above `HodgeBigradedBettiData`, prove a genuinely geometric projective readout/separation theorem on the canonical spine source, then consume the already-proved `ProjectiveDetectorVisible.toMomentHit` and detector-moment contradiction. Execute in two bursts on `sol/hodge-single-separator-successor`; after Burst 1 commit, publish a GLM handoff and trigger CI, then continue Burst 2 while GLM repairs Lean/API issues in parallel.

**Tech Stack:** Lean 4, Mathlib, existing HC-PROOF GST/projective/Hodge modules, GitHub Actions.

**Spec:** `docs/superpowers/specs/2026-09-29-hodge-cycleclass-tomography-two-burst-design.md`

## Global Constraints

- Stay on `sol/hodge-single-separator-successor`; create no branch.
- Refresh the branch head before every write because GLM is working in parallel.
- Do not delete or weaken semantic-rigidity / zero-map countermodel audits.
- Do not introduce fields equivalent to `BigradedBettiHodgeStatement`, arbitrary basis-cycle realization, `source_action`, `acts_as_GST`, exact matrix-unit realization, or arbitrary point-transition kernels.
- Tomography remains a derived GST detector; geometry must supply horizontal visibility independently.
- No `sorry`, custom Hodge-surjectivity axiom, hidden basis bridge, or renamed conclusion.
- GLM owns parser/elaborator/namespace/tactic/API repair; assistant owns mathematics, theorem statements, proof derivations, and integration.

## Review Focus

- Zero-cycle-class model: new genuine geometry must be impossible for `cycleClass = 0` whenever a codimension point exists with positive projective degree.
- Circular visibility: no theorem may prove visibility by assuming the target basis direction is already algebraic.
- Empty/trivial Hodge fibers: closure must not demand ghost/readout data where no ghost can exist.
- Parallel branch movement: writes must be rebased logically onto the latest compatible branch head rather than overwrite GLM commits.
- Finite tomography support: all separation arguments must use the finite live support selected by the actual ghost, not a hidden global finite-rank assumption.

---

### Task 1: Genuine Cycle-Class Geometry Foundation

**Files:**
- Create: `GSTClassicalHodgeGenuineCycleClassGeometry.lean`
- Reuse: `GSTClassicalHodgeGeometricCycleClassSpine.lean`
- Reuse: `GSTClassicalHodgeProjectiveDegreeTrace.lean`
- Reuse: `GSTClassicalHodgeStage2GSemanticRigidity.lean`

**Interfaces:**
- Consumes: `GeometricCycleClassSpine V H`, `ProjectiveDegreeTraceSemantics V H`, native projective correspondence operations already defined in the repo.
- Produces: `GenuineCycleClassGeometry V H`, projections to the old spine/degree interfaces, and a theorem that `zeroCycleClassData H` cannot support the new package when a genuine positive-degree point exists.

- [ ] **Step 1: Define the stronger semantic package**

Create `GenuineCycleClassGeometry (V) (H)` extending the existing spine and degree semantics, with only independently geometric projective/correspondence readout laws required later for separator visibility.

- [ ] **Step 2: Prove old-interface projections**

Expose exact coercion/projection theorems back to `GeometricCycleClassSpine V H` and `ProjectiveDegreeTraceSemantics V H` so all existing ghost/spine theorems remain reusable unchanged.

- [ ] **Step 3: Prove zero-map exclusion**

Add a theorem with the shape:

```lean
not_genuineCycleClassGeometry_zeroCycleClass :
  ... → ¬ Nonempty (GenuineCycleClassGeometry V (zeroCycleClassData H))
```

using positive projective degree / trace compatibility, not Hodge surjectivity.

- [ ] **Step 4: Add audit checks**

Include `#check` / `#print axioms` for the new public theorems and verify no new theorem depends on a Hodge-surjectivity axiom or renamed basis bridge.

- [ ] **Step 5: Commit Task 1**

Commit message: `Hodge: add genuine cycle-class geometry semantics`.

---

### Task 2: Projective Tomography Readout and Finite Separation

**Files:**
- Create: `GSTClassicalHodgeProjectiveTomographyReadout.lean`
- Create: `GSTClassicalHodgeProjectiveVisibilitySeparation.lean`
- Reuse: `GSTClassicalHodgeLefschetzTomography.lean`
- Reuse: `GSTClassicalHodgeGhostSpineCosmicLeak.lean`
- Reuse: `GSTClassicalHodgeProjectiveDetectorVisibility.lean`
- Reuse: projective correspondence algebra/kernel modules.

**Interfaces:**
- Consumes: `GenuineCycleClassGeometry V H`, `OmniversalSeparatorGhost G`, canonical `ghostSpineSeed`, finite tomography support/moment index, existing `ProjectiveNativeKernel` algebra.
- Produces: a finite family/readout of genuine projective kernels on the canonical spine source, a nondegeneracy/separation theorem, and finally `Nonempty (ProjectiveDetectorVisible G M E)` without assuming target algebraicity.

- [ ] **Step 1: Define the finite geometric readout family**

Define the readout only on the finite live support selected by the ghost/tomography data. Keep construction in the existing projective correspondence span.

- [ ] **Step 2: Prove linearity and scaling formulas**

Show readouts respect rational linear combinations of projective kernels and agree with existing cycle-class naturality on the canonical spine source.

- [ ] **Step 3: Prove finite support/separation lemma**

From the genuine geometric pairing/nondegeneracy law in Task 1, prove that a nonzero ghost/tomography functional cannot annihilate every member of the finite projective readout family.

- [ ] **Step 4: Derive detector visibility**

Construct:

```lean
exists_projectiveDetectorVisible
    (J : GenuineCycleClassGeometry V H)
    (M : NativeMassCycleClassBridge V H)
    (E : OmniversalSeparatorGhost J.toGeometricCycleClassSpine) :
    Nonempty (ProjectiveDetectorVisible J.toGeometricCycleClassSpine M E)
```

or an equivalent theorem whose proof is entirely geometric plus finite separation.

- [ ] **Step 5: Test the zero-map and circularity boundaries**

Ensure the proof uses neither a basis-cycle bridge nor `ProjectiveLiveSourceTarget.source_action` nor any `RealizesCosmicOnPoints` assumption.

- [ ] **Step 6: Commit Burst-1 source**

Commit message: `Hodge: derive projective tomography visibility from genuine geometry`.

---

### Task 3: Burst-1 Receipt, GLM Handoff, and CI Trigger

**Files:**
- Create: `GSTClassicalHodgeTwoBurstClosureReceipt.lean`
- Create or update: repository handoff note under `docs/` with exact Burst-1 commit/theorem names.

**Interfaces:**
- Consumes: Task 1 and Task 2 theorem names.
- Produces: one import/receipt surface for CI and one explicit GLM repair contract.

- [ ] **Step 1: Create receipt file**

Import the new Burst-1 modules and `#check` the genuine geometry, zero-map exclusion, finite separation, and detector-visibility theorems.

- [ ] **Step 2: Refresh branch and capture exact Burst-1 commit**

If GLM has advanced the branch, reconcile before writing the handoff.

- [ ] **Step 3: Publish GLM handoff**

State branch, exact commit, new files/theorem names, intended mathematics, and instruction: repair Lean/API/compiler issues only; do not replace geometry with Hodge-equivalent assumptions and do not delete semantic-rigidity audits.

- [ ] **Step 4: Trigger existing Hodge/Lean CI**

Use the repository's existing workflow surface. Record run ID and initial failing jobs for GLM.

- [ ] **Step 5: Classify failures**

Parser/API/tactic/import failures go to GLM; theorem-statement/mathematical failures remain in the assistant lane.

---

### Task 4: Burst-2 Tomography Visibility Crown and Genuine Semantic Closure

**Files:**
- Create: `GSTClassicalHodgeTomographyVisibilityCrown.lean`
- Create: `GSTClassicalHodgeGenuineSemanticClosure.lean`
- Modify only if needed after refresh: public Hodge landing receipt/import surface.

**Interfaces:**
- Consumes: `GenuineCycleClassGeometry`, Task-2 visibility theorem, existing `ProjectiveDetectorVisible.toMomentHit`, existing detector-moment contradiction, `not_hodge_iff_nonempty_omniversalSeparatorGhost`.
- Produces: no surviving omniversal ghost under genuine geometry and a final `BigradedBettiHodgeStatement V H` theorem over the strengthened semantic package.

- [ ] **Step 1: Prove tomography visibility crown**

Compose the finite separation theorem with existing detector rescaling/moment collision; do not reprove tomography internals.

- [ ] **Step 2: Prove ghost extinction**

Show any `OmniversalSeparatorGhost` under `GenuineCycleClassGeometry` yields `False`.

- [ ] **Step 3: Prove strengthened Hodge closure**

Add a theorem of the form:

```lean
bigradedBettiHodge_of_genuineCycleClassGeometry :
  GenuineCycleClassGeometry V H →
  NativeMassCycleClassBridge V H →
  BigradedBettiHodgeStatement V H
```

with the exact minimal additional native-mass input only if still logically required by `ghostSpineSeed`.

- [ ] **Step 4: Reconcile GLM repairs**

Refresh the branch, inspect GLM changes, update imports/theorem references without changing the mathematical route.

- [ ] **Step 5: Final CI**

Trigger/check CI on the integrated head. If failures are compiler/API-only, hand them back to GLM; if mathematical, repair in this lane and re-run.

- [ ] **Step 6: Final audit**

Check `#print axioms` on the public crown, verify no `sorry`, no hidden basis bridge, no arbitrary zero-map-compatible semantic shortcut, and report exact head/run state.
