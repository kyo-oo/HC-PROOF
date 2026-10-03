# General Space GST Hodge Cosmology Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Implement the approved carrier-independent General Space ontology and embed Graph V2, limitless world cosmology, and the classical Hodge native/Betti program calculus into it without weakening the exact Hodge target.

**Architecture:** `GeneralSpace` is an arbitrary universe-polymorphic point/path ontology. Transport, recoordination, realizations, duality, and cohomology are orthogonal capabilities. Existing Graph V2, `Nat × Nat` world cosmology, and Hodge/native/Betti structures become exact realizations/adapters; genuine graded geometric programs become General Space paths whose native and Betti transports are synchronized by the already-proved cycle-class naturality law.

**Tech Stack:** Lean 4.33.0-rc2, pinned Mathlib, existing HC-PROOF GST/Hodge modules, GitHub Actions.

**Spec:** `docs/superpowers/specs/2026-10-03-general-space-hodge-cosmology-design.md`

## Global Constraints

- No built-in finite dimension, metric, Euclidean structure, `Nat × Nat`, or arithmetic carrier in the General Space core.
- Existing GST theorems are preserved as realizations/specializations, not deleted or weakened.
- Do not assume Hodge surjectivity, basis algebraicity, universal sheet reachability, defect-zero, or separator nonexistence.
- Do not introduce `axiom`, `sorry`, or `admit`.
- Fresh modules are not called green until CI/compiler evidence exists.
- Exact Hodge acceptance target remains `GSTClassicalHodgeExactClayStatement.EveryHodgeClassIsFiniteRationalCombination H`.

## Review Focus

- Path composition orientation must agree across transport and graded geometric programs.
- Recoordination must transport intrinsic observables without making coordinates ontological.
- Graph V2 and `Nat × Nat` adapters must be specializations, not core dependencies.
- Hodge synchronization must reuse genuine `GradedGeometricProgram.cycleClass_cycleEval`, not postulate a new naturality field.
- Defect extinction may prove algebraicity only for genuinely program-reached targets; it must not smuggle universal reachability into the foundation.

---

### Task 1: General Space core
**Files:** Create `GSTGeneralSpace.lean`.
**Produces:** `GeneralSpace`, `LawfulPaths`, `Chart`, incidence/graded/causal/spectral capabilities, discrete and preorder constructors.
- [ ] RED: integration smoke imports `GSTGeneralSpace` before the file exists.
- [ ] GREEN: implement the core and compile/import smoke.

### Task 2: Transport
**Files:** Create `GSTGeneralSpaceTransport.lean`.
**Consumes:** `GeneralSpace`.
**Produces:** dependent `TransportSystem`, identity/composition laws, path reachability and composition.
- [ ] RED: smoke imports transport module before it exists.
- [ ] GREEN: implement and compile.

### Task 3: Recoordination
**Files:** Create `GSTGeneralSpaceRecoordination.lean`.
**Consumes:** `TransportSystem`.
**Produces:** bidirectional recoordination, transport inverse laws, invariant observables/predicates.
- [ ] RED then GREEN through smoke import and CI.

### Task 4: Realization
**Files:** Create `GSTGeneralSpaceRealization.lean`.
**Consumes:** core + transport.
**Produces:** charts/realizations and transport morphisms/naturality.
- [ ] RED then GREEN through smoke import and CI.

### Task 5: Duality
**Files:** Create `GSTGeneralSpaceDuality.lean`.
**Consumes:** transport/recoordination.
**Produces:** pointed transport systems, nondegenerate pairings/probes, transport-invariant duality.
- [ ] RED then GREEN through smoke import and CI.

### Task 6: Cohomology
**Files:** Create `GSTGeneralSpaceCohomology.lean`.
**Consumes:** core/transport.
**Produces:** graded cohomology capability with path action and cup compatibility.
- [ ] RED then GREEN through smoke import and CI.

### Task 7: Graph V2 adapter
**Files:** Create `GSTGraphV2GeneralSpaceRealization.lean`.
**Consumes:** General Space modules, `GSTGraphV2NonEuclidean`, `GSTGraphV2ScaleEquivariance`.
**Produces:** Graph-position General Space, SevenAxes/Vertex charts, one-step path theorem, U-cut/observable recoordination specialization.
- [ ] RED then GREEN through smoke import and CI.

### Task 8: World cosmology adapter
**Files:** Create `GSTWorldCosmologyGeneralSpaceRealization.lean`.
**Consumes:** General Space modules, `GSTWorldCosmology`.
**Produces:** `CosmicCell` as one chart realization, completed-field realization, finite-window observation and separation specialization.
- [ ] RED then GREEN through smoke import and CI.

### Task 9: Classical Hodge General Space realization
**Files:** Create `GSTClassicalHodgeGeneralSpaceRealization.lean`.
**Consumes:** General Space modules, exact Hodge/graded geometric program infrastructure, geometric point-cycle class rigidity.
**Produces:** native-cycle General Space faces, geometric Betti realization, supplied/geometric cycle-class comparison, graded-program path space and native/Betti transport systems.
- [ ] RED then GREEN through smoke import and CI.

### Task 10: Synchronization
**Files:** Create `GSTClassicalHodgeGeneralSpaceSynchronization.lean`.
**Consumes:** Task 9.
**Produces:** cycle-class transport morphism, exact native/Betti synchronization, defect transport equation, zero-defect propagation.
- [ ] RED then GREEN through smoke import and CI.

### Task 11: Defect extinction
**Files:** Create `GSTClassicalHodgeGeneralSpaceDefectExtinction.lean`.
**Consumes:** Task 10 + exact Hodge target.
**Produces:** genuine-program target algebraicity, separator contradiction for program-reached targets, General Space specialization of the existing exact target route without assuming universal reachability.
- [ ] RED then GREEN through smoke import and CI.

### Task 12: Integration gate
**Files:** Create `GSTGeneralSpaceIntegrationSmoke.lean`; create `.github/workflows/general-space-hodge.yml`.
**Produces:** one compiler gate importing all eleven modules, rejects proof escapes, runs axiom receipts.
- [ ] First commit smoke/workflow while implementation modules are absent and verify expected RED import failure.
- [ ] After Tasks 1-11, rerun and require GREEN before claiming implementation complete.
