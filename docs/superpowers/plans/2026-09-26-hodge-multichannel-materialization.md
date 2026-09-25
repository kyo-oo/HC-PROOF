# Hodge Multi-Channel Materialization Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add one native theorem layer that upgrades GST from one diagonal generator per weight to arbitrarily many independent channels at one fixed Hodge weight, then prove that algebraicity of those channel generators implies the Stage-2G Hodge target.

**Architecture:** The first module combines Wave-II `NShape` multiplicity with a fixed-weight rational channel module and proves exact basis reconstruction. The second module defines a non-circular channel realization interface over an honest Hodge submodule and linear cycle-class map, constructs the algebraic-cycle witness by finite channel superposition, and specializes the theorem to Stage-2G derived rational `(p,p)` classes.

**Tech Stack:** Lean 4, Mathlib, existing HC-PROOF Wave-II and Stage-2G modules.

**Spec:** Mathematical diagnosis from the HC-PROOF audit: fixed-weight multiplicity is the missing bridge; compilation repair is delegated to GLM in parallel.

## Global Constraints

- Do not replace the Stage-2 semantic stack or reroute existing proofs.
- Do not assume cycle-class surjectivity.
- The only geometric obligation allowed is algebraicity of canonical channel generators plus exact channel coordinates.
- Keep Wave-II channels explicit through `NShape`.
- Work on `sol/hodge-multichannel-materialization`; do not interfere with GLM's parallel repairs.
- No local compiler work is required in this pass; leave syntax/compatibility repair to GLM.

## Review Focus

- Zero-hole shapes must be accepted without special axioms.
- Multiple channels must live at one fixed weight, not be spread across different weights.
- The realization theorem must use basis-generator algebraicity only, never arbitrary-class surjectivity.
- Channel reconstruction must be exact over `ℚ`.
- The Stage-2G specialization must target `rationalHodgeSubspace (H.hodgeBigrading p)` and `H.cycleClass p` directly.

---

### Task 1: Fixed-weight multi-channel GST Hodge module

**Files:**
- Create: `GSTMultiChannelHodgeCosmology.lean`

**Interfaces:**
- Consumes: `GSTNCohomology.NShape`, `GSTNCohomology.channel_embedding`, `GSTGlobalPureHodgeCosmology`.
- Produces: `HodgeChannel`, `FixedWeightChannelCoordinates`, `channelBasis`, `channelAddress`, `channelAddress_injective`, `channel_reconstruct`, `same_weight_channel_crown`.

- [ ] Define the channel carrier at a fixed Hodge weight.
- [ ] Define the canonical Kronecker channel basis.
- [ ] Prove Wave-II channel addresses are injective.
- [ ] Prove every fixed-weight channel vector is the exact finite linear combination of its canonical channel basis.
- [ ] Add axiom receipts and a capstone theorem.

### Task 2: Generic channel materialization theorem

**Files:**
- Create: `GSTHodgeChannelMaterialization.lean`

**Interfaces:**
- Consumes: Task 1 channel basis/reconstruction and Stage-2G Hodge data.
- Produces: `ChannelHodgeRealization`, `channelCycleWitness`, `channelCycleWitness_spec`, `channel_hodge_le_cycleClass_range`, `Stage2GChannelMaterialization`, `bigraded_betti_hodge_of_channel_materialization_family`.

- [ ] Define a realization structure whose fields are an `NShape`, a linear equivalence from the Hodge submodule to fixed-weight channel coordinates, one cycle per channel, Hodge membership of each channel cycle-class, and the exact basis-coordinate law.
- [ ] Define the finite channel superposition cycle witness.
- [ ] Prove its cycle class is exactly the original Hodge class.
- [ ] Prove the Hodge submodule is contained in the range of the supplied cycle-class map.
- [ ] Specialize to Stage-2G derived `(p,p)` subspaces and codimension-`p` algebraic cycles.
- [ ] Add a universal family theorem and axiom receipts.

### Task 3: Wire the new crown into the repository entry face

**Files:**
- Modify: `HCProof.lean`

**Interfaces:**
- Consumes: Task 1 and Task 2.
- Produces: root-level import and `#check` receipts for GLM/comparator integration.

- [ ] Import both new modules after the Stage-2G stack.
- [ ] Add `#check` receipts for the fixed-weight channel crown and Stage-2G channel materialization theorem.
- [ ] Do not alter any existing theorem route.
