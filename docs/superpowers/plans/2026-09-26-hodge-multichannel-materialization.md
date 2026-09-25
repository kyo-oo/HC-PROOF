# Hodge Multi-Channel Materialization Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Upgrade GST from one diagonal generator per weight to arbitrarily many independent channels at one fixed Hodge weight, then reduce Stage-2G to algebraicity of canonical decoded channel generators.

**Architecture:** The first module combines Wave-II `NShape` multiplicity with a fixed-weight rational channel module and proves exact basis reconstruction. The second proves generator-level materialization under an exact channel equivalence. The third strengthens this to the actual target architecture: the Hodge sector is only required to be a split retract of a possibly larger Wave-II channel universe. A fourth module embeds those finite channels faithfully into the unbounded `Nat` address universe used by rank-free Stage-2.

**Tech Stack:** Lean 4, Mathlib, existing HC-PROOF Wave-II and Stage-2G modules.

**Spec:** Mathematical diagnosis from the HC-PROOF audit: fixed-weight multiplicity and its algebraic materialization are the missing bridge; compilation repair is delegated to GLM in parallel.

## Global Constraints

- Do not replace the Stage-2 semantic stack or reroute existing proofs.
- Do not assume cycle-class surjectivity.
- The geometric obligation is algebraicity of canonical channel generators, never arbitrary-class witnesses.
- Keep Wave-II channels explicit through `NShape`.
- Work on `sol/hodge-multichannel-materialization`; do not interfere with GLM's parallel repairs.
- No local compiler work is required in this pass; leave syntax/compatibility repair to GLM.

## Review Focus

- Zero-hole shapes must be accepted without special axioms.
- Multiple channels must live at one fixed weight, not be spread across different weights.
- The realization theorem must use generator algebraicity only, never arbitrary-class surjectivity.
- The split-retract formulation must allow unused channels and therefore not force exact rank matching.
- The Stage-2G specialization must target `rationalHodgeSubspace (H.hodgeBigrading p)` and `H.cycleClass p` directly.

## Execution Rulings

- **Ruling:** Do not modify `HCProof.lean` during this pass. GLM is actively repairing that shared entry face; use `HCProofHodgeChannels.lean` as an isolated receipt surface to avoid a parallel-edit collision.
- **Ruling:** Strengthen exact channel equivalence to a split retract. Exact equivalence is sufficient but unnecessarily rigid; a retract is the more general mathematical theorem and permits the channel universe to strictly contain the Hodge sector.
- **Ruling:** Add a natural-address bridge. Stage-2 compact realization uses an unbounded `Nat` address universe, so the Wave-II channel addresses should embed into that same universe rather than inventing a second addressing layer.

---

### Task 1: Fixed-weight multi-channel GST Hodge module

**Files:**
- Create: `GSTMultiChannelHodgeCosmology.lean`

**Interfaces:**
- Consumes: `GSTNCohomology.NShape`, `GSTNCohomology.channel_embedding`, `GSTGlobalPureHodgeCosmology`.
- Produces: `HodgeChannel`, `FixedWeightChannelCoordinates`, `standardChannelShape`, `channelBasis`, `channelAddress`, `channelAddress_injective`, `channel_reconstruct`, `same_weight_channel_crown`.

- [x] Define the channel carrier at a fixed Hodge weight.
- [x] Define a canonical `N`-channel shape for every finite `N`.
- [x] Define the canonical Kronecker channel basis.
- [x] Prove Wave-II channel addresses are injective.
- [x] Write exact channel reconstruction and arbitrary-same-weight-rank theorems.
- [ ] GLM compile/repair pass and axiom audit.

### Task 2: Generic channel materialization theorem

**Files:**
- Create: `GSTHodgeChannelMaterialization.lean`

**Interfaces:**
- Consumes: Task 1 channel basis/reconstruction and Stage-2G Hodge data.
- Produces: `ChannelHodgeRealization`, `channelCycleWitness`, `channelCycleWitness_spec`, `channel_hodge_le_cycleClass_range`, `Stage2GChannelMaterialization`, `bigraded_betti_hodge_of_channel_materialization_family`.

- [x] Define generator-level channel realization with no arbitrary-class witness field.
- [x] Define the finite channel superposition cycle witness.
- [x] Write the theorem that its cycle class is the original Hodge class.
- [x] Write the range theorem and Stage-2G specialization.
- [ ] GLM compile/repair pass and axiom audit.

### Task 3: Split-retract strengthening

**Files:**
- Create: `GSTHodgeChannelRetract.lean`

**Interfaces:**
- Consumes: Tasks 1–2.
- Produces: `ChannelHodgeRetract`, `retractCycleWitness`, `retractCycleWitness_spec`, `retract_hodge_le_cycleClass_range`, `Stage2GChannelRetract`, `bigraded_betti_hodge_of_channel_retract_family`.

- [x] Replace exact rank matching by `encode`/`decode` with `decode_encode = id`.
- [x] Require algebraicity only for decoded canonical channel generators.
- [x] Write exact finite-superposition reconstruction.
- [x] Specialize the split-retract theorem to Stage-2G.
- [x] Show the exact-equivalence realization canonically induces a retract.
- [ ] GLM compile/repair pass and axiom audit.

### Task 4: Unbounded address bridge

**Files:**
- Create: `GSTHodgeChannelAddressBridge.lean`

**Interfaces:**
- Consumes: Task 1.
- Produces: `channelAddressLift`, `channelAddressLift_at`, `channelAddressLift_injective`, `channel_address_bridge_crown`.

- [x] Lift fixed-weight finite channels into a `Nat -> ℚ` address field using Wave-II physical addresses.
- [x] Write exact readback at each physical channel address.
- [x] Write faithfulness/injectivity of the lift.
- [x] Preserve Kronecker basis behavior at physical addresses.
- [ ] GLM compile/repair pass and axiom audit.

### Task 5: Isolated repository receipt face

**Files:**
- Create: `HCProofHodgeChannels.lean`

**Interfaces:**
- Consumes: Tasks 1–4 and existing `HCProof`.
- Produces: an isolated import/check/axiom-audit face for comparator integration after GLM repair.

- [x] Import the new Hodge-channel modules without touching `HCProof.lean`.
- [x] Add `#check` receipts for the new crowns.
- [x] Add `#print axioms` receipts for the main materialization/retract theorems.
- [ ] GLM compile/repair pass and final integration into the main entry face when parallel edits settle.
