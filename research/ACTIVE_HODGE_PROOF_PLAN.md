# GST Hodge — Active Proof Plan

**Checkpoint:** 2026-10-17; branch research/gpt6-native-point-primitive-span-20261017; incoming SHA 593d401cd8cc2f774439955ab71aae67008731e3.

## ONE acceptance target

For every smooth projective complex variety X, every codimension p and every rational primitive (p,p)-Hodge class α, **construct an actual native rational algebraic cycle Z on the ORIGINAL X** and derive
\[
\operatorname{cl}^{\mathrm{canonical}}_X(Z)=\alpha.
\]
The final artifact is a Lean theorem whose assumptions are standard verified geometric axioms/theorems, not the desired primitive cycle, an arbitrary full-rank determinant, an assumed Hodge-surjective correspondence, or an unconstrained cycleClass field.

## The three gates

| Gate | Exact acceptance criterion | Status and next task |
| --- | --- | --- |
| **I — Canonical geometry** | The point-class mapping is realized by true analytic subvariety fundamental classes and identified with Stage2G cycleClass, with geometric cup/Gysin naturality. | Point-generated extension and rigidity verified; implement actual fundamental-class comparison. |
| **II — Universal primitive source** | For arbitrary original X and a primitive α, construct a native Z with canonical class α. | **Primary mathematical priority.** Finite trace projection and algebraic-image normalization already implemented. Native trace-kernel spanning is the unresolved theorem. |
| **III — Exact kernel assembly** | Complete I and II, wire into GSTClassicalHodgeExactClayStatement / HodgeConjecture.lean, pass complete imports, axiom audit, and exact target test. | Supporting Lean integration green at run 39027382555; only promote when I+II feed final theorem. |

These are **proof obligations**, not a promise that the open conjecture can be solved in three routine calls. The number of auxiliary mathematical lemmas is not known.

## Execute Gate II: fixed, narrow research sequence

**Target file and theorem:** GSTActualXHodgeResidualProjection.lean, around \`all_primitive_hodge_iff_native_trace_kernel_spans\` (line 1217 at checkpoint). The current theorem reduces primitive algebraicity to honest native trace-kernel spanning. The needed new result is a **construction**, not a second equivalence.

1. **Direct signed source on X (priority route).** Starting from a rational primitive Hodge target α, construct a **signed rational difference of genuine codimension-p subvarieties on X**; verify its degree-zero constraint, its nonzero primitive measurement, and its canonical Betti class without assuming a target preimage. A single positive effective representative cannot have nonzero primitive class by ample-degree positivity (see the signed-cycle route audit). First difficult test: codimension two in arbitrary smooth projective complex fourfolds. Record the actual algebraic incidence, deformation, analytic-cycle or integral calibration mechanism; do not substitute a target-dependent chosen preimage.
2. **Geometric correspondence (backup).** For an arbitrary original X, exhibit a genuine Chow/Betti correspondence to a source with independently established representatives and a split injection on the required Hodge sector. Check H^(k,0) and other source invariants FIRST. Existing finite-degree descent only transports already represented source classes.
3. **Signed integral-geometric reconstruction (independent backup).** Work with differences of analytic/algebraic currents or separately constructed effective components. Verify rational integral homology, complex-analytic regularity and multiplicity integrality for each component. The primitive class has zero ample degree, so positivity of a single effective cycle is insufficient.

## Decisions from the actual proof sources

- \`GSTActualXHodgeResidualProjection.picardTraceZero_has_zero_primitive_projection\` proves the existing divisor-born trace-zero construction has **zero primitive output**. Deprioritize divisor-only variants.
- \`GSTResidualZeroLogicalCountermodel\` records the exact logical reason positive quadratic energy, finite detector rank and a native projection **alone do not force** a primitive residual to vanish. No repetition of positivity-only closure.
- Verified Fermat and K3 source families provide genuine independent classes, but their unbounded **rank over varying X** is a different assertion from complete spanning on EACH arbitrary fixed X.
- **Wolfram source-selection filter:** Fermat cubic fourfold and its projective bundles have h^(1,0)=h^(2,0)=0. X=E×P³ has h^(1,0)=1, and X=K3×P² has h^(2,0)=1. A generically finite morphism from the former solved Fano sources to either target would inject a nonzero target holomorphic form into a zero source space, so that proposed universal Fano-source domination fails. Exact result in [the Mathbox route audit](records/2026-10-17-fano-source-selection-holomorphic-gate.md). The open conjecture itself is not tested by this obstruction.

## NO-SIDE-QUEST rule

Do **not** spend further research cycles creating a fourth special-variety rank example, an additional equivalent Hodge statement, another Fano-source covering lemma, or another CI workflow, **unless it changes the truth of an identified all-X implication**.

A new result counts as progress on the main target only if it:
1. Constructs an algebraic class in a genuinely new arbitrary-X Hodge direction, **or**
2. Proves a structural all-X step with source geometry and canonical comparison that was not previously available, **or**
3. Definitively rules out one proposed universal mechanism and changes the research route.

CI GREEN reports only that the exact Lean declarations compile at their written hypotheses. It is **not** a fourth proof gate.

## Next execution handoff

**Next mathematical lemma to attack:** for a primitive rational (2,2) Hodge class α on arbitrary smooth projective fourfold X, construct a **signed native algebraic codimension-two cycle** by an explicit X-intrinsic geometric process. Prove its ample degree is zero, its primitive intersection against α is detected, and its canonical class equals α. The algebraic source and full rank must come from the process, never from a target preimage premise. First open implication: algebraic source existence on X, not finite presentation of already algebraic sources.

**Check before editing:** reread the original exact theorem, \`GSTActualXHodgeResidualProjection\` lines 1190–1260, \`GSTClassicalHodgeGeometricCycleClassPointRigidity\` and the holomorphic source-selection gate. Preserve the existing green branches and original proof claims. Record each attempt with its first unresolved statement rather than creating more generalized supporting modules.

**Completion rule:** only label the universal target complete when all three gates are satisfied by the SAME genuine geometric cycleClass and the exact all-X theorem passes a Lean kernel proof audit.

**Signed-cycle source checkpoint:** [Exact primitive degree-zero and positivity theorem](records/2026-10-17-primitive-signed-cycle-necessity.md). The cubic example Z=3[P]-h² has degree zero and primitive norm 24; all positive effective representatives have positive ample degree.
