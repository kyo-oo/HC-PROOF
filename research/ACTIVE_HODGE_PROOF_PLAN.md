# GST Hodge — Locked Execution Contract

**Research branch:** \`research/gpt6-native-point-primitive-span-20261017\`  
**Contract revision:** 2026-10-17; this corrects the prior plan, which incorrectly stated the primitive subcase as the final acceptance target.

## The ORIGINAL target — not negotiable

For **every** smooth projective complex variety \(X\), **every** codimension \(p\), and **every** rational Hodge class \(\alpha\in H^{2p}(X,\mathbb Q)\cap H^{p,p}(X)\), construct a rational algebraic codimension-\(p\) cycle on the **original X** and prove

\[
\boxed{\forall X,\forall p,\forall\alpha\in\operatorname{Hdg}^{p}(X)_{\mathbb Q},\ 
  \exists Z\in CH^p(X)_{\mathbb Q}:\operatorname{cl}^{\mathrm{canonical}}_X(Z)=\alpha.}
\]

The exact target is represented by \`GSTClassicalHodgeExactClayStatement.EveryHodgeClassIsRationalAlgebraic\`, and its final verified implementation must match this same quantifier structure and the genuine canonical Betti cycle-class semantics. Do not replace it with a fourfold result, a nonzero primitive source, a finite-dimensional toy model, a hypothesis that the target is algebraic, or a determinant supplied as input.

## Four accountable proof gates

These four gates are the **fixed sequence of acceptance checks**, not a promised bound on the number of unknown auxiliary lemmas needed to solve an open mathematical conjecture. Every proof claim has a yes/no acceptance condition.

| Gate | Precisely what must be delivered | Acceptance test |
| --- | --- | --- |
| **1. Canonical class semantics** | Build the true analytification/fundamental-class, Hodge decomposition, rational Betti cup/Gysin and native-cycle comparison on the **same** \(X\); connect the built map to Stage2G. | No arbitrary user-supplied \`cycleClass\` can masquerade as the canonical map in the final theorem. |
| **2. Full-class reduction** | Prove, using geometric Hard Lefschetz and algebraic hyperplane powers, that actual algebraic representatives for all primitive rational Hodge classes imply representatives for all rational Hodge classes in every codimension. | A Lean theorem with **all** \(X,p,\alpha\) and no additional Hodge-surjectivity field. |
| **3. Universal primitive construction — THE MATHEMATICAL TARGET** | Construct native algebraic representatives for **every** primitive rational Hodge class on **each arbitrary original \(X\)**; every subvariety used must be geometrically constructed, and signed rational combinations are allowed. | An existence/construction theorem with no premise equivalent to the required primitive algebraicity, no target-preimage selector, no assumed full rank, and a canonical Betti equality. |
| **4. Final exact Lean proof** | Instantiate 1–3 and obtain the exact full \`EveryHodgeClassIsRationalAlgebraic\` theorem for all \(X,p,\alpha\). | Whole-dependency Lean compile green; \`#print axioms\` audited; no \`sorry\`, custom axiom, \`False\`-explosion or strengthened hidden hypotheses. |

**Execution priority:** Gate 3 is first in research effort, with Gate 1 pursued only insofar as it supplies the canonical comparison needed by Gate 3. Gate 2 then connects primitive-to-full classes; Gate 4 integrates the finished argument. Gates are a dependency structure, not a device to postpone the main task.

## Mathematically explicit closure of Gate 2

Let \(h\in H^2(X,\mathbb Q)\) be a genuine hyperplane class. The rational Lefschetz decomposition (with Hodge-compatible primitive summands) writes each rational Hodge class as
\[
\alpha=\sum_{j}h^j\smile\beta_j,\qquad
\beta_j\in H^{2(p-j)}(X,\mathbb Q)\cap H^{p-j,p-j}(X)
\text{ primitive}.
\]
If Gate 3 builds a genuine native cycle \(Z_j\) with \(\operatorname{cl}_X(Z_j)=\beta_j\) for **every** required primitive summand, then form the **actual rational algebraic cycle**
\[
Z=\sum_j H^j\cdot Z_j\in CH^p(X)_\mathbb Q
\]
with \(H\) the algebraic hyperplane divisor. Compatibility of the canonical cycle-class map with intersection products gives
\[
\operatorname{cl}_X(Z)
=\sum_j h^j\smile\operatorname{cl}_X(Z_j)
=\sum_j h^j\smile\beta_j=\alpha.
\]
This closes the mathematics of primitive-to-full recovery **once primitive representatives have genuinely been constructed**. This is a proof reduction, not a purported construction of those representatives. Keep the distinction explicit in the Lean theorem contract.

## Direct mathematical attack — three routes, one target

- **A. Actual signed native cycles on arbitrary \(X\):** Work directly on the full quantifiers. Find a geometric mechanism producing a rational signed combination of actual codimension-\(p\) subvarieties with the required primitive class. In degree \(p=2\) on fourfolds, use a *discriminating test* of the mechanism, **not** a renamed final objective. All new lemmas must be exportable to arbitrary \(X,p\), or explicitly recorded as restricted results.
- **B. A genuinely universal algebraic correspondence:** Construct a correspondence *for every original \(X,p\)* whose independently algebraic source and verified Chow/Betti retraction produce the desired primitive class. Existing finite-degree transfer cannot supply an independently algebraic source. Holomorphic form pullback rules out universal domination by the current Fano-only sources.
- **C. Integral geometric realization with algebraicity:** Develop an analytic/integro-geometric construction proving each rational Hodge class has a rational **signed algebraic** realization, including the nontrivial regularity, integrality and algebraicity step. Positive-current minimization alone cannot represent nonzero primitive classes.

**Route stop rule:** no new special Fermat, K3, higher-rank, graph-orbit, determinant, bounded-computation or CI side project unless its result directly proves or refutes a named implication in Gate 3 for arbitrary \(X,p,\alpha\). A green Lean build verifies its exact declaration, not the original conjecture.

## Existing evidence that affects the decision

- \`GSTActualXHodgeResidualProjection.all_primitive_hodge_iff_native_trace_kernel_spans\` gives an exact equivalence, **not** the native trace-kernel source-construction theorem.
- \`GSTActualXHodgeResidualProjection.picardTraceZero_has_zero_primitive_projection\`: the existing divisor-born channel supplies zero primitive output.
- \`GSTResidualZeroLogicalCountermodel\`: positivity plus finite dual detectors does not logically force universal residual zero.
- \`GSTFiniteDominantAllCodimensionDescent\`: finite Chow transfer is valid when source Hodge representatives and the genuine map are established; transfer is not a general-purpose class generator.
- \`research/records/2026-10-17-fano-source-selection-holomorphic-gate.md\`: rational holomorphic-form invariants eliminate the Fano-only universal domination route.
- \`research/records/2026-10-17-primitive-signed-cycle-necessity.md\`: nonzero primitive classes have zero ample degree and require signed native cycles.
- The existing Fermat and K3 results are retained as proved geometry on their exact domains and are **not** used as universal premises without a verified geometric transfer.

## Next proof obligation (unmodified in scope)

**Directly derive an all-\(X\), all-\(p\) source-generation principle from a new GST geometric operation, with actual native cycles and a canonical cycle-class equality.** Its first decisive test can be fourfold codimension two, but that test cannot replace the all-\(X\), all-\(p\) statement.

An acceptable route must name the new geometric object, show how it produces a native cycle **without knowing an algebraic preimage of \(\alpha\)**, and prove the class comparison. If an attempted route fails, identify the precise false implication, not a replacement theorem to celebrate.

## Latest Gate 3 checkpoint — resolved-support subroutine verified

- [All-\(X\), all-\(p\) resolved-support Gysin construction](records/2026-10-17-resolved-support-hodge-source-audit.md), committed in \`GSTUniversalResolvedSupportHodge.lean\`, was **Lean-kernel verified** in the existing integration gate [#39039315761](https://github.com/kyo-oo/HC-PROOF/actions/runs/39039315761). It builds \(f_*D\) from a genuine codimension-\((p-1)\) resolved algebraic support, a Hodge \((1,1)\) lift and Lefschetz \((1,1)\), with exact cycle-class equality.
- **Adversarial scope check:** Given a rational Hodge class, assuming the existence of its resolved codimension-\((p-1)\) Gysin support is, after allowing all such supports, essentially equivalent to already assuming its algebraicity. This is a reusable *constructive support handler*, **not an independent proof that every primitive class has that support**.
- **Separate failure of divisor-only source route:** The primitive plane class \(3[P]-h^2\) on a cubic fourfold with Picard rank one has norm \(24\), while all divisor products lie in the ambient \(h^2\)-line. Thus native hyperplane/divisor operations alone cannot span all primitive directions even on that concrete original variety.
- **One next unresolved step:** Establish independently that an arbitrary primitive rational \((p,p)\) target admits a genuinely new algebraic support/source on the original \(X\). This must be proved by new geometry rather than by a restatement of the support or cycle-class-image condition.

## Current mathematical Gate 3 route: relative original-X geometry

**New verified universal identity:** For every smooth projective \(X\) of even complex dimension \(2p\), a smooth ample hyperplane section \(i:Y\hookrightarrow X\), and every rational primitive middle \((p,p)\) class \(\alpha\),

\[
i^*\alpha=0,\qquad
\alpha\in \operatorname{im}\bigl(H^{2p}(X,Y;\mathbb Q)\to H^{2p}(X;\mathbb Q)\bigr)
 \cong\operatorname{im} H_c^{2p}(X\setminus Y;\mathbb Q).
\]

This follows from injective Gysin \(i_*\), self-intersection \(i_*i^*=h\cup\) and the pair's long exact sequence. The precise rational Betti formulation (plus the no-recovery theorem from plain restriction) is **Lean verified** in [GSTUniversalPrimitiveHyperplaneRelative.lean](../GSTUniversalPrimitiveHyperplaneRelative.lean), [GitHub run #39040307814](https://github.com/kyo-oo/HC-PROOF/actions/runs/39040307814). The full mathematical derivation and cubic fourfold exact test are in [the Mathbox route record](records/2026-10-17-primitive-middle-hyperplane-relative-gate.md).

**Decisive route change:** Ordinary restriction to a hyperplane erases *every* primitive middle class. Hyperplane-only cycle reconstruction cannot be the missing Gate 3 constructor. The relative Betti lift retains the information, but no algebraic-cycle witness has been constructed from that lift. Moreover \(U=X\setminus Y\) is affine; compact positive-dimensional algebraic representatives inside \(U\) are unavailable. The relevant construction must use **signed algebraic cycles on the original X with controlled behavior across Y**, not an algebraic cycle assumed from the outset.

**Next genuine source obligation:** Develop such a boundary-cancellation mechanism from original-\(X\) geometry for an arbitrary primitive \(\alpha\), and prove both its actual algebraicity and its canonical Betti class. Testing on cubic-fourfold primitive \(3[P]-h^2\) distinguishes a successful boundary mechanism from mere hyperplane restriction or divisor products. This is a proof obligation on the route to the original all-\(X\), all-\(p\) theorem, not a substitution for that theorem.

## Reporting and completion

Every update reports: **(i)** the exact original target; **(ii)** which of gates 1–4 acquired a proof; **(iii)** the one next missing mathematical implication; **(iv)** exact commit/CI evidence. No claim of final completion before all four acceptance tests pass.

This is a deterministic **proof-verification plan**, not a probabilistic or arbitrary numbered iteration schedule. There is no finite guaranteed lemma count until a complete valid proof exists.
