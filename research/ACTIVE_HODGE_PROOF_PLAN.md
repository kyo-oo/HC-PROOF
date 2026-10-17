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

## Live Gate 3: affine-source construction and ORIGINAL-X algebraization

**Complete all-codimension reconstruction now kernel verified.** Let \(X\) be any smooth projective complex variety, \(Y\subset X\) a genuine smooth ample boundary divisor and \(U=X\setminus Y\). For any \(p=q+1\), from a native codimension-\(p\) algebraic cycle \(Z_U\) on \(U\) with Betti class \(j^*\alpha\), and the already-established codimension-\(q\) Hodge theorem on \(Y\), the current Lean file constructs a genuine original-\(X\) cycle
\[
\boxed{Z_X=\overline{Z_U}+i_*D_Y,\qquad \operatorname{cl}_X(Z_X)=\alpha.}
\]
The divisor/boundary correction follows from rational cohomology localization, strict Hodge lifting and a native lower-codimension cycle. For \(p=2\), Lefschetz \((1,1)\) supplies that lower-weight cycle on every smooth \(Y\) independently. The first full all-\(p\) Lean induction theorem and the codimension-two case passed the **247-module [Hodge integration #39044347980](https://github.com/kyo-oo/HC-PROOF/actions/runs/39044347980)** at source SHA \`037e7644c69459c242717b7c3b9998952caf880a\`, with the sorryAx audit passing. [Exact proof and Wolfram check](records/2026-10-17-affine-boundary-algebraization-gate.md).

**Next mathematical target, unchanged:** Construct the **affine native codimension-\(p\) source \(Z_U\)** from each prescribed rational \((p,p)\) Hodge class \(j^*\alpha\) in the **lowest weight \(W_{2p}H^{2p}(U,\mathbb Q)\)** of the smooth affine complement. Once produced, all remaining Chow closure and correction operations are verified. The identity \(\mathrm{im}\,j^*=W_{2p}H^{2p}(U)\) for the smooth projective compactification is the precise pure-weight localization constraint.

**Actual algebraic K₀ source construction and pure-degree extraction:** Every original \(X\subset\mathbb P^N\) has a smooth affine Jouanolou model \(J(X)\to X\) with Chow/K₀ and Betti homotopy equivalences. The universal incidence projector \(E_{ij}=x_i\lambda_j/\sum x_k\lambda_k\) is a genuine algebraic idempotent on \(J(X)\); rank-two Clifford and split-Jacobian projectors are likewise explicitly manufactured over their coordinate rings and formalized in \`GSTUniversalResolvedSupportHodge.lean\`. GitHub [#39050631654](https://github.com/kyo-oo/HC-PROOF/actions/runs/39050631654) compiled all source-projector declarations (plus the 247-module Hodge integration) at SHA \`d1003315265cadf6fadeed10bc8e4a75ec7d2213\` without \`sorryAx\`.

**Every codimension has an exact algebraic Chern isolator.** For \(0\le p\le n=\dim X\), the finite Lagrange polynomial \(L_{p,n}(t)=\prod_{j\neq p,0\le j\le n}(t-2^j)/(2^p-2^j)\), applied to algebraic Adams operation \(\psi^2\), gives \(\xi^{\langle p\rangle}=L_{p,n}(\psi^2)\xi\in K_0(X)_{\mathbb Q}\) with \(\mathrm{ch}_i(\xi^{\langle p\rangle})=\delta_{ip}\mathrm{ch}_p(\xi)\). The algebraic spectral identity has been added to Lean and the exact arithmetic to the integration workflow. The all-degree nonambient test is a *genuine virtual K-class* on every smooth degree-\(d\) fourfold containing a plane:
\[
\xi_d=d[\mathcal O_P]-[\mathcal O_T]-\frac{d-1}{2}[\mathcal O_C]
-\frac{d(d^2-1)}{12}[\mathcal O_q],\qquad
\mathrm{ch}(\xi_d)=d[P]-h^2,
\]
with all other Chern-character degrees zero and primitive square \(d(d-1)^3\). [Full uniform GRR proof and next construction contract](records/2026-10-17-universal-adams-k0-pure-chern-realization.md).

**Native higher-rank bundle source, now green:** On every smooth degree-\(d\) fourfold containing an algebraic plane defined by three linear equations, the kernel \(E=\ker(\mathcal O_X(-1)^3\to\mathcal I_P)\) is an honest rank-two algebraic vector bundle with \(c_2(E)=3h^2-[P]\). Thus \(d[P]-h^2=(3d-1)h^2-dc_2(E)\), a nonambient primitive Chern class of norm \(d(d-1)^3\). This source is not merely a virtual K-class: its vector-bundle equations are explicit. Both [all-dimensional primitive CI #39052892131](https://github.com/kyo-oo/HC-PROOF/actions/runs/39052892131) and [247-module Hodge integration #39052892119](https://github.com/kyo-oo/HC-PROOF/actions/runs/39052892119) passed, including the `sorryAx` audits. [Complete syzygy construction and GRR calculation](records/2026-10-17-plane-syzygy-bundle-native-chern-source.md). The adjoining [all-codimension pure source record](records/2026-10-17-pure-algebraic-k0-all-codimensions.md) is independently green at [#39052449104](https://github.com/kyo-oo/HC-PROOF/actions/runs/39052449104).

**One remaining mathematical construction (exact original objective):** Given an arbitrary rational primitive Hodge \(\alpha\) on arbitrary original \(X\), manufacture an independently algebraic idempotent/projective module on \(J(X)\) with \(\mathrm{ch}_p=\pi^*\alpha\). Neither the universal tautological line, the stably-free Jacobian projector nor pullbacks from a single affine quadric generate every primitive direction; the current work identifies actual nonambient K-theory sources and an exact Chern-degree extractor. The source must be produced from \(X,\alpha\), not passed in as an already algebraic representative.

**Scope control:** This is one executable affine source-birth route to the SAME universal Hodge conjecture, not a change to the final theorem. The established middle-relative, matched-boundary, resolved-support, and finite Chow-descent results remain indexed in [research records](records/INDEX.md). Do not add further special-family ranks or conditional source structures unless they advance the actual algebraic affine K/Chow source construction or instantiate a missing canonical Betti comparison.

## Reporting and completion

Every update reports: **(i)** the exact original target; **(ii)** which of gates 1–4 acquired a proof; **(iii)** the one next missing mathematical implication; **(iv)** exact commit/CI evidence. No claim of final completion before all four acceptance tests pass.

This is a deterministic **proof-verification plan**, not a probabilistic or arbitrary numbered iteration schedule. There is no finite guaranteed lemma count until a complete valid proof exists.
