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

## Gate 3 — ONE open mathematical implication, not competing plans

**Unchanged finish condition:** for each arbitrary original smooth projective complex \(X\), any \(p\), and any prescribed rational \((p,p)\) Hodge \(\alpha\), independently construct \(Z_\alpha\in CH^p(X)_{\mathbb Q}\) with the **canonical** equality \(\operatorname{cl}_X(Z_\alpha)=\alpha\). Neither a nonzero example nor a cohomological projector alone meets this condition.

**What the completed investigations share:** Fermat planes, blowups, K3 products, tangent-Chern classes, Jouanolou/K₀ bundles and CM–Weil cycles are **source-generation experiments within Gate 3**, not successive changes of the objective. Their exact domains, Lean evidence and mathematical scope are preserved in [research records](records/INDEX.md). We do not open another family merely to obtain a green example.

**Existing GST infrastructure in the live proof:** \`GSTActualXHodgeResidualProjection\` separates known algebraic classes from the unresolved Hodge residual; \`GSTUniversalCodimensionTwoPrimitiveExtraction\` and \`GSTPrimitiveTransverseCycleExtraction\` apply the genuine native Hard-Lefschetz correction; \`GSTPrimitiveAlgebraicMotiveProjector\` handles already-present algebraic correspondences; \`GSTCMQuadraticNativeRankForcing\` supplies an actual irrational CM-action independence principle; \`GSTUniversalCMArithmeticObstruction\` and the direct split Weil source certificate test the remaining source-birth mechanism. These existing laws are **used**, but no GST law has been verified to create a cycle for *every* arbitrary \(\alpha\).

**Completed source-to-original-X algebraization subroutine:** on a smooth affine complement \(U=X\setminus Y\), a genuine affine algebraic codimension-\(p\) source representing \(j^*\alpha\), plus the strictly lower-codimension Hodge theorem on \(Y\), gives the native original-\(X\) cycle \(\overline{Z_U}+i_*D_Y\) with exact class \(\alpha\). This is kernel green at [#39044347980](https://github.com/kyo-oo/HC-PROOF/actions/runs/39044347980), but constructing the **affine source** remains the source-birth obligation.

**Fixed discriminating source-birth test (no family switching):** a genuinely **nonsplit Weil-type abelian fourfold** \(A\) with \(\operatorname{NS}(A)_{\mathbb Q}=\mathbb Q\,\theta\). The actual CM algebraic projector \(\Pi_W\) has a two-dimensional rational Weil \((2,2)\) image. It kills \(\theta^2\), so rational divisor products and CM graph operations on the ambient polarization cannot supply the source. The split CM elliptic-power example provides an independently constructed genuine rank-two source and all-\(p\) proof [#39059438328](https://github.com/kyo-oo/HC-PROOF/actions/runs/39059438328), [#39059702764](https://github.com/kyo-oo/HC-PROOF/actions/runs/39059702764); **its graph divisors do not automatically deform** to the nonsplit original \(A\).

**Major exact simplification, now GREEN:** for the nonsplit original \(A\), one nonzero projected **irreducible codimension-two algebraic subvariety** \(V\) is enough. With actual CM action \(T\), the two classes \(z=\Pi_W\operatorname{cl}_A(V)\ne0\) and \(Tz\) have strictly positive determinant \((x+ay)^2+(by)^2\), so every prescribed rational Weil target has an **explicit** rational native combination of \(V\) and its CM translates. Lean verifies coefficient reconstruction at [#39061912241](https://github.com/kyo-oo/HC-PROOF/actions/runs/39061912241) and finite-native-sum reduction to **one irreducible source** at [#39062250730](https://github.com/kyo-oo/HC-PROOF/actions/runs/39062250730). The [same Mathbox proof record](records/2026-10-17-geometric-weil-cm-isogeny-projector-all-p.md) gives a symbolic first-order Hodge calculation explaining why split mixed graph divisors lose type (1,1) in a nonsplit deformation even while the projected Weil class retains type (2,2).

**New completed constructive source theorem on the SAME Weil test:** For a QM abelian surface \(B\) with division quaternion endomorphisms \(i^2=-1,j^2=3,ji=-ij\), the genuine algebraic graph of \(j\) on original \(A=B\times B\) has nonzero exceptional Weil projection: its explicit rational Betti top-wedge determinant is **−12**, independently checked by Wolfram and by the exact coefficient audit. GST's proven one-source CM-orbit reconstruction therefore supplies every prescribed rational Weil \((2,2)\) class on THIS A. The graph mechanism extends to quaternionic-factor Weil abelian \(2p\)-folds for each \(p\ge2\), with squared graph pairing \(144^{\lfloor p/2\rfloor}4^{p\bmod2}>0\).

**Stronger full-Hodge realization on original generic QM fourfold:** The Hodge group of a generic simple QM surface is an inner form of SL₂; on \(B^2\), ten genuine rational QM/Rosati divisor generators yield algebraic intersections whose exact rational exterior ranks are **(1,10,20,10,1)** in codimensions \(0,1,2,3,4\). These exactly equal the full Hodge-space dimensions, providing an actual prescribed-class algebraic divisor-product construction in every codimension of this original A. The same SL₂ invariant generation extends to all powers \(B^r\). [Mathbox construction and all-p proof](records/2026-10-18-qm-fourfold-all-hodge-divisor-span.md). The quaternion graph and full-Hodge span were checked in the same pinned [GitHub Actions #39064321736](https://github.com/kyo-oo/HC-PROOF/actions/runs/39064321736) — **GREEN** with no sorryAx; the full generic Hodge-group geometry and actual analytic cycle-class comparison are mathematical inputs and not yet fully instantiated as Lean geometric structures.

**Transferred nonsplit-simple construction:** the auxiliary-sixfold construction on the other branch already gives a genuine original-\(A\) codimension-two cycle, **using the named external split-sixfold theorem T6**. Pad \(A\) by an oppositely acted CM elliptic pair \(B\); for a nonzero Weil source \(\Gamma\in CH^3(A\times B)_{\mathbb Q}\), form \(Z=(p_A)_*(\Gamma\cdot p_B^*(\Delta-F_1-F_2))\). The detector is injective on the balanced determinant tensor, so \(\operatorname{cl}(Z)\ne0\) in the original two-dimensional Weil plane. Its actual \((d+1+u)^*\)-translate supplies the second direction for \(u^2=-d\). The [construction, external-source revision and arithmetic CI receipt](records/20261018-weil-fourfold-auxiliary-extraction.md) have been transferred to this GPT-6 branch. The former instruction to discover a relative surface family is no longer the sole frontier: padding/extraction supplies this source conditional on T6.

**Native proof assembly on this branch:** `GSTUniversalCMArithmeticObstruction.auxiliaryWeilEveryMiddleHodgeClass` combines the transferred contraction theorem, the general-\(d\) fourth-power determinant, explicit rational coefficients and the polarization square into a native codimension-two cycle for every middle rational Hodge class in the generic rank-three case. The theorem visibly takes one fixed auxiliary source, extraction and CM maps, the known Hodge decomposition, and their fixed cycle-class comparisons. It assumes no arbitrary-target preimage or cycle-matrix full rank. The full integration is **GREEN [#39068146715](https://github.com/kyo-oo/HC-PROOF/actions/runs/39068146715)** at `b38695e412291e9b8e271ac0ecc6a2b445257074` (8961 build jobs; no sorryAx; printed axiom union only propext, Classical.choice and Quot.sound). Extraction also passed independently on this branch at [#39067876686](https://github.com/kyo-oo/HC-PROOF/actions/runs/39067876686).

**Exact remaining boundary:** the written original-fourfold construction uses T6 and standard canonical Chow–Betti geometry. Those geometric inputs have not been constructed as Lean inhabitants here; a GST-only proof of T6 is also not supplied. Instantiate/formalize these explicit leaves to upgrade the conditional native assembly to a fully geometric Lean theorem. Even that would settle this Weil-fourfold case, not the unchanged arbitrary \(X,p,\alpha\) objective.

**Scope controls:** GitHub green means exactly the Lean declarations and finite computations compile without a reported \`sorryAx\`; it does not by itself instantiate all classical analytic Betti/Hodge interfaces or close Gate 3. No universal claim without a genuine native source and a canonical Betti equality for the prescribed target.

## Reporting and completion

Every update reports: **(i)** the exact original target; **(ii)** which of gates 1–4 acquired a proof; **(iii)** the one next missing mathematical implication; **(iv)** exact commit/CI evidence. No claim of final completion before all four acceptance tests pass.

This is a deterministic **proof-verification plan**, not a probabilistic or arbitrary numbered iteration schedule. There is no finite guaranteed lemma count until a complete valid proof exists.
