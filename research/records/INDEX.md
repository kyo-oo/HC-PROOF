# GST Hodge Research — Construction Program

- [Resolved Gysin supports on every original X](2026-10-17-resolved-support-hodge-source-audit.md) — **Lean green #39039315761**, actual native divisor pushforward in all codimensions for genuinely supported Hodge classes; audit isolates why establishing support for every primitive class is the remaining Gate 3 obligation.

**Current execution plan:** [Three proof gates, fixed all-X primitive target, and no-side-quest rule](../ACTIVE_HODGE_PROOF_PLAN.md).

**Direct-X geometric source refinement:** [Primitive classes require signed algebraic cycles](2026-10-17-primitive-signed-cycle-necessity.md). Positive-degree obstruction verified exactly; the active constructor must produce signed, genuinely algebraic cycles on each original X.

**Latest route decision:** [Wolfram-verified holomorphic-form source-selection gate](2026-10-17-fano-source-selection-holomorphic-gate.md) — finite domination from the current solved Fano source class cannot cover every original smooth projective variety.


## Pinned objective

For every smooth projective complex variety \(X\), every codimension \(p\), and every rational primitive Hodge class \(\alpha\), **construct an algebraic cycle \(Z\) on the original \(X\)** and verify \(\operatorname{cl}_X(Z)=\alpha\) under the canonical geometric Betti cycle-class map.

## Verified mathematics

- **Primitive plane construction:** explicit smooth degree-\(d\) hypersurfaces with algebraic maximal-plane cycles in all even dimensions. [Kernel run #39022821753](https://github.com/kyo-oo/HC-PROOF/actions/runs/39022821753).
- **Unbounded independent directions:** \(d\) disjoint Fermat planes; normal-bundle Gram matrix \(d^2 q I_d-dJ_d\) has full rank for \(m\ge 1,d\ge 3\). [Kernel run #39022662792](https://github.com/kyo-oo/HC-PROOF/actions/runs/39022662792).
- **Geometric measurement bridge:** independence passes to rational cohomology classes with the canonical intersection comparison. [Kernel run #39022986348](https://github.com/kyo-oo/HC-PROOF/actions/runs/39022986348).
- **Threefold codimension two:** constructive Hard Lefschetz + Hodge-(1,1) algebraic representatives, using the genuine geometric cup-identity interfaces. [Kernel run #39019810931](https://github.com/kyo-oo/HC-PROOF/actions/runs/39019810931).
- **All-varieties native primitive projection:** finite native-cycle presentation and primitive extraction on original smooth projective carriers. [Kernel run #39016555036](https://github.com/kyo-oo/HC-PROOF/actions/runs/39016555036).

## Active geometric constructions

1. **Canonical analytic cycle class:** produce the fundamental Betti class of each irreducible subvariety and identify it with the point-generated Stage-2G map.
2. **Universal primitive cycle generation:** construct enough independent algebraic cycles on an arbitrary original \(X\) to cover its entire rational primitive Hodge fiber.
3. **Lean integration:** link all geometric and analytic constructions to the exact Hodge theorem and verify the complete dependency graph.

## Research records

- [Directed-component primitive cycles](2026-10-17-directed-component-primitive-birth.md)
- [Smooth hypersurface source families](2026-10-17-unbounded-hypersurface-primitive-plane.md)
- [Hypersurface kernel proof audit](2026-10-17-unbounded-hypersurface-kernel-audit.md)
- [All-threefold Hodge representatives](2026-10-17-all-threefold-middle-hodge.md)
- [Unbounded Fermat primitive independence](2026-10-17-fermat-unbounded-primitive-rank.md)
- [Fermat measurement bridge](2026-10-17-fermat-realization-bridge-kernel-verified.md)
- [Native point-class integration](2026-10-17-canonical-point-cycle-integration.md)
- [Analytic fundamental-class construction](2026-10-17-analytic-fundamental-class-math-bridge.md)

## Source and verification

Research branch: [`research/gpt6-native-point-primitive-span-20261017`](https://github.com/kyo-oo/HC-PROOF/tree/research/gpt6-native-point-primitive-span-20261017).

Integration review: [Draft PR #3](https://github.com/kyo-oo/HC-PROOF/pull/3). Each theorem is tracked by its source file, precise hypotheses, and corresponding GitHub kernel build.

- [Complete 21-direction Hodge basis of the Fermat cubic fourfold](2026-10-17-fermat-cubic-405-full-hodge-span.md) — 405 explicit planes, 21 independent classes, determinant 27, exact CI [#39026408866](https://github.com/kyo-oo/HC-PROOF/actions/runs/39026408866). Next: arbitrary-X primitive source construction.

- [Fermat cubics in every dimension: complete rational Hodge-cycle construction](2026-10-17-all-even-dimensional-fermat-cubic-hodge-cycles.md) — uniform diagonal-character Fourier proof in even middle degree, hyperplane powers elsewhere; exact checks [#39027053023](https://github.com/kyo-oo/HC-PROOF/actions/runs/39027053023), Lean excess Chern identity [#39027382546](https://github.com/kyo-oo/HC-PROOF/actions/runs/39027382546). Next: arbitrary-X cycle construction.

- [All-codimension finite-degree Chow transfer and projective-bundle composition](2026-10-17-finite-dominant-all-codim-geometry.md) — construct explicit target cycles by normalized geometric pushforward; native defect transport identifies required source geometry. Dedicated GitHub Lean run #39028268013.

- [Rational Hodge-defect injection under geometric finite pullback](2026-10-17-hodge-defect-finite-pullback-functoriality.md) — exact algebraic image equality and deficit-rank monotonicity; Wolfram Hodge-sector source tests guide arbitrary-X geometry.

- [Primitive automorphism-graph cycles on quartic K3 self-products](2026-10-17-k3-graph-primitive-source.md) — actual order-four quartic K3 automorphism gives two independent primitive algebraic graph directions; Wolfram exact rank2; dedicated Lean proof workflow #39029194289.

- [Complete primitive graph criterion for polarized surfaces](2026-10-17-surface-graph-h1-moment-completeness.md) — exact iff using graph coefficient augmentation and rational H¹-action moment; Wolfram irregular-surface tests; corresponding Lean equivalence and primitive rank certificate under geometric Künneth inputs.

- [Unbounded primitive graph-cycle rank in fixed dimension four](2026-10-17-unbounded-fermat-surface-primitive-graph-rank.md) — explicit smooth Fermat surface self-products of every degree d≥4 carry φ(d) independent canonical primitive rational algebraic codimension-two cycles; cyclotomic determinant identity with exact 65-order [CI #39030979414](https://github.com/kyo-oo/HC-PROOF/actions/runs/39030979414).

- [Every dimension D≥4: unbounded-rank primitive algebraic graph cycles](2026-10-17-primitive-projective-tower-unbounded-all-dimensions.md) — external products of Fermat surface graph differences with P^(D−4) retain primitive canonical Betti classes; φ(d) independent representatives for all prime d≥5; Lean binomial tower theorem under CI #39031358849.
