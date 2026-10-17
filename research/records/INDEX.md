# GST Hodge Research — Construction Program

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
