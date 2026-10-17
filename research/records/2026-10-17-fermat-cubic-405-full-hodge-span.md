# Mathbox route — complete rational (2,2) Hodge representatives on the Fermat cubic fourfold

## Mathematical target and concrete source

On the smooth Fermat cubic fourfold
`X = {z_0^3+z_1^3+z_2^3+z_3^3+z_4^3+z_5^3=0} ⊂ ℙ⁵_ℂ`,
construct an algebraic representative for **every** rational (2,2) Hodge class on the original X through its canonical geometric Betti cycle-class map. This is a complete test of the full-rank geometric source-generation mechanism, with actual scheme-theoretic planes, rather than a rank lower bound alone.

## 405 actual algebraic planes

There are 15 pairings M of the six coordinate indices into 3 unordered pairs. Each pair (a,b) admits one of the 3 values `λ=-ω^k`, `k=0,1,2`, `ω³=1`. The projective plane defined by `z_b=λ z_a` for all pairs lies on X because `z_b³=-z_a³`. Thus the explicit construction supplies `15·3³=405` genuine codimension-two algebraic planes on X.

Every two such planes intersect in projective dimension r∈{-1,0,1,2}, computed from a *six-variable system of linear equations*, encoded as parity and cube-root phases on the 2-regular union of the two matchings. A connected component contributes one affine dimension exactly when its parity/phase constraints are consistent; projective dimension is affine dimension minus 1. The exhaustive intersection multiplicity distribution, over unordered plane pairs including diagonals, is:

| Projective intersection | Geometric number | Pair count |
| --- | ---: | ---: |
| empty | 0 | 45,360 |
| point | 1 | 31,590 |
| line | -1 | 4,860 |
| coincident plane | 3 | 405 |

**Geometric intersection formula.** A transverse point contributes 1. For a shared line L, the excess-intersection bundle has c₁ degree `deg c₁(N_(P/X)|_L)-deg c₁(N_(L/Q))=0-1=-1`. For a plane P, the normal exact sequence `0→N_(P/X)→O_P(1)^3→O_P(3)→0` gives `c₂(N_(P/X))=3`. Disjoint planes have product zero. These give the *genuine canonical-cycle-class intersection numbers*.

## Full 21-dimensional rank and explicit rational representative

Let `G∈M₄₀₅(ℤ)` be that intersection matrix. Deterministic standard-library Python computes:

- `rank_F101(G)=rank_F103(G)=21`;
- a 21-plane principal Gram minor (zero-index source identifiers)

```text
0, 1, 2, 3, 4, 9, 10, 12, 13, 27, 28, 36, 37, 81,
82, 84, 85, 108, 109, 189, 190
```

has **exact integer determinant 27**, verified by Bareiss fraction-free elimination and independently by SymPy rational determinant.

The Jacobian ring for X is `ℂ[z₀,…,z₅]/(z₀²,…,z₅²)`. By the smooth hypersurface residue/Hodge computation, its degree-three piece has dimension `binom(6,3)=20` and equals the primitive complex (2,2) Hodge component. The hyperplane-square class contributes the remaining dimension, so `dim_ℂ H^{2,2}(X)=21`. The 21 algebraic plane classes with invertible Gram therefore form a ℂ-basis of H^{2,2}(X).

Since their classes are rational, they also span every rational (2,2) Hodge class. For a rational Hodge class α define `b_j=∫_X α∪cl(P_j)∈ℚ`, `G₀=(∫_X cl(P_i)∪cl(P_j))_{i,j=1}^{21}`, and take

`c_i=(1/27)Σ_j adj(G₀)_{ij} b_j ∈ ℚ.`

The **explicit native rational algebraic cycle** `Z(α)=Σ_i c_i [P_i]` satisfies `cl_X(Z(α))=α`. This covers the full primitive part as well as the h²-direction, and uses canonical Betti geometry.

## Machine evidence and boundary

**Exact finite computation**: `research/computations/fermat_cubic_405_rank.py` enumerates all 405 planes, calculates all 82,215 unordered geometric intersection entries, checks the selected 21×21 determinant over ℤ, and independently checks the 405×405 rank modulo 101 and 103. It uses Python 3 standard library only, with no randomness, sampling or floating-point arithmetic.

- Full ordered 405×405 integer matrix SHA256: `ba97d18902a7ecf4a6675ef0f7a664ccdd1f77895bbf3ea38efa8085c5cd1df2`.
- 21×21 exact integer determinant: `27`.
- Jacobi ring dimension calculation: `binom(6,3)+1=21`.
- Narrow CI: `.github/workflows/gst-fermat-cubic-405-rank.yml` (check the latest run tied to its exact commit).
- Previous Lean modules already verify uniform normal Chern coefficients, explicit smooth hypersurface equations, primitive orthogonality and finite-rank detector. The new 405-source finite certificate is currently a Python exact-arithmetic check, **not** a Lean-kernel proof of the complete geometric incidence matrix.

**Research-program next implication:** Turn the construction into a *source-producing operation on arbitrary original X* with an all-X full-rank theorem for its complete rational primitive Hodge fiber. A transfer between different carriers must preserve canonical geometric cycle classes and primitive directions, so the incidence computation by itself is a specialized complete case rather than an all-varieties transfer. The ongoing branch also requires its all-codimension canonical Betti fundamental-class Lean integration.

## Route disposition

Constructive rational Hodge (2,2) completion for an explicit, nontrivial smooth cubic fourfold, using 21 real algebraic plane cycles and exact intersection geometry. Completion of the all-varieties generalization is the continuing program objective.
