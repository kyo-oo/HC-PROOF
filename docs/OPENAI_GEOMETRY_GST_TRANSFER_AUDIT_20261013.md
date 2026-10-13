# OpenAI Mathematics → GST Hodge Geometry: Evidence and Transfer Ledger

**Research branch:** `research/openai-geometry-gst-native-plane-20261013`
**Baseline:** `clean/advanced-gst-hodge-20261009` at `8eccd637ee145b6a5a1df6f3d7e42f302663330d`
**Source:** [OpenAI's public math collection](https://github.com/openai/math), index [overview.tex](https://github.com/openai/math/blob/main/overview.tex); publication date 2026-10-06.
**Index scope:** 98 result *families*, not individual manuscripts, in four geometry-related categories (Algebraic and complex geometry: 36 result families; Convex and metric geometry: 15 result families; Topology: 18 result families; Differential geometry: 29 result families). These are indexed for future review; **NOT** independently validated or all read.
**Verification rule:** metadata or a LaTeX claim does not constitute kernel-checked Lean proof; distinguish formalized hypotheses, actual algebraic constructions, and conditional reductions.

## Fixed HC-PROOF target (do not move it)

`GSTClassicalHodgeNativeExecutablePlane.NativeExecutableGSTPlaneCompleteness`:

```lean
∀ q : Nat, ∀ j : ClassicalHodgeBasisIndex V H q,
  ∃ P : GradedCorrespondenceProgram V H 0 q,
    H.cycleClass q (nativeOutput P) =
      (classicalHodgeBasis V H q j).1
```

Existing *conditional* landing: `GSTClassicalHodgeNativeExecutablePlane.hodge_of_nativeExecutableGSTPlane`, then `GSTClassicalHodgeExactClayStatement.exact_rational_hodge_conjecture_finite_sum`. This is not an unconditional proof. `GSTClassicalHodgePlaneCompletenessTheorem.gst_plane_completeness` concerns intrinsic linear-algebra/graph paths; it does NOT construct the required native algebraic cycles. `GSTClassicalHodgeGSTPlaneAxiomStatus.targetStrictClosure_iff_noGhost` formally certifies that assuming ghost-target closure merely renames the Hodge conclusion.

## Specific OpenAI paper inspected in mathematical source, not just metadata

**Family 032:** [The rational Hodge conjecture for CM abelian varieties](https://github.com/openai/math/tree/main/preprints/The-rational-Hodge-conjecture-for-CM-abelian-varieties-September-30-2026). Inspected manuscript LaTeX:
`build/sections/01-introduction.tex`, `02-tensors.tex`, `03-surface.tex`, `04-theta.tex`, `05a-moduli.tex`, `05b-frobenius.tex`, `05b-satake-frobenius.tex`, `05c-cm-types.tex`, `06-assembly.tex`, `07-consequences.tex` (structural inventory; four-factor, surface, theta and assembly passages examined in detail).

**Geometric program extracted from the manuscript's claims:**

1. Split degree-one cohomology into CM embedding lines. Balanced Hodge-sign lists are connected via finitely many conjugate-paired **four-factor switches** (02-tensors, Theorem 'Four-factor switch' and Proposition 'switch-reduction').
2. A switch line is alleged algebraic if one can find a smooth projective surface `S`, four rational Hodge maps to first cohomology and a **nonzero four-way cup period** on `S` (03-surface, 'Surface criterion').
3. Push `[S]` into the product `A` via `f:S→A`, giving an *algebraic* cycle `Z=f_*[S]` with nonzero pairing on a switch tensor; combine four algebraic divisor kernels `D_i` and apply cup-product/push-pull `p'_* (p^*Z ∪ Π D_i) = k t_β`, `k ≠ 0`. Nonzero scalar descent isolates the algebraic line, subject to all actual hypotheses.
4. The proposed nonzero period comes from theta one-forms on projective ball quotients, variation of rational orthogonal splittings while fixing the total theta datum, arithmetic/Frobenius extraction of CM sources, and finite-sum selection (04-theta through 06-assembly).

**Mathematical boundary:** these claims are about CM abelian varieties (and specified related special families), not arbitrary smooth projective complex varieties. No inference to the unrestricted rational Hodge conjecture is justified without an independently proved general construction. The CM manuscript's mathematical proof and cited deep results require separate verification; no Lean kernel proof was found in its preprint's listed contents.

## Actual Lean construction started, without smuggling a geometric theorem

`GSTClassicalHodgeCMFourFactorGeometry.lean` proves the *arithmetic* lemmas necessary for the CM four-factor reduction:
- conjugate-paired swaps preserve pointwise balance and oddness under conjugation;
- the swap is involutive;
- a nonzero finite mixed period has at least one nonzero cup-product term.

These are genuine standalone reductions, not the missing geometric switch theorem or universal Hodge claim. They are intentionally orthogonal to the conditional Hodge finale.

## Precise geometry sockets for further formal construction

| OpenAI operation | Existing HC-PROOF landing | Required independent theorem |
| --- | --- | --- |
| Algebraic cycles from projective surface pushforward | `GSTClassicalHodgeGeometricCycleClassPointRigidity`, `GSTClassicalHodgeCanonicalPointIncidenceTransfer` | Identify actual surface pushforward point/cycle class with its genuine Betti Gysin action, no arbitrary cycle-class map |
| Algebraic divisor kernels on products | `GSTClassicalHodgeSchemeFiniteCorrespondenceFirewall`, `GSTClassicalHodgeStrictGraphCorrespondence` | Construct a strict correspondence with the needed source-target action; point-finite is weaker than scheme-finite |
| Cup/push/pull correspondence square | `GSTClassicalHodgeIncidenceRealizationEquivalence`, `GSTClassicalHodgeStrictGraphBettiTrace` | Prove `SuppliedPointDirectIncidenceLaw` for the constructed correspondence and identify its genuine cohomological action |
| Nonzero source and spectral generation | `GSTClassicalHodgeClosedCorrespondenceSpectralAmplifier`, `GSTClassicalHodgeGeometryFirstTwoGenerator` | Derive a target basis hit `ClosedCorrespondenceHitsSheet` from explicitly constructed geometry |
| Finite witness collapse | `GSTClassicalHodgeNativeExecutablePlane`, `GSTClassicalHodgeExactClayStatement` | Use existing reconstruction; no new abstract finale is necessary |

**First truly missing theorem:** a concrete geometric data constructor whose output is a scheme-appropriate correspondence and verified cup/Gysin trace on a nonzero surface period, producing the required Hodge basis-sheet hit. This *must not* take target algebraicity or `ClosedCorrespondenceHitsSheet` as an input.

**Proposed per-paper audit statuses:** `indexed`, `read`, `independently verified`, `formalized and CI-green`, `usable for specified special varieties`. Never silently promote one status to another.

## Geometry-related family index (OpenAI catalogue)

This inventory is a finding aid. The presence of a title does not mean the theorem is true or applicable to GST.

### Algebraic and complex geometry — 36 families

| Family | OpenAI title | Source manuscript |
|---|---|---|
| 032 | The rational Hodge conjecture for CM abelian varieties | [Original](https://github.com/openai/math/blob/main/preprints/The-rational-Hodge-conjecture-for-CM-abelian-varieties-October-6-2026/paper.pdf) |
| 033 | Campana's orbifold Iitaka conjecture and logarithmic subadditivity | [Original](https://github.com/openai/math/blob/main/preprints/Orbifold-and-logarithmic-Iitaka-subadditivity-September-26-2026/paper.pdf) |
| 034 | Log abundance and effective Iitaka fibrations | [Original](https://github.com/openai/math/blob/main/preprints/Log-abundance-for-compact-Kahler-spaces-under-logarithmic-Iitaka-subadditivity-October-6-2026/main.pdf) |
| 035 | Threefold log abundance in numerical dimension one in characteristic $p>3$ | [Original](https://github.com/openai/math/blob/main/preprints/Log-abundance-in-numerical-dimension-one-for-threefolds-in-positive-characteristic-October-5-2026/paper.pdf) |
| 036 | Numerical semiampleness and generalized minimal models | [Original](https://github.com/openai/math/blob/main/preprints/Numerical-semiampleness-of-nef-adjoint-classes-on-compact-Kahler-manifolds-October-6-2026/numerical-generalized-abundance.pdf) |
| 037 | The sharp ordinary-double-point volume gap | [Original](https://github.com/openai/math/blob/main/preprints/The-ordinary-double-point-gap-in-every-dimension-September-24-2026/paper.pdf) |
| 038 | Fujita's freeness conjecture | [Original](https://github.com/openai/math/blob/main/preprints/Fujitas-freeness-conjecture-September-23-2026/Fujitas-freeness-conjecture-September-23-2026.pdf) |
| 039 | Nagata's conjecture and maximal Seshadri constants | [Original](https://github.com/openai/math/blob/main/preprints/Nagatas-Conjecture-for-Plane-Curves-September-23-2026/main.pdf) |
| 040 | Bloch's conjecture for complex surfaces | [Original](https://github.com/openai/math/blob/main/preprints/Blochs-Conjecture-for-Surfaces-with-pg-equals-q-equals-0-September-24-2026/paper.pdf) |
| 041 | Hyperk\"ahler SYZ and projective-space bases | [Original](https://github.com/openai/math/blob/main/preprints/Projective-Space-Bases-of-Lagrangian-Fibrations-September-23-2026/main.pdf) |
| 042 | Oka classification for K3 surfaces and other compact complex surfaces | [Original](https://github.com/openai/math/blob/main/preprints/Every-complex-K3-surface-is-Oka-September-23-2026/paper.pdf) |
| 043 | $P=W$ for fixed-determinant moduli spaces | [Original](https://github.com/openai/math/blob/main/preprints/P-equals-W-in-composite-rank-for-fixed-determinant-September-24-2026/P-equals-W-in-composite-rank-for-fixed-determinant-September-24-2026.pdf) |
| 044 | The equivariant cohomological Hikita conjecture for quivers | [Original](https://github.com/openai/math/blob/main/preprints/The-equivariant-cohomological-Hikita-conjecture-for-arbitrary-quivers-September-24-2026/main.pdf) |
| 046 | Counterexamples to Shafarevich holomorphic convexity | [Original](https://github.com/openai/math/blob/main/preprints/A-projective-fourfold-with-large-fundamental-group-and-non-Stein-universal-cover-October-5-2026/large-fundamental-group-non-stein.pdf) |
| 047 | Complex counterexamples to cancellation and affine fibrations | [Original](https://github.com/openai/math/blob/main/preprints/An-explicit-failure-of-complex-affine-space-cancellation-September-23-2026/paper.pdf) |
| 048 | A characteristic-zero counterexample to Lipman--Zariski | [Original](https://github.com/openai/math/blob/main/preprints/A-singular-normal-affine-surface-with-free-tangent-sheaf-September-23-2026/paper.pdf) |
| 049 | A stable-coordinate counterexample in four variables | [Original](https://github.com/openai/math/blob/main/preprints/A-stable-coordinate-that-is-not-a-coordinate-in-four-variables-October-5-2026/stable-coordinate-four-variables.pdf) |
| 050 | A counterexample to Griffiths' positivity conjecture | [Original](https://github.com/openai/math/blob/main/preprints/ample-rank-two-bundles-on-the-quadric-surface-without-griffiths-positive-metrics-September-24-2026/paper.pdf) |
| 051 | Kobayashi's canonical-ampleness conjecture | [Original](https://github.com/openai/math/blob/main/preprints/Canonical-ampleness-of-compact-hyperbolic-Kahler-manifolds-September-23-2026/canonical-ampleness.pdf) |
| 052 | Tangent-bundle splittings and universal covers | [Original](https://github.com/openai/math/blob/main/preprints/Universal-cover-splitting-for-compact-Kahler-manifolds-September-23-2026/paper.pdf) |
| 053 | A counterexample to Pixton's original completeness conjecture | [Original](https://github.com/openai/math/blob/main/preprints/A-high-arity-counterexample-to-Pixton-completeness-in-Chow-September-24-2026/paper.pdf) |
| 054 | Counterexamples to Kuznetsov's rationality conjecture | [Original](https://github.com/openai/math/blob/main/preprints/Irrational-cubic-fourfolds-with-geometric-K3-categories-September-24-2026/Irrational-cubic-fourfolds-with-geometric-K3-categories-September-24-2026.pdf) |
| 055 | Toda's Gepner conjecture and large-volume stability | [Original](https://github.com/openai/math/blob/main/preprints/A-Gepner-stability-condition-on-every-smooth-quintic-threefold-September-24-2026/paper.pdf) |
| 056 | Termination of fourfold minimal model programs | [Original](https://github.com/openai/math/blob/main/preprints/Termination-of-generalized-log-canonical-flips-on-compact-Kahler-fourfolds-October-7-2026/termination-generalized-lc-kahler-fourfolds.pdf) |
| 057 | Campana's abelianity conjecture and special varieties | [Original](https://github.com/openai/math/blob/main/preprints/The-abelianity-conjecture-for-special-compact-Kahler-manifolds-September-23-2026/paper.pdf) |
| 058 | The Koll\'ar--Pardon universal-cover conjecture | [Original](https://github.com/openai/math/blob/main/preprints/Semialgebraic-universal-covers-of-normal-projective-varieties-September-24-2026/paper.pdf) |
| 059 | Counterexamples to Zariski's multiplicity conjecture | [Original](https://github.com/openai/math/blob/main/preprints/Ambiently-homeomorphic-isolated-hypersurfaces-of-multiplicities-two-and-three-September-24-2026/paper.pdf) |
| 060 | The Global Spherical Shell conjecture | [Original](https://github.com/openai/math/blob/main/preprints/Global-Spherical-Shells-on-Minimal-Surfaces-of-Class-VII-September-24-2026/paper.pdf) |
| 062 | The LeBrun--Salamon conjecture and projective contact classification | [Original](https://github.com/openai/math/blob/main/preprints/Contact-Fano-manifolds-and-the-LeBrun-Salamon-conjecture-September-23-2026/paper.pdf) |
| 063 | The generalized Mukai conjecture | [Original](https://github.com/openai/math/blob/main/preprints/The-Generalized-Mukai-Conjecture-September-24-2026/article.pdf) |
| 064 | The $\mu$-constant problem for surface singularities | [Original](https://github.com/openai/math/blob/main/preprints/Topological-triviality-of-mu-constant-families-of-surface-singularities-September-24-2026/main.pdf) |
| 065 | Virasoro constraints for complete intersections and projective bundles | [Original](https://github.com/openai/math/blob/main/preprints/Virasoro-Constraints-under-Projectivization-October-5-2026/virasoro-constraints-under-projectivization.pdf) |
| 066 | Bounded klt complements for Fano contractions | [Original](https://github.com/openai/math/blob/main/preprints/Bounded-klt-complements-for-Fano-contractions-September-25-2026/Bounded-klt-complements-for-Fano-contractions-September-25-2026.pdf) |
| 067 | The Campana--Peternell conjecture in dimension six | [Original](https://github.com/openai/math/blob/main/preprints/The-Campana-Peternell-conjecture-in-dimension-six-September-25-2026/main.pdf) |
| 068 | Anticanonical nonvanishing under smooth semipositivity | [Original](https://github.com/openai/math/blob/main/preprints/Anticanonical-nonvanishing-from-smooth-semipositivity-September-26-2026/main.pdf) |
| 069 | Quantum geometric Langlands at irrational level | [Original](https://github.com/openai/math/blob/main/preprints/Global-quantum-geometric-Langlands-at-irrational-level-October-4-2026/quantum-langlands.pdf) |

### Convex and metric geometry — 15 families

| Family | OpenAI title | Source manuscript |
|---|---|---|
| 087 | The Mahler conjectures and symplectic width | [Original](https://github.com/openai/math/blob/main/preprints/The-symmetric-Mahler-conjecture-and-its-equality-cases-September-22-2026/paper.pdf) |
| 088 | Petty's projection-volume conjecture and simplex counterexamples | [Original](https://github.com/openai/math/blob/main/preprints/Pettys-projection-volume-conjecture-in-dimensions-at-least-four-September-24-2026/paper.pdf) |
| 089 | Bounded-distortion $L_1$ embeddings of planar and bounded-treewidth graphs | [Original](https://github.com/openai/math/blob/main/preprints/Planar-Graph-Metrics-Embed-into-L1-with-Constant-Distortion-September-23-2026/paper.pdf) |
| 090 | Universal optimality of the triangular lattice | [Original](https://github.com/openai/math/blob/main/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf) |
| 091 | The logarithmic Brunn--Minkowski conjecture | [Original](https://github.com/openai/math/blob/main/preprints/The-logarithmic-Brunn-Minkowski-conjecture-September-23-2026/paper.pdf) |
| 092 | The optimal order of convex-body covering density | [Original](https://github.com/openai/math/blob/main/preprints/A-single-lattice-covering-bound-of-order-n-log-n-September-23-2026/paper.pdf) |
| 093 | Dimension-free logarithmic Sobolev inequality for subgaussian log-concave measures | [Original](https://github.com/openai/math/blob/main/preprints/A-dimension-free-logarithmic-Sobolev-inequality-for-subgaussian-log-concave-measures-September-23-2026/paper.pdf) |
| 094 | Subpolynomial dimension reduction in $L_p$ | [Original](https://github.com/openai/math/blob/main/preprints/Subpolynomial-dimension-reduction-in-Lp-September-23-2026/paper.pdf) |
| 095 | Hyperbolicity cones without semidefinite lifts | [Original](https://github.com/openai/math/blob/main/preprints/Hyperbolicity-Cones-Without-Semidefinite-Lifts-October-5-2026/nonliftable-hyperbolicity.pdf) |
| 096 | The Gaussian propeller conjecture | [Original](https://github.com/openai/math/blob/main/preprints/The-Gaussian-Propeller-Bound-in-Every-Dimension-September-24-2026/main.pdf) |
| 097 | The Euclidean Steinitz--Bergstr\"om conjecture | [Original](https://github.com/openai/math/blob/main/preprints/The-Euclidean-Steinitz-Bergstrom-theorem-September-24-2026/The-Euclidean-Steinitz-Bergstrom-theorem-September-24-2026.pdf) |
| 098 | A negative answer to the Lang--Plaut problem | [Original](https://github.com/openai/math/blob/main/preprints/A-doubling-Hilbert-subset-with-no-finite-dimensional-bi-Lipschitz-embedding-September-25-2026/main.pdf) |
| 099 | The sharp distortion of edit distance into $\ell_1$ | [Original](https://github.com/openai/math/blob/main/preprints/Edit-Distance-in-l1-Matching-Bounds-up-to-Constants-in-the-Exponent-September-27-2026/paper.pdf) |
| 100 | A counterexample to Bang's cylinder-covering bound | [Original](https://github.com/openai/math/blob/main/preprints/Finite-angular-cylinder-covers-below-the-half-area-bound-September-27-2026/main.pdf) |
| 101 | The sharp simplex conjecture for isotropic constants | [Original](https://github.com/openai/math/blob/main/preprints/A-sharp-entropy-bound-and-the-simplex-inequality-for-isotropic-constants-October-5-2026/isotropic-simplex.pdf) |

### Topology — 18 families

| Family | OpenAI title | Source manuscript |
|---|---|---|
| 304 | The Hilbert--Smith conjecture in every dimension | [Original](https://github.com/openai/math/blob/main/preprints/The-Hilbert-Smith-conjecture-in-every-finite-dimension-September-23-2026/paper.pdf) |
| 305 | Counterexamples to disk embedding and Wall's manifold conjecture | [Original](https://github.com/openai/math/blob/main/preprints/A-boundary-only-obstruction-to-four-dimensional-disk-embedding-September-24-2026/paper.pdf) |
| 306 | The purely cosmetic surgery conjecture for knots in $S^3$ | [Original](https://github.com/openai/math/blob/main/preprints/Purely-Cosmetic-Surgery-on-Knots-in-the-Three-Sphere-September-23-2026/paper.pdf) |
| 307 | Failure of rational injectivity for maximal coarse assembly | [Original](https://github.com/openai/math/blob/main/preprints/Failure-of-rational-injectivity-for-maximal-coarse-assembly-October-5-2026/paper.pdf) |
| 308 | Smith--Toda complexes at every height with varying primes | [Original](https://github.com/openai/math/blob/main/preprints/Finite-Smith-Toda-Complexes-at-Varying-Primes-September-23-2026/paper.pdf) |
| 309 | The Kervaire invariant problem at the prime three | [Original](https://github.com/openai/math/blob/main/preprints/The-Kervaire-Invariant-Problem-at-the-Prime-Three-September-24-2026/paper.pdf) |
| 310 | Quillen's conjecture in rational homology | [Original](https://github.com/openai/math/blob/main/preprints/Rational-homology-and-Quillens-conjecture-September-24-2026/paper.pdf) |
| 311 | Chai's invariant-ideal conjecture | [Original](https://github.com/openai/math/blob/main/preprints/Stabilizer-Orbits-and-Thick-Tensor-Ideals-of-Dualizable-Kn-Local-Spectra-September-24-2026/paper.pdf) |
| 312 | The Grothendieck homotopy hypothesis | [Original](https://github.com/openai/math/blob/main/preprints/The-Grothendieck-homotopy-hypothesis-via-elementary-expansions-September-24-2026/paper.pdf) |
| 313 | Finite generation for the $K(n)$-local sphere | [Original](https://github.com/openai/math/blob/main/preprints/Finite-generation-for-the-Kn-local-sphere-September-24-2026/Finite-generation-for-the-Kn-local-sphere-September-24-2026.pdf) |
| 314 | The chromatic Smith fixed-point problem for finite $p$-groups | [Original](https://github.com/openai/math/blob/main/preprints/Cyclic-Length-and-Chromatic-Fixed-Point-Loss-September-24-2026/Cyclic-Length-and-Chromatic-Fixed-Point-Loss-September-24-2026.pdf) |
| 315 | The four-dimensional Singer conjecture | [Original](https://github.com/openai/math/blob/main/preprints/The-Singer-conjecture-in-dimension-four-September-25-2026/paper.pdf) |
| 316 | Curtis’s conjecture | [Original](https://github.com/openai/math/blob/main/preprints/The-Stable-Hurewicz-Image-of-the-Sphere-at-Two-September-25-2026/paper.pdf) |
| 317 | Thomason model structures in every strict higher dimension | [Original](https://github.com/openai/math/blob/main/preprints/Thomason-Model-Structures-in-Every-Strict-Higher-Dimension-September-25-2026/paper.pdf) |
| 318 | Chromatic splitting: counterexamples and filtrations | [Original](https://github.com/openai/math/blob/main/preprints/Filtered-chromatic-splitting-at-generic-primes-September-25-2026/paper.pdf) |
| 319 | Counterexamples to the Hahn--Wilson conjecture at height two | [Original](https://github.com/openai/math/blob/main/preprints/Counterexamples-to-the-Hahn-Wilson-conjecture-at-height-two-September-26-2026/paper.pdf) |
| 320 | A four-dimensional counterexample to Borel rigidity | [Original](https://github.com/openai/math/blob/main/preprints/Nonhomeomorphic-closed-aspherical-four-manifolds-with-the-same-homotopy-type-October-4-2026/paper.pdf) |
| 321 | A counterexample to Wall's finite D(2) conjecture | [Original](https://github.com/openai/math/blob/main/preprints/A-Counterexample-to-Walls-D2-Problem-October-6-2026/wall-d2-counterexample.pdf) |

### Differential geometry — 29 families

| Family | OpenAI title | Source manuscript |
|---|---|---|
| 333 | Smooth isometric immersions of surfaces into $\mathbb R^4$ | [Original](https://github.com/openai/math/blob/main/preprints/Smooth-isometric-immersions-of-closed-surfaces-into-Euclidean-four-space-September-23-2026/paper.pdf) |
| 334 | A smooth surface metric with no local immersion in $\mathbb R^3$ | [Original](https://github.com/openai/math/blob/main/preprints/A-Smooth-Metric-with-No-Local-Isometric-Immersion-into-Three-Space-September-24-2026/paper.pdf) |
| 335 | Gromov's integral scalar-curvature inequality | [Original](https://github.com/openai/math/blob/main/preprints/An-integral-scalar-curvature-bound-for-real-simplicial-volume-October-5-2026/v126-proof.pdf) |
| 336 | Spectral scalar curvature and codimension-two width | [Original](https://github.com/openai/math/blob/main/preprints/Spectral-scalar-curvature-and-uniform-Urysohn-width-October-5-2026/main.pdf) |
| 337 | Cartan--Hadamard isoperimetry and CAT$(0)$ fillings | [Original](https://github.com/openai/math/blob/main/preprints/Generalized-Cartan-Hadamard-isoperimetry-and-Euclidean-equality-rigidity-September-23-2026/paper.pdf) |
| 338 | Yau's uniformization conjecture | [Original](https://github.com/openai/math/blob/main/preprints/Uniformization-of-complete-Kahler-manifolds-with-positive-bisectional-curvature-September-23-2026/paper.pdf) |
| 339 | Katok's entropy rigidity conjecture | [Original](https://github.com/openai/math/blob/main/preprints/Entropy-equality-and-local-symmetry-in-negative-curvature-September-23-2026/paper.pdf) |
| 340 | A counterexample to the nearby Lagrangian conjecture | [Original](https://github.com/openai/math/blob/main/preprints/A-counterexample-to-the-nearby-Lagrangian-conjecture-September-23-2026/paper.pdf) |
| 341 | Donaldson's hypersymplectic deformation conjecture | [Original](https://github.com/openai/math/blob/main/preprints/Deforming-hypersymplectic-four-manifolds-to-hyperkahler-triples-October-7-2026/paper.pdf) |
| 342 | Donaldson's tamed-to-compatible conjecture | [Original](https://github.com/openai/math/blob/main/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf) |
| 343 | Sharp symplectic ball-packing criteria in higher dimensions | [Original](https://github.com/openai/math/blob/main/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf) |
| 344 | The metric Blaschke conjecture | [Original](https://github.com/openai/math/blob/main/preprints/The-metric-Blaschke-theorem-September-23-2026/paper.pdf) |
| 345 | Infinitely many closed geodesics on spheres and three-manifolds | [Original](https://github.com/openai/math/blob/main/preprints/Infinitely-many-closed-geodesic-images-on-every-Riemannian-sphere-September-24-2026/paper.pdf) |
| 346 | Sharp singular-set bounds for stationary integral varifolds | [Original](https://github.com/openai/math/blob/main/preprints/A-Codimension-One-Bound-for-the-Singular-Set-of-a-Stationary-Integral-Varifold-October-5-2026/varifold-singular-dimension.pdf) |
| 347 | Counterexamples to strong forms of Arnold's fixed-point conjecture | [Original](https://github.com/openai/math/blob/main/preprints/Hamiltonian-Fixed-Points-Below-the-Stable-Morse-Number-in-Dimension-Twenty-Two-October-5-2026/hamiltonian-fixed-points-below-stable-morse-number.pdf) |
| 348 | Nonnegatively curved Einstein four-manifolds and a topological gap | [Original](https://github.com/openai/math/blob/main/preprints/Zero-Plane-Rigidity-for-Einstein-Four-Manifolds-October-4-2026/einstein-boundary.pdf) |
| 349 | The Solomon--Yau least-volume conjecture | [Original](https://github.com/openai/math/blob/main/preprints/The-Solomon-Yau-least-volume-theorem-September-23-2026/paper.pdf) |
| 350 | Yau's nodal conjecture: surfaces and counterexamples | [Original](https://github.com/openai/math/blob/main/preprints/Sharp-nodal-length-on-smooth-surfaces-September-23-2026/paper.pdf) |
| 351 | Scalar curvature detects four-dimensional Ricci-flow singularities | [Original](https://github.com/openai/math/blob/main/preprints/A-closed-Ricci-flow-with-bounded-scalar-curvature-and-finite-time-curvature-blowup-September-24-2026/paper.pdf) |
| 352 | Finite-time singularity of Calabi flow | [Original](https://github.com/openai/math/blob/main/preprints/A-finite-time-singularity-of-Calabi-flow-on-projective-space-September-24-2026/paper.pdf) |
| 353 | The sharp dimension threshold for affine Bernstein rigidity | [Original](https://github.com/openai/math/blob/main/preprints/Smooth-Nonquadratic-Affine-Maximal-Graph-in-Dimension-Ten-October-5-2026/affine-maximal-dimension-ten.pdf) |
| 354 | Isoperimetric regions in the cubic three-torus | [Original](https://github.com/openai/math/blob/main/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf) |
| 355 | Unique tangent flows at the first surface singularity | [Original](https://github.com/openai/math/blob/main/preprints/Tangent-flow-uniqueness-2026-09-24/paper.pdf) |
| 356 | Gigli's characterization of Alexandrov curvature | [Original](https://github.com/openai/math/blob/main/preprints/Giglis-distributional-curvature-characterization-of-Alexandrov-spaces-September-24-2026/main.pdf) |
| 357 | Bi-Lipschitz coordinates at every regular RCD point | [Original](https://github.com/openai/math/blob/main/preprints/Bi-Lipschitz-Coordinates-at-Regular-Points-of-Noncollapsed-RCD-Spaces-September-25-2026/paper.pdf) |
| 358 | A three-manifold with no conjugate points and no nonpositively curved metric | [Original](https://github.com/openai/math/blob/main/preprints/A-Three-Manifold-Without-Conjugate-Points-and-Without-a-Nonpositively-Curved-Metric-September-24-2026/paper.pdf) |
| 359 | Negative K\"ahler curvature without bounded holomorphic coordinates | [Original](https://github.com/openai/math/blob/main/preprints/A-negatively-pinched-Kahler-threefold-without-bounded-holomorphic-coordinates-September-25-2026/paper.pdf) |
| 360 | Villani’s convexity conjecture and regular optimal transport | [Original](https://github.com/openai/math/blob/main/preprints/Global-Support-and-Convex-Injectivity-Domains-under-Weak-MTW-September-25-2026/paper.pdf) |
| 361 | Counterexamples to Yau's harmonic dimension bound | [Original](https://github.com/openai/math/blob/main/preprints/A-counterexample-to-integer-degree-harmonic-dimension-comparison-September-25-2026/paper.pdf) |
