# GST cardinal-topological limit-to-finite extraction and primitive residual-energy theorem

**Date:** 2026-11-10. **Branch:** research/gpt6-gst-cardinal-intent-reconstruction-20261110. **Scope:** the owner's proposed all-cardinal N, topology tau_n, Hodge sum S=Sum c_alpha ell_alpha and GST Hodge-star/F-function, interpreted as one connected original-X geometry compiler.

## 1. Define the correct canonical topological Hodge target

Fix an arbitrary smooth connected projective complex variety X, complex dimension d, codimension p. Put

\[
W=W_p(X)=H^{2p}(X,\mathbb Q)\cap H^{p,p}(X,\mathbb C),\quad
A=\operatorname{im}(\operatorname{cl}_X:\operatorname{CH}^{p}(X)_{\mathbb Q}\to W),
\quad r=\dim_{\mathbb Q}W<\infty.
\]

Both W and its algebraic subspace A are rational vector spaces. Write W_R=W tensor_Q R with its ordinary finite-dimensional Hausdorff vector-space topology, A_R=A tensor_Q R. The general cardinal/index topology on upstream GST worlds can be more complicated, but any proposed limit in the canonical Hodge target must be interpreted in an explicitly declared topology.

The user's S=sum_(a<omega_1) c_a ell_a can be assigned the exact meaning of a NET of finite partial sums of actual Chow classes:

\[
S_F=\sum_{a\in F}c_a\,\operatorname{cl}_X(Z_a),\quad
F\subset I,\ F\text{ finite},\quad c_a\in\mathbb Q,\ 
Z_a\in\operatorname{CH}^{p}(X)_{\mathbb Q}.
\]

The directed net is indexed by all finite subsets F of an arbitrary ordinal/cardinal index set I. An uncountable sum in W_R means convergence of this NET, not a literal infinite rational Chow cycle.

## 2. NEW THEOREM: cardinal Hodge limit-to-finite extraction

**Theorem.** For every original (X,p),

\[
\boxed{\overline{A}^{\,W_R}=A_R,\qquad A_R\cap W=A.}
\tag{1}
\]

Therefore, if a cardinal-indexed net of finite rational algebraic-cycle class sums S_F converges in W_R to a RATIONAL Hodge class alpha in W, then alpha already has a FINITE rational Chow representative on the original X:

\[
\boxed{\bigl(S_F\longrightarrow\alpha\in W\bigr)
\Longrightarrow
\exists Z\in\operatorname{CH}^{p}(X)_{\mathbb Q}:
\operatorname{cl}_X(Z)=\alpha.}
\tag{2}
\]

**Proof.** Choose a Q-basis a_1,...,a_k of A and extend it to a Q-basis a_1,...,a_r of W. In these coordinates, A equals Q^k times {0} inside Q^r, and W_R is R^r. Q^k is dense in R^k, while R^k times {0} is closed in R^r. Hence the real closure of A is R^k times {0}, proving the first identity. The intersection of this real coordinate plane with Q^r is Q^k times {0}, proving the second identity. Every finite partial sum S_F is in A, so its limit belongs to the closed real span A_R. Since the limit alpha is rational, equation (1) implies alpha in A. By definition of image of cycleClass, some FINITE rational Chow cycle Z realizes alpha. No infinite Chow sum, completion of Chow, or unknown cycle chosen in advance is needed.

**Interpretation:** This is a rigorous and FAITHFUL way the author's infinite/cardinal/topological sum COULD prove Hodge: show for every rational Hodge alpha that native GST born source packets have ordinary Betti/cohomology limit alpha. Exact Chow algebraicity then follows automatically by the finite-extraction theorem. Proving the existence of such approximants from actual geometry remains the open geometric step and cannot be assumed.

## 3. Arbitrary aleph input does not mean uncountably many independent Hodge directions

For a fixed original X,p, W is a finite-dimensional vector space over the COUNTABLE field Q. Its underlying rational set is at most countable, independently of how many complex algebraic cycles, topological worlds or cardinal labels generated the data. Thus a family indexed by aleph_1 or larger can encode extremely rich GEOMETRY while its canonical rational Hodge-class values necessarily repeat.

More strongly, if the unordered sum over I of vectors v_a in a finite-dimensional normed real space is defined as a limit of ALL finite partial sums, then at most COUNTABLY many of the v_a are nonzero. Proof: for every epsilon=1/n, the Cauchy property gives a finite forbidden set F_n outside which each individual term has norm <1/n (compare the two finite partial sums F_n and F_n union {a}). Each set of indices with norm >=1/n is therefore finite. Every nonzero vector has norm >=1/n for some n. Their union over n is countable. This does not prohibit arbitrary-cardinality topological worlds; it identifies the exact cardinal reduction after a convergent ordinary cohomological sum lands on finite-dimensional W_R.

## 4. NEW EXACT POLARIZED GST RESIDUAL-ENERGY CRITERION

The rational Hodge-Riemann bilinear relations, applied to the rational Lefschetz primitive decomposition with an integral ample class, provide a rational positive-definite symmetric form Q on W. It need not already be an algebraic correspondence; it is a rational Hodge-space measurement.

Let B be any finite collection of actually constructed rational Chow cycles, with independent Hodge classes b_1,...,b_k. The true Gram matrix

\[
G=(Q(b_i,b_j))_{i,j=1}^{k}\in\operatorname{Mat}_k(\mathbb Q)
\]

is positive definite, hence invertible. For any rational Hodge alpha, put c_i=Q(b_i,alpha) and define the EXACT rational orthogonal projector

\[
P_B(\alpha)=\sum_{i=1}^k b_i(G^{-1}c)_i\in
\operatorname{span}_{\mathbb Q}\{b_i\}.
\]

The residual R_B(alpha)=alpha-P_B(alpha) is rational, orthogonal to every old known source, and has rational squared energy

\[
\boxed{
E_B(\alpha)=Q(R_B(\alpha),R_B(\alpha))
=Q(\alpha,\alpha)-c^\mathsf T G^{-1}c\ge0.}
\tag{3}
\]

If an actual born native Chow cycle z_new has Hodge class w and v=(Q(b_i,w))_i, the augmented Gram determinant obeys the exact Schur complement formula

\[
\boxed{
\det G_{\mathrm{aug}}
=\det G\,[Q(w,w)-v^\mathsf T G^{-1}v].}
\tag{4}
\]

The bracket is the squared Q-norm of the NEW source after removal of its old-frame component. It is STRICTLY POSITIVE if and only if the native-born class is independent of the old Hodge source span. This is the quantitative version of the author's GST curvature residual/source-birth detector and gives a genuine, rational, falsifiable rank-growth certificate.

For the FULL algebraic image A, choose a Q-basis of A (finite since W is finite). The rational Q-orthogonal projection P_A exists and has rational coefficients. It produces an ACTUAL finite Chow combination because its output lies in A. Consequently

\[
\boxed{
\min_{Z\in\operatorname{CH}^{p}(X)_{\mathbb Q}}
Q(\alpha-\operatorname{cl}_X Z,\alpha-\operatorname{cl}_X Z)
=Q(\alpha-P_A\alpha,\alpha-P_A\alpha).}
\tag{5}
\]

This minimum is 0 exactly when alpha is algebraic. If a rational Hodge class is not in the algebraic image, equation (5) gives a strictly POSITIVE residual energy gap: no native algebraic class can approximate it arbitrarily well in the standard Hodge topology.

**Equivalent new density target:**

\[
\boxed{
\forall\alpha\in W,\ \forall\varepsilon>0,\
\exists Z\in\operatorname{CH}^{p}(X)_{\mathbb Q}:
Q(\alpha-\operatorname{cl}_X Z,\alpha-\operatorname{cl}_X Z)
<\varepsilon^2
\quad\Longleftrightarrow\quad A=W.
}
\tag{6}
\]

The forward implication is the real-limit-to-finite theorem; the reverse is trivial if A=W. For the author's program this is a possible ALTERNATIVE geometric proof route: use certified GST cardinal/topological waves to construct actual Chow sources driving the residual energy below every positive threshold, rather than requiring an exact target Chow inverse at the start. But the approximation property itself is still to be proved; it is mathematically equivalent to rational Hodge algebraicity at the fixed (X,p).

## 5. Precise GST product-topology compiler gate

Suppose the author's simultaneous cardinal input is the full product topological vector space E=R^I with PRODUCT topology, where I is an arbitrary cardinal index type. The finite-support rational packets S=Q^(I) are DENSE in E: any basic neighborhood constrains only finitely many coordinates, which can be approximated by rationals while all other coordinates are zero.

Suppose there exists a CONTINUOUS, SURJECTIVE original-X Hodge landing map q:E -> W_R such that every rational native finite packet s in S lands as an ACTUAL algebraic cycle class: q(s) in A. Then q(S) is dense in W_R because S dense and q continuous surjective. By theorem (1), A=W. This is a SUFFICIENT geometric/topological GST criterion which would prove Hodge for the original (X,p), without assuming target algebraic preimages.

**Adversarial finite-dependence theorem:** If q is also R-LINEAR and E has product topology, q necessarily depends on only FINITELY MANY input coordinates.

Proof: for one real component functional ell∘q, continuity at zero gives a basic product neighborhood U whose finitely many constrained coordinates lie in finite F and whose image has absolute value <1. For any input x that vanishes on F, every real scalar multiple t*x belongs to U (all constrained coordinates still zero). Hence |t ell(q(x))|<1 for every real t, forcing ell(q(x))=0. Thus this component depends only on F. W_R has finite rank r, so the union of the finite coordinate supports of r components is finite. Therefore q factors through R^F for finite F.

**Implication:** merely replacing N by aleph-indexed coordinates with product topology and a continuous linear landing cannot bypass finite-dimensional geometric source birth. To exploit genuinely unbounded topology the GST compiler must either use a different, mathematically defined topology/completion and control its Chow landing, or use certified nonlinear/arbitrary-arity GEOMETRIC world-birth operations. Neither option is automatic from cardinality.

The input topology, continuity and Chow landing conditions must be proved; the theorem does NOT claim the original owner's F-function is linear or must use product topology.

## 6. Exact Wolfram residual-energy test

The committed exact rational source
research/computations/GST_cardinal_topological_Hodge_density_residual_energy_20261110.wl
was fetched after commit and executed in a stateless Wolfram kernel. A four-dimensional rational positive-definite Gram Q had leading principal minors (3,11,52,301), all positive. A test rational Hodge target alpha=(1,1,2,1) and genuine-*model* source directions e1,...,ek produced the exact minimum residual-energy sequence:

- k=1: 113/3;
- k=2: 318/11;
- k=3: 301/52;
- k=4: 0.

Each rational projection was verified orthogonal to its current old span. The new-source Schur complement at k=2 to k=3 was 52/11>0, and the determinant ratio identity held exactly. All finite assertions returned allPassed=True. These are exact linear-algebra tests; they do not instantiate actual Chow cycles on an arbitrary X, do not verify analytic topology on infinite cardinal inputs and do not prove the universal approximation property.

## 7. Connection to the preexisting GST theorems

- GSTPolarizedHodgeResidualEnergy: rational positive polarized residual norm is the natural invariant for (3)--(6).
- GSTHodgeWaveCurvatureResidualStep and GSTHodgeWaveCurvatureCyclicAugmentation: native curvature source born relative to old frame, whose independent detector/rank are certified by the positive Schur complement.
- GSTWorldCosmology: CompactCosmos finite support vs CompletedCosmos coordinate completion; these are NOT literally rational Chow cycles but can serve as topological input to a separately proved geometric F-function.
- GSTGraphV2SelfExpandingCosmology: arbitrary-arity born-world assembly, which would have to output true Chow classes under a verified canonical X landing.
- GSTCardinalConnectedNavigation.lean: verified finite cross-world native/Betti path naturality.
- GSTCardinalSimultaneousOriginalXCompiler.lean: verified native/Betti square for simultaneous finite cardinal packets, genuine source words and curvature detector certificates.
- GSTUniversalChowSourceSaturation.lean: native one-seed source module saturation and common-detector rank bound.
- research/derivations/GST_connected_cardinal_native_source_full_rank_compiler_2026_11_10.md: universal rank-one Chow correspondence, all-rank ORIGINAL GST U+J+M corner, actual dual-cycle single fold compiler and operator criterion.

## 8. What actually changed, and what remains

**New proved results:** arbitrary-cardinal convergent native Chow source sums with a RATIONAL Hodge limit automatically yield a FINITE Chow representative; exact rational polarized minimum-error / Schur-complement source-birth criterion; exact sufficient topological-density/Hodge landing criterion; product-topology linear landing's finite-coordinate dependence theorem.

**Still open original-X result:** generate such approximating native sources with arbitrarily small Hodge residual energy from the author's true GST cardinal-topological wave, curvature, Hodge-star, N-cohomology and world-birth laws, for EVERY rational Hodge class on EVERY smooth projective complex X. The actual native Chow realization and full density are nontrivial geometric hypotheses, not consequences of signal-space cyclicity or cardinal arithmetic alone. No unconditional Hodge proof is claimed.
