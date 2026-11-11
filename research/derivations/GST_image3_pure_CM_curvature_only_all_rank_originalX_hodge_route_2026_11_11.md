# GST original CM curvature alone gives an all-rank native single-fold: exact finite and universal proof

**Date** 2026-11-11. **Author's original mathematical program:** GST / Hodge antecedent.
**Branch:** \`research/gpt6-image3-cm-curvature-only-ranked-source-20261111\`,
forked from the certified prior image-3 original GST branch, without modifying the owner's active research proof branch.

## Target and precise evidence status

**TARGET of the owner's actual Hodge hypothesis:**
for EACH original smooth projective complex X, EACH codimension p, and
its CANONICAL rational Hodge space W_p(X), construct a genuine
algebraic correspondence Γ on X×X with rational Betti action T, and a
genuine native Chow seed Z0, such that:
1. cl_X(Γ Z)=T(cl_X Z) on all genuine native cycles;
2. [cl_X Z0,T cl_X Z0,...,T^(r-1) cl_X Z0] has rank r=dim_Q W_p(X);
3. a RATIONAL geometric moment detector gives nonzero Hankel
   determinant (derived from full orbit rank);
4. the construction exists for all X,p, with the CANONICAL cycle class.

The author's existing Lean \`GSTHodgeSingleHypothesisConditional.lean\`
proves that THAT antecedent implies rational Hodge algebraicity.
Neither the antecedent nor Hodge are assumed here.

**New proved result in THIS attack:** FULL RANK at every prescribed
finite rank r **INSIDE THE ORIGINAL GST SIGNAL/N-COHOMOLOGY CARRIER**,
using PURE DERIVED ORIGINAL CM CURVATURE [J,M] transported across
original N-cohomology worlds, with **ZERO local SURVIVE and ZERO local
curvature source**. A rank-r CYCLIC RATIONAL QUOTIENT plus Hankel
detector is constructed for every r. The original-X Chow/Betti square
is separately proved given actual certified original-X operators.
The universal geometric existence/rank landing is still unproved.

This route differs from prior
\`GST_image3_rank_adaptive_rational_CM_zero_local_companion_2026_11_11.md\`:
the old global source was the ORIGINAL SURVIVE M. Here the **ONLY
interworld source is the TRUE SECONDARY CM CURVATURE [J,M]**. This is
not a relabeling: [J,M] has different rank (6 vs M's rank 3) and
anti-commutes with J, and has an independent degree-31 determinant.

## 1. Original physical GST operators, untouched

Read \`GSTGraphV2CMWaveFusion.lean\`. Wave-I signals are exactly the
ORIGINAL twelve physical carry/trit cells \(\{0,1,2,3\}\times\{0,1,2\}\).
\(U\) is the true 5-period information shuffle, \(J\) the rational
signed CM mirror with \(J^2=-I\), \(M\) the exact TRUE SURVIVE source
multiplication, and \(v=e_{(0,0)}+e_{(0,1)}\) is the actual old seed.
All operator coefficients are rational.

Set
\[
\boxed{K:=[J,M]=JM-MJ.}
\]
By associativity and \(J^2=-I\),
\[
\boxed{JK+KJ=J^2M-MJ^2=0.}
\]
Thus the NEW interworld source is strictly **CM-odd**: it rotates
the old even/odd sectors rather than being a re-coordination that
commutes with original J. The actual original 12×12 K has rank 6.
It has a nonzero fixed seed source readout 2, verified independently
and already connected to the original Lean theorem
\`wave_source_CM_curvature_nonzero\`.

Note: the construction includes M THROUGH its commutator. "No local
M" does NOT mean M is absent from the global source law.

## 2. Exact NEW 12-cell pure curvature determinant

For any rational t define the actual original Wave-I curvature fold
\[
F_t:=U+J+tK.
\]
For the original seed v, the exact symbolic 12×12 Krylov determinant is
\[
\boxed{
D_K(t):=\det[v,F_tv,\ldots,F_t^{11}v]
=t^4(2t-1)\,P_{10}(t)\,Q_{16}(t),
}
\]
where
\[
\begin{aligned}
P_{10}(t)={}&411701-2185728t^2+293888t^3
+3073344t^4-960384t^5\\
&-1658656t^6+835776t^7+244932t^8
-222264t^9+36900t^{10},
\\[2mm]
Q_{16}(t)={}&255140-1606056t^2+3096493t^4
-2099096t^6\\
&+1818992t^8-3016960t^{10}
+2444032t^{12}-1234944t^{14}
+331776t^{16}.
\end{aligned}
\]
These polynomials are completely extracted from exact original
\(U,J,M,v\), with NO substituted generic matrix. Wolfram independently
checked \`Expand[Det[Krylov]-t^4(2t-1)P10 Q16]===0\`.

For an integer polynomial a_d t^d + ... + a_0, Cauchy's root bound
gives
\[
|\zeta|\le 1+\max_{k<d}|a_k/a_d|.
\]
The *exact* bounds here are
\[
1+\max_{k<10}|[t^k]P_{10}|/36900
=\frac{259187}{3075}<100,
\]
\[
1+\max_{k<16}|[t^k]Q_{16}|/331776
=\frac{3428269}{331776}<100.
\]
Consequently, for **EVERY rational t with |t|>100**,
\(t\ne0,\frac12\) and neither remaining factor can vanish:
\[
\boxed{\forall t\in\mathbb Q,\quad |t|>100
\implies \operatorname{rank}K_{12}(F_t,v)=12.}
\]
This is a proof for infinitely many rational strengths, not a finite
numerical extrapolation.

At t=0 the actual source-free original rank is 10; t=1/2 has rank
11; t=1 yields rank12. These exceptional facts help distinguish
nonzero curvature from sufficient rank: not every nonzero source
strength is cyclic.

## 3. Rank-independent ORIGINAL CM fixed-point rational eigenvalues

The ORIGINAL U-shuffle has fixed cells (0,0),(3,2). On their rational
signal subspace, in this physical order, the TRUE original operators
satisfy
\[
U_{\rm fix}=I_2,\quad
J_{\rm fix}=\begin{pmatrix}0&1\\-1&0\end{pmatrix},\quad
M_{\rm fix}=\begin{pmatrix}0&0\\0&2\end{pmatrix},
\quad K_{\rm fix}=
\begin{pmatrix}0&2\\2&0\end{pmatrix}.
\]
Thus
\[
\boxed{
F_{t,\rm fix}=
\begin{pmatrix}1&1+2t\\-1+2t&1\end{pmatrix},
\qquad
\chi_{\rm fix}(z)=z^2-2z+2-4t^2.
}
\]

For EVERY integer \(a\ge501\), choose
\[
\lambda(a)=\frac14\left(a+\frac1a\right)>100.
\]
The discriminant \(4(4\lambda(a)^2-1)\) is a rational square,
and the two eigenvalues are
\[
\boxed{\mu_\pm(a)=1\pm\tfrac12\left(a-\tfrac1a\right)\in\mathbb Q.}
\]
Both the original full 12-dimensional cyclicity (by §2) and at least
one rational spectral line (from the EXACT old fixed sector) are
therefore available in EACH selected block.

## 4. NEW all-prescribed-r GST CM-CURVATURE-ONLY companion theorem

**Theorem.** For every integer \(r\ge1\), one can construct
explicit rational ORIGINAL GST matrices with:
- h=2r independent original N-cohomology Wave-II worlds;
- each local U+J block completely source-free;
- source operator ONLY K=[J,M], and ALL diagonal interworld
  source coefficients ZERO;
- ONE original root source seed w;
- full native root orbit dimension 24r;
- a rational, F-equivariant, rank-r CYCLIC QUOTIENT;
- a nonzero rational Hankel moment determinant on the quotient.

**Construction.** For i=1,...,r set \(a_i=500+i\).
Take ordered distinct true rational curvature strengths
\[
\lambda_{2i-1}=\lambda(a_i),\qquad
\lambda_{2i}=-\lambda(a_i).
\]
All have absolute value >100, so all original F_{\lambda_k}
are cyclic; sum of ALL h=2r strengths is ZERO.

Let \(P_h(t)=\prod_{k=1}^{h}(t-\lambda_k)\in\mathbb Q[t]\).
Let \(C_h\) be its canonical rational Frobenius companion matrix
with forward basis transport \(C_h e_j=e_{j+1}\) for \(j<h-1\)
and last column determined by \(-P_h\)'s coefficients.
Because \([t^{h-1}]P_h=-\sum\lambda_k=0\), the ENTIRE diagonal of
\(C_h\) is zero. Consequently **none of the N-cohomology holes
receives LOCAL K or LOCAL SURVIVE M** from the source matrix.

Let
\[
L_r=100(r+510),\qquad b_k=L_r(k-1).
\]
The rational Lagrange navigation polynomial f_h is chosen by
\(f_h(\lambda_k)=b_k\). Set \(B_h=f_h(C_h)\).
Define ONE ORIGINAL GST global F
\[
\boxed{
\mathcal F_h=
I_h\otimes(U+J)+C_h\otimes K+B_h\otimes I_{12}.
}
\]
This is exactly the existing N-wave transport construction with the
ORIGINAL source M replaced by its DERIVED TRUE ORIGINAL CM curvature K.
It does not add new local source strengths.

Its single ROOT native seed is
\[
w=e_0\otimes(e_{(0,0)}+e_{(0,1)}).
\]

**Proof full rank.**
(i) All \(\lambda_k\) are rational, pairwise distinct. Thus \(C_h\)
diagonalizes over Q. Its basis-vector root e0 is cyclic (true for a
Frobenius companion), so in the eigenbasis it has a nonzero coordinate
in EVERY one-dimensional eigenspace.

(ii) Under the same rational conjugacy,
\(\mathcal F_h\) is the direct sum of
\(F_{\lambda_k}+b_kI_{12}\) and w projects as a NONZERO rational
multiple of v in every block.

(iii) The original matrices have exact infinity norms
\(\|U\|_\infty=\|J\|_\infty=1\), \(\|K\|_\infty=2\),
hence every original 12-block spectrum is confined to
\[
|\zeta-b_k|\le2+2|\lambda_k|.
\]
The largest \(a_r=500+r\), so
\(2+2\max_k|\lambda_k|<r+510\).
Neighboring centers are separated by
\(L_r=100(r+510)\), which exceeds TWICE that bound.
Therefore the characteristic/minimal polynomials of distinct
original blocks are COPRIME over Q.

(iv) Each original block is cyclic for v by §2; shifting by a scalar
does not change its generated module. The polynomial Chinese remainder
theorem combines these h cyclic modules into ONE cyclic module under
\(\mathcal F_h\). Thus
\[
\boxed{\operatorname{rank}_\mathbb Q
[w,\mathcal F_hw,\ldots,\mathcal F_h^{24r-1}w]=24r.}
\]

**Proof quotient rank r.**
For the r positive-source blocks, select exactly ONE rational
original fixed-pair eigenvalue
\[
\nu_i=b_{2i-1}+\mu_+(a_i)
=b_{2i-1}+1+\tfrac12(a_i-a_i^{-1}).
\]
The \(\nu_i\in\mathbb Q\) are pairwise distinct (their block
addresses are disjoint). Each \(t-\nu_i\) divides the characteristic
polynomial of \(\mathcal F_h\). Since w generates the entire
24r-dimensional cyclic module, identifying the root module with
\(\mathbb Q[t]/(\chi_{\mathcal F_h})\) and evaluating at these r
distinct rational factors gives a SURJECTIVE \(\mathbb Q[t]\)-module
homomorphism
\[
\boxed{q_r:\mathbb Q^{24r}\twoheadrightarrow\mathbb Q^r,\qquad
q_r(w)=(1,\ldots,1),\qquad
q_r\mathcal F_h=\mathrm{diag}(\nu_1,\ldots,\nu_r)q_r.}
\]
The Vandermonde determinant on the quotient is
\(\prod_{i<j}(\nu_j-\nu_i)\ne0\). The quotient seed is therefore
r-cyclic.

**Moment detector.** Since
\((q_rw,T_rq_rw,\ldots,T_r^{r-1}q_rw)\) is a rational basis,
there is a rational functional ℓ determined by
\(\ell(T_r^kw)=\delta_{k,r-1}\) for 0≤k<r.
The Hankel matrix \(H_{ij}=\ell(T_r^{i+j}q_rw)\) is zero strictly
below its anti-diagonal and has all anti-diagonal entries 1.
Consequently
\[
\boxed{\det H=(-1)^{r(r-1)/2}\ne0.}
\]
This proves the **pure original-CM-curvature-only, zero-local-source,
rank-adaptive native steps 02–03 for ALL prescribed finite r**.

## 5. Independent exact Wolfram certificates and provenance

Committed \`research/computations/GST_image3_pureCMcurvature_only_rankadaptive_20261111.wl\`.
It was **fetched back from the new GitHub branch and executed verbatim**
using Wolfram Language. \`allPassed=True\`.

Verified assertions include:
- exact full symbolic degree-31 original \(\det K_{12}\) identity;
- rational Cauchy bounds for both factors;
- derived K anti-commutes with J and has actual rank 6;
- genuine companion h=2 and h=4 has zero diagonal and exact
  specified eigenvalues;
- original single root e0 is cyclic for companion;
- navigation matrix B commutes with companion and has the prescribed
  exact rational interpolation addresses;
- actual original fixed-block CM eigenvalues are rational;
- full native global Krylov 24×24 determinant mod 1009 = 882 (r=1);
- full native global Krylov 48×48 determinant mod 1009 = 969 (r=2).

These finite cases are **independent tests of the exact algebraic
construction**. The all-r theorem is the above symbolic/Cauchy/CRT
proof, not an empirical pattern claim.

## 6. GENUINE original-X Chow-Betti landing, without preselected Hodge inverse

Two additional additive Lean files on this branch:
- \`GSTImageThreePureCMCurvatureNative.lean\` formalizes the EXACT
  original wave CM curvature, its anti-commutation with J, the
  curvature-only global N-wave F and zero-local-curvature-source law.
- \`GSTImageThreePureCMOriginalXLanding.lean\` constructs a TRUE
  original-X \`CycleClassOperatorPair\` from two already-certified
  original-X J,M pairs by the actual Chow/Betti commutator
  \([J,M]\), then instantiates the existing all-N actual original-X
  Chow/Betti square for arbitrary source and navigation matrices.

The original-X theorem is:
\[
\boxed{
\mathrm{cl}_X^{N}\circ \mathcal N_{\rm CM}
=\mathcal T_{\rm CM}\circ \mathrm{cl}_X^{N}.
}
\]
It assumes genuine original-X J,M and U operator pairs with their
certified canonical square. It does NOT claim that the original
12-cell abstract J,M operators always descend to projective Chow
correspondences on every X, nor that every rational Hodge class
has a cycle preimage. Kernel status must be taken from the
specific new GitHub CI run, not inferred from Wolfram.

## 7. NEW sharpened proof requirements for the Hodge antecedent

**Actual geometric step 01 needs an existence theorem**, NOT merely
natural closure under sums/commutators:
for every (X,p) construct ACTUAL algebraic correspondences realizing
a native generator and a CM-odd curvature source compatible with
the CANONICAL rational Betti cycle class. Their compositions are
genuine Chow source operations. The existing Lean source-pair law
is conditional on those actual geometric operators.

**Actual geometric step 02 needs a rank-retaining landing**
\(\Phi_{X,p}:W^{GST}_{24r}\to W_p(X)\)
that is surjective and intertwines the GENERATED one-fold
\(\mathcal F_h\) with the actual geometric correspondence action,
and maps the GST root seed to the canonical class of a GENUINE
original-X algebraic cycle. Because r=dim W_p(X), this would produce
a cyclic original-X geometric Hodge orbit, using the JUST PROVED
arbitrary-r quotient to avoid rank-divisibility obstruction.
A freely CHOSEN vector-space isomorphism is NOT sufficient: the map
and its cyclic seed must be constructed from original-X geometry.

**Actual step 03 then follows** from the finite-dimensional rational
dual detector when the original-X orbit is proved full-rank,
without another separate determinant postulate.

**Universal step 04** is the existence of the above construction
for all smooth projective X and p with canonical cycle class.
No inherited "Hodge true" hypothesis may enter its construction.

### Critical universal CM parity firewall

An over-strong geometric requirement would be FALSE: asking a rational
complex structure \(J_X^2=-I\) on the WHOLE target Hodge space
\(W_p(X)\) for EVERY (X,p). If r=dim_Q W_p(X) is odd, then
\[
\det(J_X)^2=\det(-I_r)=(-1)^r=-1,
\]
impossible over Q. In particular \(\dim W_1(\mathbb P^2)=1\).
Therefore **full CM J-equivariance on every target Hodge space
cannot be the universal landing hypothesis**.

The native rank-r quotient \(q_r\) above is only \(\mathcal F_h\)
equivariant: it need NOT preserve J separately. This is the correct
resolution within the original GST architecture, not abandonment of
the original J/CM/curvature construction.

### Algebraicity range firewall

Every genuine X-native cycle operator maps already-algebraic classes
to already-algebraic classes. Cross-world mixing is powerful for
constructing NEW combinations outside a PREVIOUSLY KNOWN subspace of
algebraic cycles, but cannot create a non-algebraic Hodge class as a
Chow output. To prove the Hodge conjecture, one must show that the
actual algebraic outputs fill ALL Hodge space. The universal rank
proof is not inferred from wave information rank alone.

## 8. Step-by-step score, with no conflation

1. **Geometric actual X fold:** formal naturality/closure proved from
   existing actual correspondence pairs; UNIVERSAL CONSTRUCTION
   of those pairs not proved.
2. **All Hodge directions:** TRUE ORIGINAL GST wave/source cyclicity
   proved for every prescribed finite rank via above curvature-only
   theorem; landing on all geometric Hodge directions of actual
   X remains unproved.
3. **Nonzero determinant:** exact original native determinant and all-r
   quotient Hankel proved; geometric determinant remains conditional
   on step 02 original-X landing.
4. **All X,p canonical:** conditional implication exists and is
   mathematically meaningful, but universal hypothesis itself
   is not yet established.

**Universal step count completed: 0/4.**
This is NOT a score for all native sublemmas; multiple substantial
native sublemmas and the original-X naturality conditional are proved.
The Hodge implication is proved if the missing universal antecedent
is established. This research route has advanced the native necessary
construction and made the remaining geometric target exact.
