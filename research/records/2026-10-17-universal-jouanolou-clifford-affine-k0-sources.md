# Mathbox Gate 3 — explicit algebraic projectors on universal affine replacements

- **Date / checkpoint:** 2026-10-17. Research branch \`research/gpt6-native-point-primitive-span-20261017\`; base checkpoint \`e82048f9a1d3a06500595a232717dd78973df179\`.
- **Fixed final target:** For all smooth projective complex varieties \(X\), codimensions \(p\), and rational \((p,p)\) Hodge classes \(\alpha\), construct a native rational algebraic codimension-\(p\) cycle on **original \(X\)** with its canonical Betti class \(\alpha\).
- **Work-package target:** Construct genuine ALGEBRAIC vector-bundle sources from explicit equations on smooth affine models without presupposing any K-theory lift of \(\alpha\), and test their relation to a canonical affine replacement of arbitrary \(X\).

## 1. Universal, genuinely affine carrier for every original X

Fix a closed embedding \(X\hookrightarrow\mathbb P^N_{\mathbb C}\). Let \((\mathbb P^N)^\vee\) be the dual projective space and define
\[
 J(X)=\{(x,H)\in X\times(\mathbb P^N)^\vee:x\notin H\}.
\]
The excluded incidence locus is the zero divisor of \(\mathcal O_X(1)\boxtimes\mathcal O(1)\), an **ample** line bundle on the projective product. Thus its complement \(J(X)\) is **affine**. Over a chart \(x_i\neq0\), normalized equations \(\sum_j\lambda_jx_j=1\) solve uniquely for \(\lambda_i\) and leave \(N\) free affine parameters. Consequently \(\pi:J(X)\to X\) is a Zariski-locally trivial \(\mathbb A^N\)-bundle (Jouanolou affine replacement) for **every** smooth projective \(X\). It is smooth.

By affine-bundle homotopy invariance,
\[
  \pi^*:H^{2p}(X,\mathbb Q)\simeq H^{2p}(J(X),\mathbb Q),\qquad
  \pi^*:CH^p(X)_{\mathbb Q}\simeq CH^p(J(X))_{\mathbb Q}.
\]
These maps respect canonical Betti classes; rational algebraic \(K_0\) is likewise invariant on smooth regular schemes. Because the Betti map is a geometric isomorphism, the affine target \(\pi^*\alpha\) has pure Hodge type \((p,p)\) for every original \(X,p,\alpha\). **An algebraic affine cycle on \(J(X)\) can be descended unambiguously to an algebraic cycle on original \(X\)** using the Chow inverse. This is a direct all-\(X\) affine model without the auxiliary divisor-boundary induction.

**Precise remaining generator problem:** produce \(Z_{J(X)}\in CH^p(J(X))_{\mathbb Q}\) with \(\mathrm{cl}_{J(X)}(Z_{J(X)})=\pi^*\alpha\) *without assuming the desired Chow witness*. The affine equivalence above is not an existence proof. It is a rigorous geometry-first environment in which to manufacture the required algebraic K-classes.

## 2. Universal rank-one projector manufactured from the incidence equations

The regular functions on \(J(X)\)
\[
 e_{ij}=\frac{x_i\lambda_j}{\sum_k x_k\lambda_k}
\]
are globally well-defined: each is homogeneous degree zero separately in the two projective factors and the denominator never vanishes on \(J(X)\). The matrix \(E=(e_{ij})\) satisfies
\[
   \mathrm{tr}\,E=1,\qquad e_{ik}e_{kj}=e_{ij}e_{kk},
   \qquad E^2=E.
\]
The \(\operatorname{im}(E)\) over the AFFINE coordinate ring is therefore a **genuine algebraic projective module**, precisely the pullback of the tautological algebraic line \(\mathcal O_X(-1)\). It exists on **every** original \(X\), without Oka or a chosen K-theory preimage.

The current rank-one source produces the ambient hyperplane Chern classes. It does not supply arbitrary primitive Hodge directions, so it must be extended with explicit **higher-rank primitive projectors**, not mistaken for complete Hodge spanning.

## 3. Clifford recursion manufactures algebraic K-classes at every p

For each integer \(p\ge1\), over the polynomial ring \(\mathbb Z[x_1,\ldots,x_p,y_1,\ldots,y_p,z]\) put \(q_p=\sum_i x_i y_i\). Define \(A_1=(x_1)\), \(B_1=(y_1)\) and recursively with \(I\) of size \(2^{p-1}\):
\[
 A_{p+1}=\begin{pmatrix}A_p&x_{p+1}I\\y_{p+1}I&-B_p\end{pmatrix},\qquad
 B_{p+1}=\begin{pmatrix}B_p&x_{p+1}I\\y_{p+1}I&-A_p\end{pmatrix}.
\]
Direct block multiplication and commutativity show \(A_pB_p=B_pA_p=q_p I\) **for every p by induction**. Set
\[
 E_p=\begin{pmatrix}zI&A_p\\B_p&(1-z)I\end{pmatrix},
 \quad \text{size }2^p\times2^p .
\]
One direct block multiplication gives the **polynomial identity**
\[
 \boxed{E_p^2-E_p=(q_p-z(1-z))I_{2^p},\quad
  \operatorname{tr}E_p=2^{p-1}.}
\]
On the smooth affine split quadric
\[
 Q_{2p}=\operatorname{Spec}\,
 \mathbb C[x_1,\ldots,x_p,y_1,\ldots,y_p,z]/(q_p-z(1-z)),
\]
\(E_p^2=E_p\). Hence \(P_p=\operatorname{im}E_p\) is a **genuine algebraic projective module of rank \(2^{p-1}\)** on an affine variety of complex dimension \(2p\). Under any genuine algebraic map \(U\to Q_{2p}\), pulling back \(E_p\) constructs an algebraic projective module on that particular affine \(U\). This is an explicit source factory available in EVERY codimension \(p\); its pullback is defined by polynomial equations on \(U\), not by a topological/Hodge preimage assumption.

A second explicitly manufactured **native codimension-p algebraic cycle** on \(Q_{2p}\) is
\[
 L_p=\{z=y_1=\cdots=y_p=0\}\cong\mathbb A^p,
\]
with codimension \(p\). Its Betti class is nonzero: the compact real sphere inside \(Q_{2p}(\mathbb C)\) defined by \(y_i=\overline{x_i}\), \(z\in\mathbb R\), \(\sum|x_i|^2=z(1-z)\) is an \(S^{2p}\). It intersects \(L_p\) transversely at the single south pole \(x=y=z=0\), with local intersection number \(\pm1\); thus \(\mathrm{cl}(L_p)\) evaluates nontrivially against that sphere. Therefore this is a genuine nonzero rational algebraic class in middle degree **for every p**, without assuming its cycle preimage.

For \(p=1\), \(E_1=\begin{pmatrix}z&x\\y&1-z\end{pmatrix}\). Its image line has a polynomial global section whose zero divisor is \(L_1=\{z=y=0\}\). For the universal affine replacement of \(X=\mathbb P^1\), the identification \(J(\mathbb P^1)\simeq Q_2\) sends the universal rank-one incidence projector to this explicit matrix (up to change of coordinates). Hence the Clifford source starts in the ACTUAL universal affine replacement construction rather than an unrelated toy model.

## 4. Exact independent verification and Lean connection

- Wolfram evaluated the polynomial matrix equations for \(p=1,2,3,4\), obtaining matrices of sizes \(2,4,8,16\), \(A_pB_p=B_pA_p=q_pI\), \(E_p^2-E_p=(q_p-z(1-z))I\) and traces \(1,2,4,8\). This is **exact symbolic arithmetic**, not floating point, and the all-\(p\) proof is the separate block induction above.
- The independent pure-stdlib polynomial audit \`research/computations/affine_clifford_k0_source.py\` checks every polynomial coefficient without external CAS dependencies. In GitHub Actions [#39049136728](https://github.com/kyo-oo/HC-PROOF/actions/runs/39049136728), the polynomial audit PASSED for \(p=1,\ldots,4\); that first combined run FAILED later in a Lean tactic, not in the polynomial construction. The ring-generic Lean rank-one theorem \`quadricBottProjector_idempotent\` is being repaired/verified in \`GSTUniversalResolvedSupportHodge.lean\` with the existing 247-module workflow. Do not equate a failed Lean tactic with a false polynomial identity.
- Full geometric K-theory/Chern-class and affine-bundle/analytic realization for the current GST Stage2G interfaces is still a **separate formalization task**, although the classical algebraic constructions above are explicit and independent of the conjecture.

## 5. Direct next operation on all X,p,alpha

For each original embedded \(X\) and prescribed \(\alpha\), work **on the actual affine ring** \(A=\Gamma(J(X),\mathcal O)\). The concrete candidate space consists of polynomial idempotent matrices \(E\in M_N(A)\), certified by \(E^2=E\), whose algebraic Chern character \(ch_p(\operatorname{im}E)\) equals \(\pi^*\alpha\) under the canonical rational Betti comparison. The incidence projector is a certified ambient generator; the Clifford family supplies explicit additional source matrices when \(A\) contains polynomial quadric data.

**First unresolved mathematical implication:** construct enough genuinely **new algebraic idempotents over \(A\)** (or independently geometric Chow cycles) to hit each prescribed primitive Hodge \(\pi^*\alpha\), not merely ambient Chern classes or a subspace generated by existing cycles. This is the single Gate-3 source-production target, and its truth would imply the original rational Hodge conjecture. No conjectural full-rank hypothesis was added to any proof.

**Route status:** constructive all-\(X\) affine carrier and universal explicit K₀ source factories obtained, with exact algebraic identities; spanning of arbitrary primitive rational Hodge targets open. Natural next attack: build Jacobian-derived higher-rank projectors over arbitrary \(A\), then test whether their primitive Chern directions supply classes outside the universal rank-one span.
