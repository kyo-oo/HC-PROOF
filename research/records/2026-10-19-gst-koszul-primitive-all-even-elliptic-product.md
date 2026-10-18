# Mathbox: GST independent algebraic perfect-complex primitive births in ALL even dimensions

**Date:** 2026-10-19 · **Main target unchanged:** for every original smooth projective complex X, every p and every rational (p,p) class alpha, construct a rational Chow cycle with genuine canonical Betti class alpha. **Active route:** actual algebraic K₀ sources, finite-flat Chow projection, polarized GST native frame. **First checkpoint:** c7e5ca0ef1b47cfd205b304707b1bfcf3b9c5484. **Lean changes:** GSTUniversalResolvedSupportHodge.lean, including a concrete rank-two elliptic-fourfold source family and a dimension-uniform Koszul lemma.

## 1. Geometric source, original X, exact types

Let the ORIGINAL complex projective abelian variety be \(X=E_1\times\cdots\times E_{2m}\), where \(m\ge1\) and each \(E_j\) is a smooth projective elliptic curve. Choose a degree-one line bundle \(L_j\) on \(E_j\); denote its first Chern class on X by \(x_j=c_1(\operatorname{pr}_j^*L_j)\in CH^1(X)_\mathbb Q\).

The true algebraic Chow relations are \(x_j^2=0\); \(H=\sum_j x_j\) is a genuine ample polarization, and \(\int_X x_1\cdots x_{2m}=1\). The integral perfect-complex K-class
\[
\mathcal E_m=\bigotimes_{k=1}^m ([L_{2k-1}]-[L_{2k}])
\in K_0(X)
\]
is constructed independently of an arbitrary Hodge target alpha. Every factor has Chern-character degree-zero part zero, degree-one part \(x_{2k-1}-x_{2k}\). Therefore the FIRST nonzero rational GRR/Chow degree of \(\mathcal E_m\) is exactly
\[
\boxed{Z_m=\prod_{k=1}^m(x_{2k-1}-x_{2k})\in CH^m(X)_\mathbb Q.}
\]
No Chern/homology target witness is among the input data.

## 2. Dimension-uniform exact polarized primitive source

For ANY commutative coefficient ring and any paired square-zero classes \(u_k,v_k\) one has
\[
(u_k+v_k)(u_k-v_k)=u_k^2-v_k^2=0,\qquad
(u_k-v_k)^2=-2u_kv_k.
\]
Since \(H=\sum_k(u_k+v_k)\) and \(Z=\prod_k(u_k-v_k)\),
\[
\boxed{HZ=0,\quad Z^2=(-2)^m\prod_k u_kv_k.}
\]
On the actual original X, the product of all factor divisors integrates to one. Thus
\[
\boxed{(-1)^m\int_X Z_m^2=2^m>0.}
\]
This supplies a genuinely nonzero middle Lefschetz-primitive (m,m) algebraic class on EVERY such original X, despite \(T_X\) being trivial and tangent Chern sources therefore vanishing.

The exact general-rank Lean proof uses the list-valued \`hyperplaneOfPairs\` and \`koszulPrimitiveSource\` inside namespace \`GSTNativeAbelianKoszulAllEvenDimensions\`. It proves both equalities inductively for arbitrary list length, with square-zero divisors as the only algebraic relations. Its GH Actions status must be determined from the revision-matched run, rather than presumed.

## 3. Two independently born primitive cycles on one abelian fourfold

For \(m=2\), the already present P source is joined by a second algebraic virtual perfect complex:
\[
\begin{split}
P&=(x_1-x_2)(x_3-x_4),\\
Q&=(x_1-x_3)(x_2-x_4).
\end{split}
\]
Both are Chow codimension two and Lefschetz-primitive for \(H=\sum_{i=1}^4 x_i\). In the **genuine squarefree divisor product basis** \((x_{12},x_{13},x_{14},x_{23},x_{24},x_{34})\),
\[
P=(0,1,-1,-1,1,0),\quad
Q=(1,0,-1,-1,0,1).
\]
The cup/cap intersection pairing only pairs complementary 2-sets, so
\[
\boxed{G(P,Q)=\begin{pmatrix}4&2\\2&4\end{pmatrix},\qquad
\det G=12,\quad G^{-1}=\tfrac1{12}\begin{pmatrix}4&-2\\-2&4\end{pmatrix}.}
\]
For any actual prescribed primitive Hodge alpha, put \(a=Q(\alpha,P)\), \(b=Q(\alpha,Q)\). The target-directed original-X rational algebraic combination is
\[
\boxed{Z_\alpha=\frac{2a-b}{6}P+\frac{2b-a}{6}Q.}
\]
The **exact** two period equalities are
\(Q(Z_\alpha,P)=a,\ Q(Z_\alpha,Q)=b\), and
\[
\boxed{Q(\alpha,Z_\alpha)=\frac{a^2-ab+b^2}{3}>0}
\]
when \((a,b)\ne(0,0)\). The positivity is elementary via \(4(a^2-ab+b^2)=(2a-b)^2+3b^2>0\). This is a native target-sensitive algebraic perfect-complex source, with no alpha Chow preimage among the assumptions.

Wolfram exact-rational test on 2026-10-19: cup(P)=cup(Q)=(0,0,0,0), G=[[4,2],[2,4]], det(G)=12, inverse=[[1/3,-1/6],[-1/6,1/3]], exact period recovery, exact target coupling \(a^2/3-ab/3+b^2/3\), positivity for real a,b not both zero.

The Lean definitions/theorems \`GSTNativeAbelianKoszulRankTwo.nativeKoszulP\`, \`nativeKoszulQ\`, \`nativeKoszul_two_source_gram_determinant\`, \`nativeKoszulTargetCycle_P_period\`, \`nativeKoszulTargetCycle_Q_period\`, \`nativeKoszulTargetCycle_primitive\`, and \`nativeKoszulTargetCycle_target_pairing\` were committed into the EXISTING GSTUniversalResolvedSupportHodge.lean. A small tactic-level conjunction correction was applied after first CI reported a \`True ∧ True ∧ True\` residual; do not label this suite kernel-green until the new CI run succeeds.

## 4. Larger rank: explicit Catalan-family experiment

For every noncrossing perfect matching \(M\) of \(\{1,\dots,2m\}\), the actual integral \(K_0\) perfect complex made from factors \([L_i]-[L_j]\) defines another primitive Chow source
\[
Z_M=\prod_{(i,j)\in M}(x_i-x_j).
\]
The number of noncrossing matchings is the Catalan number \(C_m=\frac1{m+1}\binom{2m}{m}\). A *potential* stronger GST law is that the \(Z_M\) provide a native \(\mathbb Q\)-basis of the primitive squarefree divisor-product sector \(\ker(H: \mathcal A_m\to\mathcal A_{m+1})\), where \(\mathcal A=\mathbb Q[x_1,\dots,x_{2m}]/(x_1^2,\dots,x_{2m}^2)\). The dimension predicted by the projective-product Lefschetz module is
\[
\dim\ker H=\binom{2m}{m}-\binom{2m}{m-1}=C_m.
\]

**Finite exact computational audit** (2026-10-19): independently enumerate ALL noncrossing matchings recursively, expand each cycle into the squarefree degree-m monomial basis with coefficients in \(\{-1,0,1\}\), compute matrix ranks modulo the fixed exact prime 1,000,003 (no randomization, floats or sampling), and compare to the entire theoretical Catalan dimension. Results:

| m | noncrossing complexes | matrix shape | exact rank mod 1,000,003 | Catalan |
|---|---:|---:|---:|---:|
| 1 | 1 | 2×1 | 1 | 1 |
| 2 | 2 | 6×2 | 2 | 2 |
| 3 | 5 | 20×5 | 5 | 5 |
| 4 | 14 | 70×14 | 14 | 14 |
| 5 | 42 | 252×42 | 42 | 42 |

The signed rational intersection Gram \(G_{MN}=(-1)^m\int_X Z_M Z_N\) was also constructed EXACTLY as the complement-incidence product matrix. Its exact Gram determinant is 2 at m=1, 12 at m=2, 5184 at m=3 and 8,358,844,170,240 at m=4; exact finite-field Gram rank is 42 at m=5. The m=3 Gram matrix in the recursive matching order is
\[
\begin{pmatrix}
8&-4&-4&2&-4\\
-4&8&2&-4&2\\
-4&2&8&-4&2\\
2&-4&-4&8&-4\\
-4&2&2&-4&8
\end{pmatrix}
\]
with det=5184. These are exact FINITE tests, not proof that all m has full Catalan rank.

**Proposed uniform proof:** identify the squarefree divisor ring as the 2m-fold tensor of the two-dimensional standard module for the Lefschetz \(\mathfrak{sl}_2\)-action, and the cycles \(x_i-x_j\) as antisymmetric two-slot singlets. Noncrossing pairings form the expected Temperley–Lieb/SL₂ invariant basis; translating that theorem into actual GST K₀-source coefficients, rather than relying on a finite sample, would yield an explicit general-rank native algebraic source frame for the ENTIRE divisor-word primitive sector. The key source correspondence is given here; a general kernel-verified basis theorem is not claimed.

**Geometric scope:** on a nonsplit Weil-type abelian fourfold with NS_Q=Qθ, these elliptic factor line bundles are not present. Thus even a complete squarefree divisor-product span cannot be asserted to provide every exceptional Weil Hodge class. The all-X program must still obtain an independently algebraic perfect complex beyond existing divisor products, e.g. a genuinely exotic sheaf/Hilbert/CM construction on the original nonsplit X. This is the specific geometric source-growth obligation; the alpha-selected K₀ and Gram compiler then produces explicit original-X cycles.

## 5. Current work products

- Lean: GSTUniversalResolvedSupportHodge.lean, existing module edited to add both source families and all-m square-zero algebraic laws; GH Actions GST Native K0 Original X Extraction and pinned full Hodge integration run on the active research branch.
- Calculation: Wolfram exact fourfold pairing and inverse Gram; deterministic finite-field rank check for m=1..5; rational exact determinants for m<=4.
- Hodge/Chow type gate: The genuine perfect complexes and their actual Chow Chern classes are mathematical original-X constructions, while the **Lean** all-m code operates at the exact rational squarefree intersection-algebra interface. The canonical Betti realization on arbitrary schemes is still a separate geometric input, and the conjecture for all X,p,alpha is not inferred from this source subfamily.
