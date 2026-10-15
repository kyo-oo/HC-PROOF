# GST blow-up Hodge transfer beyond affine pavings

**Date:** 2026-10-15
**Origin:** exact head `66e4f0bfed4f2c74cb3cd3825eae0c2911e75c88` of `mathbox/bd23-single-operator-charge-wedge`.
**Development branch:** `research/gpt6-gst-blowup-transfer-20261015`.
**Formal module:** `GSTBlowupHodgeTransfer.lean`.
**CI:** `.github/workflows/gst-blowup-hodge-transfer.yml`.

## Original target retained

Given an arbitrary smooth projective complex variety X, codimension p,
and a rational Hodge (p,p) class alpha, construct an actual rational
algebraic cycle Z with cl(Z)=alpha. **This remains unproved universally.**

Here we establish a new _geometric inheritance mechanism_ extending the
existing affine-paving, quadric, divisor-word, projective-product and CM/NM
routes. No arbitrary Hodge-class preimage for the blow-up is assumed.

## Exact geometric transfer theorem

Let X be smooth projective and Z \subset X a smooth closed subvariety of
complex codimension c >= 2. Put \tilde X = Bl_Z X, with blow-up map
\pi : \tilde X -> X, exceptional divisor E=P(N_{Z/X}), projection
q:E->Z, and closed immersion j:E->\tilde X. Let
\xi=c_1(O_E(1)) denote the algebraic tautological hyperplane class.

The classical cohomological blow-up formula gives, for each p,

\[
 H^{2p}(\tilde X,\mathbb Q) \cong
 H^{2p}(X,\mathbb Q)\oplus
 \bigoplus_{r=1}^{c-1} H^{2(p-r)}(Z,\mathbb Q)(-r).
\]

The isomorphism sends a tuple \((\beta,\gamma_1,\ldots,\gamma_{c-1})\)
to

\[
 \pi^*\beta+\sum_{r=1}^{c-1}
 j_*\big(\xi^{r-1}\smile q^*\gamma_r\big).
\]

Every map is an independently geometrically defined pullback, cup with
an actual divisor, or proper Gysin pushforward. The decomposition is a
well-established geometric cohomology theorem, **not** the desired
cycle-class surjectivity repackaged.

If the rational Hodge conjecture holds for X in codimension p and for Z
in each codimension p-r, choose genuine cycles A, B_r with
cl(A)=beta and cl(B_r)=gamma_r. Then

\[
 \boxed{\mathcal Z_\alpha=\pi^* A+
 \sum_{r=1}^{c-1}j_*\big(\xi^{r-1}\cdot q^* B_r\big)}
\]

is an actual rational algebraic cycle on the blow-up, and
\(\mathrm{cl}(\mathcal Z_\alpha)=\alpha\). Hodge bidegrees and rational
coefficients are preserved by the algebraic operations. It follows that
the Hodge conjecture is stable under smooth blow-ups once the original
variety and its smooth center satisfy it.

This is a proved mathematical construction from known blow-up and
cycle-class functoriality facts. The Lean file formalizes its explicit
three-source linear lifting algebra. It does **not** formalize all of
the scheme blow-up or its Betti-to-Hodge comparison.

## A NONCELLULAR arbitrary-genus fourfold family

Choose any smooth projective complex curve C of genus g >= 1,
embedded into P^4. Such embeddings exist: any line bundle of sufficiently
large degree on C is very ample; for genus two, a degree-six complete
linear system embeds into P^4.

Take Y=Bl_C(P^4). Here c=3 and the weight p=2 formula is

\[
 H^4(Y,\mathbb Q)\cong H^4(P^4,\mathbb Q)\oplus
 H^2(C,\mathbb Q)(-1)\oplus H^0(C,\mathbb Q)(-2).
\]

All three source groups are one-dimensional rational Hodge spaces, with
the following actual cycle sources:

1. The square of the projective hyperplane class on P^4;
2. A rational point of C, pulled back to E and Gysin-pushed to Y;
3. The tautological divisor class \xi on E, Gysin-pushed to Y.

Thus \(h^{2,2}(Y)=3\) and **every rational (2,2) class on Y has an
explicit rational algebraic cycle**, with NO target preimage assumed.

The odd Betti cohomology does not vanish:
\[
 H^3(Y,\mathbb Q)\cong H^1(C,\mathbb Q)(-1),\quad b_3(Y)=2g.
\]
So Y does **not** admit an algebraic affine-cell paving. This
proves the new construction reaches varieties excluded by the latest
affine-paving program, instead of re-proving the same cellular case.

By Hard Lefschetz, \(L:H^4(Y)\to H^6(Y)\) is surjective (since
\(L^2:H^2(Y)\to H^6(Y)\) is an isomorphism). The blow-up formula gives
\(b_4(Y)=3\), \(b_6(Y)=2\). Hence the rational middle primitive Hodge
kernel has dimension exactly one; its classes have actual rational
algebraic representatives by the construction above.

## Exact Wolfram computation

Let u,v denote Hodge bidegree bookkeepers; the Hodge polynomial is

\[
 P_Y(u,v)=\sum_{k=0}^{4}(uv)^k+
 (uv+(uv)^2)(1+gu+gv+uv).
\]

Wolfram Language expansion gave

\[
1+2uv+gu^2v+guv^2+3u^2v^2+
gu^3v^2+gu^2v^3+2u^3v^3+u^4v^4.
\]

Therefore the Hodge-diamond entries and Betti counts above are exact.
For g=2, h^(2,1)=h^(1,2)=2, b3=4 and h^(2,2)=3.
This calculation checks the blow-up Hodge-number formula; it does not
replace the geometric blow-up theorem.

## Lean scope and proof architecture

`CodimThreeBlowupData` contains:
- three **source** cycle-class maps and the target forward cycle-class map;
- actual native base-pullback and two exceptional Gysin operations;
- the three independently defined geometric Hodge maps;
- the three projections from the cohomological blow-up decomposition;
- cycle-class naturality for the three native geometric operations.

`constructBlowupCycle` uses the three source witnesses and adds their
native geometric images. `constructBlowupCycle_correct` derives exact
target cycle-class equality. A separate theorem constructs representatives
of primitive rational target Hodge classes. It assumes neither a target
section nor target Hodge surjectivity.

**Important limit:** the existence of a genuine `CodimThreeBlowupData`
from a specific Mathlib scheme blow-up is not proved in this file. The
actual source geometry remains an independently established mathematical
input; connecting it through Lean's Betti cohomology API is a subsequent
formalization obligation, not a license to claim a fully formalized result.

## Principal remaining obstruction and next proof route

The universal problem still begins with an arbitrary noncellular smooth
projective X that need not come from blow-ups of varieties and centers
with known Hodge algebraicity. Blow-ups only propagate a known Hodge result
along genuine geometry; they cannot supply an arbitrary unknown primitive
representative by themselves.

Proposed decisive next route:
1. Build the scheme-theoretic smooth blow-up and exceptional Gysin maps in
   the current `GSTGeometricRealizationStage2G` / Stage-2F semantic layer.
2. Instantiate `CodimThreeBlowupData` for the explicit
   Bl_C(P^4) benchmark; verify the three cohomology projections and the
   native-to-Betti naturality square.
3. Generalize to all codimensions and finite center-summand families;
   then test primitive correspondences on a NON-blowup benchmark with a
   previously unrepresented middle Hodge class. This distinguishes
   genuinely new geometric generators from mere transport of existing ones.

**Evidence status:** The classical blow-up deduction and Hodge-polynomial
calculation are mathematical arguments. Lean source and CI are separate
and must be checked at their exact commit SHA. The arbitrary-variety
Hodge conjecture is not claimed solved.


## Strengthened arbitrary-codimension formal transfer

The three-slot module is now complemented by
`GSTBlowupHodgeAllCodimension.lean`. Its
`FiniteBlowupPresentation` takes an arbitrary **finite index type** of
exceptional shifts r. The native cycle and Hodge types are dependent
families `NE r` and `HE r`, so different degrees of the center
do NOT get conflated into a single rational vector space.

The actual constructed native cycle at target alpha is

\[
 \mathrm{nativeBase}(Z_0(\alpha))+
 \sum_{r\in I}\mathrm{nativeExceptional}_r(Z_r(\alpha)),
\]

with each Z chosen from an independently realized source Hodge class.
The Lean proof establishes the cycle-class identity from
`geometricDecomposition`, `nativeBaseNaturality`, and
`nativeExceptionalNaturality` only. The theorem
`finite_blowup_preserves_all_rational_hodge_classes` derives
surjectivity on the *target Hodge fiber*. It is not a hypothesis.
`finite_blowup_primitive_realization` adds the exact primitive
Lefschetz-kernel identity for target classes in the kernel.

For geometric codimension c>=2 use the finite index
r in {1,...,c-1}, `NE r = CH^(p-r)(Z)_Q` and
`HE r = Hodge^(p-r,p-r)(Z)_Q`, with the appropriate Tate twist and
Gysin map. This is the algebraic interface needed for a true all-codimension
blow-up-stability theorem.

**Still external to the Lean file:** construction of the actual
scheme-specific `FiniteBlowupPresentation` from the Mathlib
blow-up/Poincare duality/Hodge comparison stack. This obligation
is separate from the now-general algebraic transfer, and is the
next proof-assistant integration target.


## Phase 2: independent geometric rank and explicit polarized primitive

**New Lean modules**

* \`GSTBlowupThreeCycleIntersectionRank.lean\`: exact inverse to the
  geometric three-cycle intersection readouts; produces a native algebraic
  cycle directly from three rational measurements.
* \`GSTBlowupSchemeNativeBridge.lean\`: specializes the three-source transfer
  to ACTUAL \`codimensionCycles\` on smooth projective Mathlib schemes and to
  the \`ClassicalHodgeFiber\` computed from Stage-2G rational Betti cohomology.
  The native pullback and exceptional Gysin maps remain geometric interface
  obligations, NOT constructed scheme morphisms in this module.
* \`GSTBlowupNoncellularPrimitiveCurve.lean\`: a parametrized **nonzero**
  primitive algebraic cycle for an ample class \(A=mh-e\), supported on
  genuine base and exceptional cycle candidates.

### Precise geometry and intersection pairing

Let \(C\hookrightarrow\mathbf P^4\) be a smooth connected curve of genus
\(g\) and degree \(\delta\), \(Y=\operatorname{Bl}_C(\mathbf P^4)\),
\(\pi:Y\to\mathbf P^4\), \(j:E\to Y\), \(q:E\to C\),
\(h=\pi^*c_1(O_{\mathbf P^4}(1))\), \(e=[E]\), and
\(\xi=c_1(O_E(1))\). Use the convention \(j^*e=-\xi\) and
\(q_*(\xi^2)=1\).

The normal bundle \(N_{C/\mathbf P^4}\) has rank three and first
Chern degree
\[
n=\int_C c_1(N)=5\delta+2g-2.
\]

Choose \(P\in C\) a closed complex point, and the three genuine
codimension-two algebraic cycle classes
\[
u_0=h^2,\quad u_1=j_*q^*[P],\quad u_2=j_*\xi.
\]
The projective-bundle formula and projection formula give the *geometric*
cup-intersection matrix:
\[
G=(\int_Yu_i\smile u_j)_{i,j}
=\begin{pmatrix}
1&0&0\\
0&0&-1\\
0&-1&-n
\end{pmatrix},
\qquad \det G=-1.
\]
This determinant does not presume any Hodge cycle-class surjectivity.
It is forced by the genuine intersection geometry and is unchanged
by the degree or genus of the center curve.

Wolfram EXACT verification:
\[
G^{-1}=
\begin{pmatrix}
1&0&0\\
0&n&-1\\
0&-1&0
\end{pmatrix},\qquad GG^{-1}=I_3.
\]

Let \(\lambda_i(\alpha)=\int_Y \alpha\smile u_i\), the *independently
defined geometric* intersection measurements. Then
\[
\boxed{
\mathcal Z_\alpha
=\lambda_0(\alpha) Z_0+
[n\lambda_1(\alpha)-\lambda_2(\alpha)]Z_1
-\lambda_1(\alpha)Z_2.
}
\]
The kernel proof reconstructs \(\alpha\) whenever the three geometric
measurements jointly separate the true Hodge classes. This separation
does **not** assume algebraic representatives: by the classical
blow-up Betti formula \(b_4(Y)=3\), and the perfect Poincare pairing,
three geometric classes with \(\det G\ne0\) form a basis.
Consequently their geometric evaluations separate \(H^4(Y,\mathbb Q)\)
and, a fortiori, its rational Hodge subspace.

### Ample Lefschetz primitive class

For any sufficiently large positive integer \(m\), the rational
divisor \(A=mh-e\) is ample on \(Y\). Set
\(w=j_*(\xi\,q^*[P])\) and use \(h^3,w\) as an actual geometric
basis of \(H^6(Y,\mathbb Q)\). The projective bundle relation yields
\[
j_*\xi^2=\delta h^3+n w.
\]

Thus the geometric Lefschetz operator
\(L_A:H^4(Y,\mathbb Q)\to H^6(Y,\mathbb Q)\) has matrix
\[
L_A=\begin{pmatrix}
m&0&\delta\\
0&1&m\delta+n
\end{pmatrix}.
\]
Wolfram verified symbolically
\[
L_A
\begin{pmatrix}
-\delta\\-m(m\delta+n)\\m
\end{pmatrix}=
\begin{pmatrix}0\\0\end{pmatrix}
\quad\text{identically for all }m,\delta,n.
\]

The **explicit actual rational algebraic primitive cycle** is
\[
\boxed{
Z_{\rm prim}
=-\delta\,Z_0-m(m\delta+n)Z_1+mZ_2.
}
\]

Its class satisfies \(L_A(\mathrm{cl}Z_{\rm prim})=0\).
Also \(\int_Y\mathrm{cl}(Z_{\rm prim})\smile u_1=-m\ne0\)
for \(m>0\). This is a certified **nonzero** polarized middle
primitive algebraic cycle, constructed entirely from real projective
and exceptional algebraic loci. The all-genus argument covers
\(g\ge1\), where \(b_3(Y)=2g>0\), so these varieties cannot have
algebraic affine cell decompositions.

For genus two, \(n=5\delta+2\), giving the fully explicit integer
coefficient vector
\[
(-\delta,\,-m((m+5)\delta+2),\,m).
\]

### Verification boundaries / next executable proof obligations

1. The Lean files verify **linear algebra from separately stated**
   scheme-cycle and Hodge geometry. The projective bundle formula,
   blow-up Hodge decomposition, Gysin/cycle-class compatibility and
   Poincare pairing are mathematical geometric inputs, and are **not**
   newly kernel-proved inside these files.
2. Concretely construct the blow-up scheme carrier, exceptional
   projective bundle and the analytic Betti/Gysin comparison maps
   in the pinned Lean/Mathlib implementation. This is the
   missing bridge needed for a *fully formalized* scheme-level instance.
3. Generalize the Gram calculation to blow-ups of higher-dimensional
   centers, where the cycle generators and primitive Hodge rank may be
   larger. Prove new nonzero determinants from intersection data,
   not an assumed target-surjectivity statement.
4. The **original general Hodge conjecture** remains open for arbitrary
   primitive rational classes on arbitrary smooth projective varieties
   outside the demonstrated blow-up/cellular/divisor/CM geometries.
   Proving existence of universally sufficient geometric
   correspondences is still the fundamental obstruction.

No claim of arbitrary-variety universal Hodge algebraicity is made.


## Phase 3: unbounded geometric primitive rank on noncellular fourfolds

**Exact all-finite-rank Lean module:** \`GSTBlowupArbitraryRankDetector.lean\`.

For each integer \(r\ge1\), choose \(r\) mutually disjoint smooth
genus-positive curves \(C_1,\ldots,C_r\) embedded in \(\mathbf P^4\).
There is no fixed upper bound on this finite \(r\): general-position
projective translates of finitely many smooth embedded curves
are mutually disjoint because \(1+1<4\). Form the smooth fourfold

\[
Y_r=\operatorname{Bl}_{C_1\sqcup\cdots\sqcup C_r}(\mathbf P^4).
\]

The genuine classical blow-up cohomology decomposition gives
\[
b_4(Y_r)=1+2r,\qquad b_6(Y_r)=1+r,
\]
and \(b_3(Y_r)=2\sum_i g(C_i)>0\).
Thus these fourfolds are **not** algebraically affine-cell paved.
For an ample class \(A=mh-\sum_ie_i\), the classical Lefschetz theorem
makes \(L_A:H^4(Y_r)\to H^6(Y_r)\) surjective, and consequently its
primitive kernel has rational dimension exactly \(r\).

Let \(\delta_i=\deg C_i\), \(n_i=5\delta_i+2g(C_i)-2\), and define
the *actual native algebraic* sources
\[
Z_0=h^2,\qquad Z_{1,i}=j_{i*}q_i^*[P_i],\qquad
Z_{2,i}=j_{i*}\xi_i.
\]
They have the explicit **polarized primitive cycles**
\[
\boxed{
P_i=-\delta_i Z_0-
m(m\delta_i+n_i)Z_{1,i}+mZ_{2,i}.}
\]

The disjointness of exceptional supports makes the mixed
intersection readouts vanish exactly. For each \(i\), define the
genuine geometric detector
\[
\lambda_i(\alpha)=\int_{Y_r}
\alpha\smile\operatorname{cl}(Z_{1,i}).
\]
Then
\[
\boxed{\lambda_i(\operatorname{cl}(P_j))=-m\,\delta_{ij}.}
\]
For \(m>0\), the corresponding \(r\times r\) detector matrix is
invertible. These are \(r\) independently constructed native
algebraic primitive directions, not iterates of one Gaussian CM
operator. Since \(\dim_\mathbb Q\ker L_A=r\), they supply the
**entire** primitive rational Hodge sector for this special family,
provided the classical scheme/Betti identifications hold as stated.

A four-component Wolfram stress test used a nine-dimensional rational
middle cohomology model and a five-dimensional degree-six model.
It verified exactly:
* the full \(9\times9\) middle-intersection Gram determinant equals \(1\);
* the Gram matrix has full rank \(9\);
* each of the four independently constructed \(P_i\) lies in
  \(\ker L_A\);
* the primitive detector matrix is \(-mI_4\).

The Lean source proves a UNIFORM all-finite-index theorem:
if a family of actual native cycles has geometric rational
detector evaluations \(c\delta_{ij}\) with \(c\ne0\), then
**every rational linear relation among their cycle classes is
trivial**. Unlike a finite Wolfram experiment, the Lean statement
has no fixed bound on the index-set cardinality.

**Semantic firewall:** neither the finite-index Lean theorem nor the
fourfold geometric construction supplies an algebraic representative
for arbitrary Hodge classes on unrelated varieties \(X\).
This family demonstrates unbounded independent primitive directions
within a specific genuine geometric construction. Extending such
independent cycle sources to all arbitrary smooth projective \(X\)
without assuming equivalent Hodge surjectivity remains the original
open problem.


## Independent positivity audit

From the EXACT geometric intersection Gram, the polarized primitive
cycle above has self-pairing
\[
\int_Y\operatorname{cl}(Z_{\rm prim})^2
=\delta^2+2\delta m^3+n m^2.
\]
Wolfram verified this symbolic identity and its positivity whenever
\(\delta>0\), \(m>0\), \(n>0\). For genus two, substitute
\(n=5\delta+2\), yielding
\[
\delta^2+2\delta m^3+5\delta m^2+2m^2>0.
\]
This supplies a second, independent geometric nonvanishing detector
in addition to \(\lambda_1(Z_{\rm prim})=-m\).
The intersection-to-Betti comparison is a geometric hypothesis,
not a consequence of the polynomial calculation.


## Final execution checkpoint — focused Lean gates

The following are exact observed **successful** GitHub Actions results
for this research branch, with no local Lean installation:

| Gate | GitHub Actions run | Result |
|---|---:|---|
| Abstract three-source plus arbitrary finite blow-up transfer, and three-cycle rational reconstruction | 38733901418 | SUCCESS |
| Symbolic rational intersection Gram and explicit inverse | 38735055904 | SUCCESS |
| Any finite geometric rank via exact diagonal detectors | 38735896897 | SUCCESS |
| Native polarized nonzero primitive curve-cycle constructor | 38736568005 | SUCCESS |
| Actual Mathlib codimension-cycle / Stage-2G Hodge subtype bridge | 38736567960 | SUCCESS |
| Stage-2G rank-to-native-cycle landing with registered local dependencies | 38736743778 | SUCCESS |

All six gates compile their associated stated Lean theorems.
Earlier failed/cancelled runs were superseded by these successful
runs; neither a successful algebraic gate nor a full source census
claims a machine-checked analytic blow-up formula from first principles.

**Exact strongest mathematical result**: all rational Hodge classes on
finite blow-ups of projective space along disjoint smooth curves
have explicit algebraic representatives by the standard independently
known geometric blow-up decomposition. The polarized middle primitive
kernel can have any prescribed finite positive rank r, and an explicit
basis of actual algebraic primitive cycles is derived by the exceptional
geometry; its rank is certified by an exact intersection detector.

**Precise unresolved universal implication**: produce actual geometric
cycle representatives for *all* primitive rational Hodge classes of an
arbitrary smooth projective complex variety X, beyond varieties with
certified cellular, projective, CM or smooth-blow-up source geometries.
The current approach transports independently algebraic source classes
and proves their rank from geometry; it does not show every arbitrary X
admits a sufficient independent geometric source system.

**Next Lean integration target**: construct true blow-up morphisms,
exceptional projective bundles, push/pull/Gysin maps and cohomological
blow-up isomorphisms from the pinned Mathlib scheme/Betti API; instantiate
the already verified \`ActualSchemeCurveBlowupGeometry\` and
\`AlgebraicCycleHodgeSemantics\` with those operations. Then certify the
exact Gram-formula from the genuine intersection product on the chosen
blow-up instead of passing its numerical entries as hypotheses.

No custom full-Hodge axiom, arbitrary native preimage, forced
determinant nonvanishing, or target surjectivity field has been added
to any proved target theorem.
