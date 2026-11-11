# Original GST Image-3: two-plus-ten curvature splitting and exact spectral resultant (11 November 2026)

**Base:** curvature branch `296478b17cd342eef7aa7f2361f764cd29a4f1ad`.
**New branch:** `research/gpt6-image3-advanced-curvature-rigidity-20261111`.
**Primary Lean:** `GSTImageThreeCurvatureResonance.lean` and `GSTImageThreeAdvancedGeometricSource.lean`.
**Exact computation:** `research/computations/GST_image3_CM_curvature_two_ten_resultant_factorization_20261111.wl`.
**Evidence:** exact symbolic Wolfram evaluation at a=0; exact rational sample checks at (a,b)=(0,1),(1,1),(2,1/3),(-2,5/4),(1,1/2),(0,0). These six checks illustrate the all-parameter identity; the structural proof below supplies its universal scope. The newest Lean kernel status MUST be read from the exact-HEAD CI, not inferred from Wolfram.

## 1. Correct, unaltered source operators

Take the **owner-original** 12-cell rational signal space
`V = (Fin 4 × Fin 3) → Q`, with original five-order shuffle `U`,
signed CM mirror `J` (so `J²=-I` and `JU=UJ`), original Wave-I
SURVIVE diagonal operator `M`, and original mixed seed
`v=e_(0,0)+e_(0,1)`.

The SOURCE operation studied here is

[
C=[J,M]=JM-MJ,qquad F_{a,b}=U+J+aM+bC,quad a,binmathbb Q.
]

No outside auxiliary signal matrix or presumed Hodge-to-Chow inverse is used.

## 2. The exact 2×2 original fixed-cell quotient

Put (s=(0,0)), (t=(3,2)). The exact original `U` shuffle and
`J` mirror preserve the two-cell set `{s,t}`; `M` is diagonal.
Consequently both the two-cell subspace and the complementary **ten**
original cells are invariant under every `F_(a,b)`. Under the order
`(s,t)`, the fixed-cell block is

[
A_{a,b}=
egin{pmatrix}
1&1+2b\\
2b-1&1+2a
end{pmatrix}, quad v_2=inom 10 .
]

The two-step Krylov determinant is **exactly**

[
det[v_2,A_{a,b}v_2]=2b-1.
]

Therefore the **two-cell projection** of the original GST orbit is cyclic
if and only if `b != 1/2`, uniformly for all rational `a`. This does
NOT by itself say the entire twelve-cell orbit is cyclic.

At the half-curvature resonance, the maximum-cell coordinate obeys
`(F_(a,1/2) u)_t = (1+2a) u_t`. The original seed has `v_t=0`.
Hence **every** iterate and therefore its **entire rational span**
lies in the proper hyperplane `ker(eval_t)`. This upgrades the
old single-iterate statement into a global linear-span no-go.

The fixed-block characteristic polynomial and discriminant are

[
chi_2(x)=x^2-(2+2a)x+(2+2a-4b^2),quad
Delta=4(a^2-1+4b^2).
]

Even at repeated eigenvalues (`Delta=0`), the fixed-block cyclic
seed criterion is still simply `2b-1 != 0`: it is a Krylov determinant,
not an assumption that `A` diagonalizes.

## 3. The crucial ALL-parameter 2+10 determinant identity

Order the original cells as `(s,t,remaining 10 cells)`. Moving the
original final cell into second position crosses precisely 10 cells,
so this permutation has sign +1. The original mixed seed has components
`v=(v_2,v_10)`, with `v_10=e_(0,1)` inside the ten-cell space.

Let `D_(a,b)` be the restriction of the same original `F_(a,b)`
to the remaining ten cells. Let

[
K_2=[v_2,A v_2],quad
K_{10}=[v_{10},Dv_{10},ldots,D^9v_{10}].
]

Then for **all** rational `a,b`,

[
oxed{
det K_{12}(F_{a,b},v)
=
(2b-1),det K_{10}(D_{a,b},v_{10}),
operatorname{Res}_x(chi_{A_{a,b}},chi_{D_{a,b}})
}.
	ag{*}
]

**Reason:** over an algebraic closure, on the Zariski-dense locus
where `A` and `D` have disjoint, simple eigenvalues, express each
Krylov matrix in its eigenbasis. The full Vandermonde decomposes as the
product of the two within-block Vandermondes and
`prod_(i,j)(beta_j-alpha_i)`. Since `2×10=20` is even, this cross
factor is the indicated characteristic-polynomial resultant with
**positive** sign, and the cell-order permutation also has sign +1.
The identity is polynomial in the entries of `A,D`; therefore it
continues to ALL parameters, including repeated and colliding spectra
and singular cyclic blocks. Alternatively it follows from the
block-Krylov/Sylvester determinant identity without genericity.

This produces three precise and INDEPENDENT native rank bottlenecks:

- **Fixed-cell controllability:** `2b-1=0`;
- **Ten-cell controllability:** `det K_10=0`;
- **Cross-block spectral collision:** `Res(chi_2,chi_10)=0`.

The **complete native twelve-cell cyclicity** condition is exactly the
simultaneous nonvanishing of these three quantities. This is
stronger than a single unexplained large determinant and supplies
smaller typed Lean targets.

## 4. Original curvature-only slice a=0: factor meaning upgraded

The earlier work reported

[
det K_{12}(U+J+b[J,M],v)
=b^4(2b-1)P_{10}(b)P_{16}(b).
]

The new exact split identifies the three factors **geometrically in
the original information carrier**, rather than merely symbolically:

[
det K_2=2b-1,qquad
det K_{10}=P_{10}(b),qquad
operatorname{Res}(chi_2,chi_{10})=b^4P_{16}(b).
]

Both `P10` and `P16` are the exact committed integer polynomials in
`GST_image3_CM_curvature_all_rational_strength_mod7_20261111.wl`.
That script's exhaustive mod-7 nonroot check implies neither
polynomial has a rational root (the leading coefficients are nonzero
mod 7 and the finite-field reduction is primitive enough for the
rational-root argument). Consequently for **every rational `b`**,
the curvature-only original 12-cell source is cyclic precisely
when `b != 0` and `b != 1/2`.

This immediately distinguishes the two known rational exceptional
strengths: `b=0` is a **spectral collision**, whereas `b=1/2` is
a **fixed-cell controllability failure**. In particular, the old
statement that both were just generic numerical rank failures hid
two different mechanisms. At `b=0`, the fixed pair itself remains
controllable (`det K2=-1`) but full cyclicity fails because
the ten-cell and fixed-cell characteristic polynomials overlap.

## 5. Exactly evaluated rational samples, independent of the a=0 argument

At parameters `(a,b)=(0,1)`, `det K2=1`,
`det K10=-130491` and `Res=-10623`, whose product is
`1386205893`.

At `(1,1)`, `det K2=1`, `det K10=-209893` and
`Res=2121393`, giving the independently reported balanced
determinant `-445265540949`.

Further exact rational checks at `(2,1/3)`, `(-2,5/4)`,
`(1,1/2)`, and `(0,0)` confirm the identity and expose
each failure branch. These are CHECKS of (*) and not the proof of
the all-parameter polynomial identity, which is the block algebra
argument in section 3.

## 6. Upgraded original-X correspondence typing

`GSTImageThreeAdvancedGeometricSource.lean` now distinguishes:

1. an abstract `CycleClassOperatorPair`;
2. a `RealizedFiniteClosedCorrespondence` with an **actual closed
   geometric carrier** on `X×X` and its separately proved Betti action;
3. five such realized geometric atoms `U,J,M,JM,MJ` together with
   exact action equalities certifying the ordered products `JM`
   and `MJ` on both native cycles and Betti cohomology.

Only at level (3) does the five-atom rational word
`U+J+aM+b(JM-MJ)` have a witness in a rational word of actual
finite closed correspondences. Its original-X Chow and Betti actions
then equal the Image-3 `geometricCurvatureF` operator pair.

**Important scope:** `JM` and `MJ` are supplied independently
realized geometric inputs in this new structure, not silently
manufactured by composing abstract linear maps. Construction of
these witnesses universally for every original `X,p`, and showing
their action gives the *canonical* Hodge full-rank landing, is NOT
deduced from the native spectral identity.

The existing `FiniteClosedCorrespondence` point transport currently
uses reduced/set-theoretic left-fiber multiplicity one; equating this
without additional intersection multiplicity hypotheses to the
full refined `CH^d(X×X)_Q` push-pull formalism would be an overclaim.

## 7. Correct scope with respect to Hodge

The new theorem is a **nontrivial structural theorem about the
author-original GST U/J/M/CM source**, not a universal
`X_GST` antecedent. A native full-rank wave orbit cannot by itself
imply that the canonical `cl_X: CH^p(X)_Q → W_p(X)` is onto.
A true geometric `F` preserving the actual Chow image necessarily
keeps that image invariant; an independent, noncircular
canonical full-rank Hodge landing is still required.

**Novel operational gain:** instead of attempting to force an opaque
12×12 determinant to be nonzero on the canonical target, future
geometric tests can try to realize and distinguish (i) the exact
two fixed-cell birth, (ii) ten rotating original-N cohomology
directions, and (iii) their spectral coupling, with separately
certified actual algebraic correspondences and canonical Hodge rank.
The division is an analytic reduction of the source bottleneck,
not an assumption that those geometric targets already exist.
