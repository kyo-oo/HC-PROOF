# Mathbox — geometric CM isogeny projector onto exceptional Weil Hodge classes in EVERY codimension

**Target remains:** For all smooth projective complex X, all p and all prescribed rational (p,p) Hodge classes alpha, construct a true native algebraic cycle on original X with canonical geometric Betti class alpha. This route attacks an exceptional CM Hodge subspace that ordinary ambient Chern/Adams generators do not reach.

**Date / checkpoint:** 2026-10-17. **Initial SHA:** 0f6d731d0906cb1e2e8768057c94e53f241421f6. **Research branch:** research/gpt6-native-point-primitive-span-20261017.

## Geometric problem and actual objects

Let A be a complex abelian variety of dimension 2p (p>=1), of Weil type for K=Q(i): H¹(A,Q) is free of K-rank 2p and K acts on the complex Hodge H^(1,0) with equal sigma and conjugate sigma multiplicities p,p. Its complexified rational H¹ splits into 2p-dimensional K-eigenspaces W_sigma, W_barsigma; each has Hodge signature (p,p). The genuine rational Weil Hodge space

\[
 W_{\mathrm{Weil},p}\otimes_{\mathbb Q}\mathbb C
   =\bigwedge^{2p}W_\sigma\oplus\bigwedge^{2p}W_{\bar\sigma}
     \subset H^{2p}(A,\mathbb C)
\]
has rational dimension exactly **two**, with both complex lines of Hodge type (p,p).

The CM ring acts by actual algebraic group endomorphisms (isogenies) on A, not abstract formal GST operators. Let f=[2+i]:A→A; on H¹ its eigenvalues are lambda=2+i and mu=2−i. On H^(2p)=wedge^(2p)H¹ the r-th eigen-sector is

\[
 e_r=\lambda^r\mu^{2p-r},\qquad
 \mathrm{multiplicity}\;\binom{2p}r^2,\qquad 0\le r\le 2p.
\]
The pure eigensectors r=0 and 2p are precisely the two Weil Hodge lines. The central sector r=p has eigenvalue 5^p. All sectors are distinguishable because lambda/mu=(3+4i)/5 is **not a root of unity**: its sum with its conjugate is the rational number 6/5, which is not an integer, while a root of unity's rational algebraic-integer trace would be an integer.

## Exact all-p algebraic polynomial projector (constructive CRT)

Let t be a rational polynomial variable, set n=5^(2p), and for 0≤r<p define

\[
 G_r(t)=(t-e_r)(t-e_{2p-r})
       =t^2-2\Re(e_r)t+n\in\mathbb Z[t].
\]
The remaining central factor is t−5^p. Set
\[
 N_p(t)=(t-5^p)\prod_{r=1}^{p-1}G_r(t),\qquad
 G_0(t)=t^2-2a t+n,\; a=\Re(e_0).
\]
Reduce N_p modulo G0: N_p≡A_0+B_0 t. Since all spectral eigenvalues are distinct, this residue is nonzero modulo G0. Define
\[
 D=A_0(A_0+2aB_0)+nB_0^2\ne0
\]
and the **completely explicit rational polynomial**
\[
 \boxed{P_p(t)=
 N_p(t)\frac{A_0+2aB_0-B_0t}{D}.}
\]
The factor in the numerator is the inverse of A_0+B_0t modulo G0, because t²≡2a t−n modulo G0. Consequently P_p(t)≡1 mod G0 and P_p(t)≡0 mod N_p. By CRT, P_p(e_r)=1 for r=0 or r=2p and zero for all other r, and P_p²≡P_p modulo the minimal polynomial G0*N_p of f* on H^(2p).

**Geometric algebraic-correspondence construction:** Every power of the genuine isogeny pullback f* on rational Betti cohomology is realized by the transpose graph of an actual algebraic isogeny f^j. Hence the above rational polynomial P_p(f*) is the cohomological action of a **genuine rational algebraic codimension-2p correspondence on A×A**, with rank exactly two on H^(2p) and image exactly the Weil Hodge subspace. No Hodge class or algebraic preimage was inserted into its construction.

For p=2 there is a smaller formula using f=[1+i]. The normalized action U=f*/4 on H⁴ satisfies U⁴=1, with eigenvalues −1,−i,1,i,−1 and multiplicities 1,16,36,16,1. Its minus-one projector is
\[
 P_{\mathrm W}=\tfrac14(I-U+U²-U³)
             =\tfrac14 I-\tfrac1{16}f^*+\tfrac1{64}(f^*)²-\tfrac1{256}(f^*)³.
\]
This also is an actual algebraic correspondence on A×A. The Lean module GSTUniversalCMArithmeticObstruction.lean contains the ring/field proof of idempotence modulo U⁴−1, the minus-one/plus-one/quadratic eigensector filters, and the dimension census 70→2.

## Exact Wolfram and GitHub certificate

Wolfram determined that for p=2 and f=[2+i],
G0=t²+14t+625 and N=(t−25)(t²−30t+625).
For p=3, G0=t²+234t+15625 and N=(t−125)(t²−150t+15625)(t²+70t+15625).
Using PolynomialExtendedGCD, it found an exact rational polynomial P_p with P_p(e_r)=[1,0,...,0,1] for both p=2 and p=3. The p=2 [1+i] projector polynomial is 1/4−t/16+t²/64−t³/256 and has scalar idempotent factor
(P²−P)=(t⁴−256)(t²−8t+48)/65536.

The repo's pure standard-library exact-rational certificate
research/computations/weil_cm_correspondence_projector.py computes eigenvalues, conjugate quadratic spectral factors, Bezout inverse, rational projector and idempotence remainders for **all p=1,...,8**, and checks dimension C(4p,2p) with rank 2 in each case. [GitHub Actions #39058710211](https://github.com/kyo-oo/HC-PROOF/actions/runs/39058710211) **SUCCESS** at source SHA 061a6087a666e934ac3edc84bdeb70a6a1f09216, with complete pinned Hodge Lean integration and sorryAx check, evidence artifact 12109993388, digest sha256:9d73715797ccb4df084827b4b0b63adc6711dff88e65ddcddfd9efc71cbee34a. Its exact log enumerates p=1..8, rank2 and degree2p projectors; the uniform CRT argument above supplies the all-p proof independently of that finite test.

## What this actually advances and what remains

This explicitly geometrizes the previous GST-CM formal higher-degree Hodge charge atoms using genuine complex abelian varieties and actual algebraic CM isogenies, producing a **canonical algebraic-correspondence projector** whose image is a difficult rational Weil Hodge space in every middle codimension p. This is stronger than the earlier raw character-lattice sums and finite CM trace tests: the sector really exists as a Hodge subspace of smooth projective geometry and has an independently constructed algebraic projector.

**Crucial distinction:** An algebraic correspondence projecting onto a two-dimensional Hodge subspace is not by itself an algebraic representative of either of its Hodge classes. The projector may act as zero on all currently available algebraic source cycles while acting as the identity on the missing Weil classes. Applying the projector to a *prescribed Weil Hodge class* produces the same class cohomologically, not an algebraic cycle. There is no illicit step here claiming that the projector manufactures its own target witnesses.

**Next exact actual-source obligation (Gate 3):** Construct at least two independent genuine algebraic codimension-p source cycles on the original Weil-type A whose projected classes span W_Weil,p, and then extend the source mechanism to arbitrary original X. For a first positive test, take a split Weil-type abelian fourfold built from CM elliptic curves and identify algebraic graph/divisor intersections with nonzero CM projector image; determine which geometric deformation obstruction prevents transfer to an arbitrary Weil-type fourfold. This explicitly tests **source birth**, rather than constructing another representation theorem conditional on source existence.
