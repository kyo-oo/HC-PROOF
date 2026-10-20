# GST Mathbox — integral Weil lattice Gram, CY6 Ext pressure, and the effective-source no-go

- **Date:** 2026-10-20 (IST)
- **Kind:** structural proof attempt, exact exterior audit, and a scoped geometric obstruction
- **Program/route/claim IDs:** universal original-X rational Hodge-to-Chow, Gate 3; integral split CM Weil source
- **Base checkpoint:** `56c32b0a5f6b90134d43e772bfbdfd8984327c07`
- **Target:** universal construction of a genuine original-X algebraic representative of every rational Hodge class; local discrimination on the smaller integral Weil source
- **Hypotheses and types:** (A=E^6) at split CM, with three elliptic pair factors, integral divisors (A_j,B_j\in CH^1(E^2)), and genuine integral Betti cup product. The Lean Gram law is in any `CommRing` given the surface intersection equations. The Serre pressure law is an integer consequence of its explicitly provided Euler identity.
- **Conventions:** on each pair (S_j), (A_j^2=B_j^2=-2[p_j]), (A_jB_j=0), and ([p_1][p_2][p_3]) integrates to (+1) in complex orientation. The exterior enumerator indexes `e1..e6,f1..f6` and accounts for the sign (-1) converting to complex `e1,f1,...,e6,f6` orientation.
- **Prior attempt:** [four-divisor integral Weil K0 source](2026-10-20-gst-four-divisor-integral-weil-k0-source.md). Its finite exterior Gram calculation was not a reusable Lean theorem across all coefficients.
- **Distinct mechanism:** preserve the Gaussian orthogonal tensor law under three pairwise source factors; deduce the entire integral Weil Gram and CY6 Euler pressure, then test effective support and ample-polynomial deformation.
- **Success criterion for this route:** kernel-certified general Gram and Serre pressure, plus a mathematically checked obstruction to the naive effective/line-bundle-only nonsplit realization. This does not constitute Gate 3 completion.
- **Failure criterion:** a nonzero primitive (W) that is an ample cubic, a nonzero ((h\smile W)), or an exact pair-orthogonality identity failing over a commutative ring.
- **Evidence label:** exact Gram and integer implications **proved in Lean** at pinned revisions listed below; geometric consequence **conditional on the canonical Betti/divisor and positivity identifications**; no universal Hodge claim.
- **Review:** Mathbox-guided self-review, independent Python exact exterior enumeration and polynomial ideal reduction, not independent geometric referee review.

## Reusable uniform algebra

Define the integral real and imaginary source classes by the already-constructed four signed triple-divisor expressions
[
W_R=-A_1A_2A_3+A_1B_2B_3+B_1A_2B_3+B_1B_2A_3,
quad
W_I=B_1A_2A_3+A_1B_2A_3+A_1A_2B_3-B_1B_2B_3.
]
The generic Gaussian pair law in the existing Lean file states that, when (x^2=y^2), (xy=0), (u^2=v^2), and (uv=0), the real and imaginary parts of ((x+iy)(u+iv)) have **equal square** (2x^2u^2) and **zero mixed product**. Iterate it three times over the actual surface equations to get
[
W_R^2=W_I^2=-32P,qquad W_RW_I=0,qquad P=[p_1][p_2][p_3].
]
Hence every pair of integral combinations obeys the bilinear identity
[
(mW_R+nW_I)(m'W_R+n'W_I)=-32(mm'+nn')P.
]
Over canonical rational Betti cohomology, (deg P=1). The corresponding pure-(mathrm{ch}_3) perfect (K_0) class (F_{m,n}) has, **if genuinely realized with all other Chern-character grades zero on the abelian sixfold**, the HRR invariant
[
chi(F_{m,n},F_{m,n})=32(m^2+n^2).
]
CY6 Serre duality then implies
[
e_0+e_2\ge 16(m^2+n^2),qquad
e_2\ge16(m^2+n^2)-1 	ext{if }e_0=1.
]
For a simple basis class ((m,n)=(1,0)), this is (e_2\ge 15); for ((1,1)), (e_2\ge31). Unlike the old 4800-scaled graph-numerator obstruction, these bounds do NOT force a failure of injectivity into the 495-dimensional raw semiregularity target.

## Exact exterior primitivity and effective-support obstruction

The source forms in the fixed 12-dimensional exterior algebra are
(A_j=e_j\wedge e_{j+3}+f_j\wedge f_{j+3}) and
(B_j=e_j\wedge f_{j+3}-f_j\wedge e_{j+3}).
Let (h=\sum_{k=1}^{6}e_k\wedge f_k), the standard product polarization. Directly, for every (j), the individual (A_j) and (B_j) wedge to zero with **both** (e_j\wedge f_j) and (e_{j+3}\wedge f_{j+3}). Every four-product summand of each Weil generator contains exactly one of (A_j,B_j) from **every** pair (j). Consequently
[
h\smile W_R=h\smile W_I=0;
qquad h^3\smile(mW_R+nW_I)=0.
]
The full 12-generator exterior enumerator confirms both (hW) products vanish, the diagonal (-32I_2) intersection in complex orientation, and zero mixed intersection. There are 32 nonzero signed coefficients in each (W_R,W_I), so for a nonzero integer pair the class itself is nonzero.

For any **nonzero effective** algebraic codimension-three cycle (Z) on this smooth projective sixfold, positivity of the degree against an ample class gives
(int_A h^3[Z]>0). A nonzero integral Weil class has this intersection **zero**. Therefore **no nonzero integral Weil class can be the class of an effective codimension-three cycle**. In particular a single coherent sheaf of rank zero with (mathrm{ch}_0=mathrm{ch}_1=mathrm{ch}_2=0) cannot have precisely this nonzero (mathrm{ch}_3): its leading support cycle in codimension three would be effective. Signed Chow combinations and alternating derived complexes remain possible, as already constructed at the split CM fibre.

This is a no-go for **one effective/pure-support coherent source**, not an obstruction to algebraicity in the rational Chow group and not a counterexample to Hodge.

## Why the naive nonsplit line-bundle recipe also fails

At a nonsplit polarized Weil period with (mathrm{NS}_{\mathbb Q}(A)=\mathbb Q h) (an explicit **hypothesis**, not asserted for every period), every line bundle has rational first Chern class proportional to (h). Hence any finite integral combination of line-bundle Chern characters and skyscraper sheaf characters has codimension-three component in (\mathbb Q h^3). For a nonzero primitive Weil class (W) with (hW=0) and (h^4\ne0), (W=q h^3) would imply (q h^4=0), hence (q=0) and (W=0), a contradiction. The new generic Lean lemma `cmWeilCMIntegralPrimitiveNotAmpleCubic` formalizes the required rational-linear separation.

Therefore the central split formula built from special CM divisor line bundles and point corrections **cannot deform component-by-component as an assembly of line bundles and points** into such a rank-one Néron–Severi period. If a genuinely coupled nonsplit perfect source exists, its deformation must abandon that naive constituent presentation (or use genuinely new sheaves/perfect objects).

## What this test does and does not establish

- **Proved as written in Lean:** Gaussian orthogonality, full Gram, all-integer bilinear formula, numerical CY6/Serre implications under the stated Euler relation, and abstract primitive-versus-ample-cubic separation. The latest CI results must be matched to their exact proof commits.
- **Exact computational cross-check:** the ring quotient ((A_j^2+2p_j,B_j^2+2p_j,A_jB_j)) reduces the two self-squares to (-32p_1p_2p_3) and the cross product to zero. An independent 12-symbol exterior enumeration gives (hW_R=hW_I=0) and the same Gram after orientation conversion.
- **Conditional geometric interpretation:** the divisors, Betti intersection, positive ample degree, rank-one Néron–Severi hypothesis when used, and HRR/Serre comparison are geometric inputs beyond the present ring-only Lean theorems.
- **First unresolved implication:** construct a nontrivial, genuinely coupled perfect object on a nonsplit Weil sixfold whose class is this *small* integral Weil source, and show (mathrm{At}(F)\lrcorner\kappa=0) in actual self-(operatorname{Ext}^2), then prove the canonical Betti comparison.
- **Original universal target:** Gate 3 remains open for **all** original (X,p,alpha); neither this split CM source nor the nonsplit locus alone covers arbitrary varieties.
- **Route disposition:** the Gram/Ext certificate succeeded; the naive effective-sheaf and line-bundle-only extension routes are excluded in their stated scope; the derived-coupled route remains open.
- **Artifacts:** `GSTUniversalCMArithmeticObstruction.lean` commits `efe5fd7f8befaeaa224667424142b5ffc341911e` (pinned GREEN run #39361657338), `f8bf2a0e89f4531406b8c1218a36253896ee6b52` (pinned GREEN run #39362181323), and `772f8c3107fba54705122e453268ad1f2aabe36a` (pinned CI status to verify).
- **Next discriminating check:** explicitly calculate an Atiyah/Kodaira–Spencer obstruction for a *genuinely coupled* (not direct split-sum) low-integral Weil perfect source, with its true derived geometric model and canonical Chern character; alternatively find a counterexample to the proposed low-rank coupling, not to Hodge itself.
