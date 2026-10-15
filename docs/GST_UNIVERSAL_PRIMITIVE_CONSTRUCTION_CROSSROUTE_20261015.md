# GST primitive Hodge research: exact target, universal operations, and verified limits

**15 October 2026.** Contributor attribution intentionally anonymous.

## Nonnegotiable target

For every smooth projective complex variety X, every codimension p, and every rational Hodge class α in H^(2p)(X,Q) intersect H^(p,p)(X), construct a genuine algebraic codimension-p rational cycle Z with cl(Z)=α. More precisely the unresolved part is algebraicity of all primitive rational Hodge classes at middle degrees. This is the unchanged classical Hodge conjecture, not the existence of one primitive example.

A successful Lean proof must establish the geometry behind the cycle-class map and cannot insert an arbitrary Stage2G class-preimage, Hodge basis packet, geometric cyclicity axiom, or period equality equivalent to α being algebraic.

## Route 1: explicit all-variety primitive divisor constructor

File: \`GSTUniversalPrimitiveDivisorConstruction.lean\`.
CI: \`gst-universal-primitive-divisor.yml\`, initial 38697994233 failed because \`GSTUniversalLefschetzCurveCycles\` was not registered as a Lake root, not because its mathematics was refuted. Updated run **38698441049** must be inspected for final status.

For X smooth projective of dimension d, fix ample h, and define the actual rational top-intersection functional on H¹(X,Q) (i.e. the Hodge (1,1) part of degree-two Betti cohomology):

\[
\deg_h(\beta)=\int_X \beta\smile h^{d-1},\quad \deg_h(h)=\int_X h^d>0.
\]

Given an actual divisor D and its Hodge class [D], construct the **native algebraic primitive divisor**
\[
D_{\mathrm{prim}}=D-
\frac{\deg_h([D])}{\deg_h(h)}\,H.
\]
All coefficients are rational; the output is an ACTUAL rational algebraic divisor, and \(\deg_h([D_{\mathrm{prim}}])=0\). If β is an arbitrary primitive rational Hodge (1,1) class, the established Lefschetz (1,1) theorem produces a divisor D with [D]=β, and the normalization preserves that target class **exactly**. This proves a genuine universal constructive algebraicity statement for *all primitive rational divisor Hodge classes*, subject to the standard Lefschetz (1,1) theorem and the natural Betti intersection pairing. It is not new to mathematics but is new explicit GST formalization.

The Lean input \`DivisorsRepresentHodge11\` denotes the independently established classical Lefschetz (1,1) theorem; HC-PROOF does not itself supply a formal proof of that analytic-geometric theorem. The new file must not be called fully formalized scheme geometry merely because its conditional algebra compiles.

## Route 2: algebraic fourfold Lefschetz correction and primitive native-cycle extraction

File: \`GSTUniversalFourfoldPrimitiveExtraction.lean\`.
CI: \`gst-universal-fourfold-primitive-extraction.yml\`, updated run **38698446453** must be checked.

For X any smooth projective complex fourfold, let L denote cup with the ample h. Hard Lefschetz gives L²:H²(X,Q)→H⁶(X,Q) an isomorphism of rational Hodge structures. Given *any* rational (2,2) class α, define
\[
\beta=(L^2)^{-1}(L\alpha)\in H^2(X,Q)\cap H^{1,1}(X).
\]
By the known (1,1) theorem, choose a genuine divisor D with cl(D)=β. Then the actual native algebraic correction \(h\cdot D\) has
\[
L(\mathrm{cl}(hD)) = L^2\beta=L\alpha.
\]
Therefore
\[
\alpha_{\mathrm{prim}}=\alpha-\mathrm{cl}(hD),\quad L\alpha_{\mathrm{prim}}=0,\quad
\alpha=\alpha_{\mathrm{prim}}+\mathrm{cl}(hD).
\]

This is a construction of an ACTUAL algebraic complement for every codimension-two Hodge class of any fourfold, and it can also take an already algebraic codimension-two Z and construct an actual algebraic primitive Z - h·D.

It does **NOT** establish an actual algebraic representative of an arbitrary unknown α_prim; proving this primitive representation is precisely what the original target requires. The finite-dimensional and Hodge-formal data fields in the Lean interface model classical theorems but are not proved inhabited by existing Mathlib constructions. Do not call the formal implication an unconditional formalization of Hard Lefschetz and Gysin in Lean.

## Route 3: stronger special-family primitive geometry (previously green)

\`GSTMiddlePrimitiveProjectiveProduct.lean\` / run 38692915421 green: for P²×P², primitive middle classes are precisely rational multiples of a²-ab+b², and each basis term is a genuine algebraic intersection (the scheme-cohomology identification is external). This constructs every primitive rational Hodge class in that explicit special fourfold.

\`GSTCubicFourfoldPlanePrimitive.lean\` / run 38694969552 green: a smooth cubic fourfold containing a plane has the explicit algebraic primitive class 3[P]-h², and the intersection pairing is nonzero. The file verifies the exact integer arithmetic of geometric intersection numbers, not the actual scheme construction in Lean.

\`GSTMaximalLinearHypersurfacePrimitive.lean\` / run 38695158747 green: smooth degree-d hypersurfaces of even dimension 2m containing a maximal linear plane P^m have an actual middle primitive algebraic class d[P^m]-h^m, with exact squared intersection (-1)^m d(d-1)^(m+1). Again it proves existence of **one** genuine primitive class in each stated special carrier family, not all Hodge classes on arbitrary varieties.

## Route 4: CM+NM rational rank audit

A single Gaussian CM operation J on a rational Hodge fiber, with J²=-id, has the seed orbit
\[
\mathbb Q[J]\cdot z=\{a z+b Jz:a,b\in\mathbb Q\}
\]
of rational dimension ≤ 2. No quantity of powers of J or *scalar* rational CM/NM coefficients increases that dimension. This is a structural consequence of J²=-id, not an arbitrary numerical threshold.

Wolfram exact calculation used the rational four-dimensional action
\(J=\begin{pmatrix}0&-1\\1&0\end{pmatrix}\oplus
\begin{pmatrix}0&-1\\1&0\end{pmatrix}\).
One seed orbit {J^k z}_{k=0}^{11} has **rank 2** while the ambient rational Hodge space has rank 4. Its characteristic CM relation J²+I=0 holds exactly. Thus a single CM Gaussian orbit is not a universal independent-direction generator. Higher rank needs genuinely independent *algebraically realized* seeds or correspondences mixing actual primitive cohomology.

**Important:** The numerical rank check is a valid example testing a proposed mechanism, not a counterexample to the Hodge conjecture.

## Wolfram exact projector consistency on P²×P²

In bases H²={a,b}, H⁴={a²,ab,b²}, H⁶={a²b,ab²}, with h=a+b, one has
\[
L:H^4\to H^6=\begin{pmatrix}1&1&0\\0&1&1\end{pmatrix},\quad
L:H^2\to H^4=\begin{pmatrix}1&0\\1&1\\0&1\end{pmatrix},
\quad
L^2:H^2\to H^6=\begin{pmatrix}2&1\\1&2\end{pmatrix}.
\]
The universal rational primitive projector is
\[
P_{\rm prim}=I-L(L^2)^{-1}L
=\frac13\begin{pmatrix}
1&-1&1\\-1&1&-1\\1&-1&1
\end{pmatrix}.
\]
Wolfram exactly verified P²=P, rank(P)=1, and L·P=0, with primitive generator (1,-1,1). Since a,b are genuine divisor classes, this particular projector is implemented by native rational algebraic cycle combinations, not an arbitrary Hodge matrix.

## Where the original arbitrary-variety problem stands

**NOT PROVED.** Already genuine universal algebraic primitives: codimension one via (1,1) and the opposite-to-divisor codimension d-1 via Hard Lefschetz. Constructed primitive corrections: codimension two of arbitrary fourfolds, and explicit middle primitive cycles for stated special varieties.

Still missing: for an arbitrary smooth projective X and an arbitrary *unknown primitive* Hodge class α in a middle codimension 2≤p≤d-2, produce a concrete algebraic Z with cl(Z)=α without injecting that equality or an equivalent geometric cyclicity premise.

Any universal proposed CM/NM transfer must establish that actual projective correspondences act nontrivially and span the primitive class space of the arbitrary target, rather than merely generate a rational scalar field or a Gaussian CM orbit of one seed. A failed theorem or an unfinished CI test must not be portrayed as a result.

No public internet search was performed.
