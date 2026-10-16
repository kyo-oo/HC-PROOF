# GST primitive Hodge research: exact target, universal operations, and verified limits

**15 October 2026.** Contributor attribution intentionally anonymous.

## Nonnegotiable target

For every smooth projective complex variety X, every codimension p, and every rational Hodge class α in H^(2p)(X,Q) intersect H^(p,p)(X), construct a genuine algebraic codimension-p rational cycle Z with cl(Z)=α. More precisely the unresolved part is algebraicity of all primitive rational Hodge classes at middle degrees. This is the unchanged classical Hodge conjecture, not the existence of one primitive example.

A successful Lean proof must establish the geometry behind the cycle-class map and cannot insert an arbitrary Stage2G class-preimage, Hodge basis packet, geometric cyclicity axiom, or period equality equivalent to α being algebraic.

## Route 1: explicit all-variety primitive divisor constructor

File: \`GSTUniversalPrimitiveDivisorConstruction.lean\`.
CI: \`gst-universal-primitive-divisor.yml\`, initial 38697994233 failed because \`GSTUniversalLefschetzCurveCycles\` was not registered as a Lake root, not because its mathematics was refuted. Final corrected run **38698778620 — SUCCESS**. Earlier 38697994233 failed from a missing Lake root; the next attempt exposed and repaired one rational division-equality orientation.

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
CI: \`gst-universal-fourfold-primitive-extraction.yml\`, final corrected run **38698778667 — SUCCESS**. Its full dependency closure and explicit cycle construction compiled under GitHub Lean.

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


## Route 5: unbounded-dimension codimension-two primitive extraction

The new \`GSTUniversalCodimensionTwoPrimitiveExtraction.lean\` file
strengthens the fourfold correction to EVERY possible dimension
d>=4. It uses the actual weight-dependent Lefschetz arrows

\[
L^{d-3}: H^{2,2}(X,\mathbb Q)\to
H^{d-1,d-1}(X,\mathbb Q),\qquad
L^{d-2}:H^{1,1}(X,\mathbb Q)\xrightarrow{\sim}
H^{d-1,d-1}(X,\mathbb Q).
\]

For any rational (2,2) class α the standard analytic Hard Lefschetz
theorem and rational Lefschetz (1,1) theorem construct

\[
D_\alpha\in CH^1(X)_\mathbb Q,\quad
\mathrm{cl}(D_\alpha)
=(L^{d-2})^{-1}L^{d-3}\alpha.
\]

The actual **native algebraic codimension-two cycle**
\(Z_{\rm correction}=H\cdot D_\alpha\) satisfies
\(L^{d-3}\mathrm{cl}(Z_{\rm correction})=L^{d-3}\alpha\).
Therefore
\[
\alpha=\underbrace{\bigl(\alpha-\mathrm{cl}(H\cdot D_\alpha)\bigr)}
_{\in\ker L^{d-3}}\;+\;
\underbrace{\mathrm{cl}(H\cdot D_\alpha)}
_{\text{explicitly algebraic}}.
\]

If the input α is the class of an actual native algebraic
cycle Z, then subtracting the constructed correction from Z
returns an actual algebraic **primitive** codimension-two cycle.
This is a universal nonprimitive-component construction without
any global upper bound on d.

The original universal primitive algebraicity requirement remains
the equality of an arbitrary UNKNOWN primitive remainder with
the class of a concrete algebraic cycle. Nothing here assumes or
proves that assertion.

**CI:** \`gst-universal-codimension-two-primitive.yml\`,
run 38699408237 — **SUCCESS**. The actual arbitrary-dimensional
codimension-two algebraic correction compiled under Lean 4 without
new custom axioms or sorry placeholders. Older fourfold and divisor proofs
are independently green (38698778667 and 38698778620).


## 2026-10-16 Mathbox: arbitrary-fourfold primitive from an actual Gram minor

The exact universal target remains construction of rational algebraic cycles
for every primitive rational (p,p) class of every smooth projective complex X.
This record does not assert that target has been closed.

**New existing-file Lean results** in `GSTUniversalFourfoldPrimitiveExtraction.lean`:
`algebraicLefschetzCorrection_in_divisor_image`,
`primitiveizeNativeMiddleCycle_detector_invariant`,
`nonzero_native_primitive_of_numerical_detector`,
`primitive_native_direction_outside_prior_cycle_span`, and
`native_primitive_of_nonzero_intersection_gram`.
The first four were remote-kernel-verified by GitHub Action run 38910187554.
The Gram-minor theorem also passed its exact GitHub Lean kernel gate:
run 38910663004, conclusion SUCCESS, head 19ea255b36b6fbb50c401c92320f66008a1511d3.
This checks the Lean formalization, NOT the all-X existence conjecture.

Here is the new independent geometric test rather than an arbitrary Hodge
cycle-selector. On a smooth projective complex fourfold let U and Z be
**already constructed actual codimension-two algebraic cycles** and let
r_U, r_Z be rational linear readouts on the rational (2,2) Hodge fiber,
obtained in a genuine application from verified Poincare intersection
pairings. Suppose every divisor-Lefschetz class is in Q*[U]. Set

    D = r_U(cl(U)),  M = r_Z(cl(U)),
    C = r_U(cl(Z)),  N = r_Z(cl(Z)).

If the actual 2x2 determinant Δ = D*N - M*C is nonzero, the explicitly
constructed rational detector

    R(x) = D*r_Z(x) - M*r_U(x)

annihilates the ENTIRE divisor-Lefschetz image while
R(cl(Z)) = Δ ≠ 0. The universal fourfold GST algebraic Lefschetz
correction subtracts an actual native divisor product from Z, constructing

    Z_prim = Z - corrected_divisor_product(Z).

The proof gives primitiveTest(cl(Z_prim))=0 AND R(cl(Z_prim))=Δ≠0.
Thus a **nonzero algebraic primitive cycle exists** in this geometric
situation without assuming an algebraic representative of an unknown
Hodge target. This is existence, not an equivalent Hodge hypothesis.
The required U,Z, readouts, divisor-line property, and determinant must be
certified by independent geometry for each application.

For an actual symmetric intersection form take U=h^2 and r_U(x)=int_X x*h^2,
r_Z(x)=int_X x*[Z]. Then D=int_X h^4, M=C=int_X h^2*[Z],
N=int_X [Z]^2. The explicit rational cycle D*[Z]-M*h^2 is orthogonal
to h^2, with self-intersection D*(D*N-M^2). In a fourfold with one-dimensional
rational H^2 and H^6, orthogonality to h^2 additionally proves geometric
primitivity under the true Lefschetz map. This is a classical mathematical
interpretation of the exact Lean determinant certificate, not a fully
formalized scheme-theoretic intersection pairing in Mathlib.

The concrete cubic-fourfold-with-plane check gives (D,M,N)=(3,1,3),
Δ=8, primitive cycle 3[P]-h^2, self-pairing 24. This recovers and
extends the existing example with a reusable any-fourfold rank test.

**Three active completion routes:** (A) independently construct sufficiently
many algebraic surfaces and certify nonzero Gram minors, ultimately in every
primitive Hodge direction; (B) CM/NM correspondences across actual varieties
with proven period compatibility and rational descent; (C) fixed-class
calibrated integer-rectifiable geometric cycles. None currently establishes
all X, all p, all rational Hodge classes. The finite-dimensional Gram test
cannot create a missing actual source cycle or force the ranks to saturate.

## 2026-10-16 Mathbox: exact universal primitive residual detector firewall

Original target (NOT proved): for every smooth projective complex X, all
codimensions p, and each rational primitive class alpha of type (p,p),
construct an actual rational algebraic cycle Z on X with cl(Z)=alpha.

New formal theorems in EXISTING source
`GSTResidualNormZeroExactHodgeEquivalence.lean`, commit
`0e2f0346e7114e21cec134a6ddec7b3d846b478c`:

- `residual_orthogonal_to_every_native_cycle`
- `no_native_polarized_detector_of_residual`
- `missing_primitive_residual_positive_but_native_undetectable`

They passed the focused Lean kernel CI run **38912526573** (SUCCESS).
The transitive axiom audit for these declarations should be read in that
run's exact source output; the CI pass is not a classical Hodge proof.

Assumptions: Q is the rational polarized intersection pairing on the
primitive (p,p) Hodge fiber. P is a genuine native-cycle packet whose
actual cycle classes span the ENTIRE algebraic image A (not merely a
finite list of discovered representatives), whose detector coordinates
are Q-pairings with native generators. Such a basis of A is legitimate
when the rational Hodge fiber is finite-dimensional, regardless of
whether Hodge algebraicity holds.

For any rational primitive Hodge alpha set

    r(alpha) = alpha - cl(projectedNativeCycle(P,alpha)).

Then for EVERY native algebraic codimension-p cycle Z,

    Q(r(alpha),cl(Z)) = 0.

If alpha is hypothetically missing, the already verified positive
definiteness and projection facts imply

    Q(r(alpha),r(alpha)) > 0

at the very same time as EVERY native-cycle readout Q(r,cl(Z)) vanishes.
There is no contradiction. The new theorem explicitly rules out
saturating the missing direction solely by increasing the list of
already-native intersection detectors. In particular, a newly
DISCOVERED cycle still belonged to the mathematical definition of A
before it was discovered; it does not enlarge the complete image A.

Executed program routes, with exact first unresolved implications:

1. Full GST rank-free matrix units: these mix rational Hodge basis
   coordinates abstractly. Constructing equivalent *geometrically
   realized* operators on arbitrary X remains unproved; the existing
   native-realization firewall demonstrates why abstract operator
   identities are insufficient.
2. CM/NM, graph words, native commutators and rational Gram growth:
   when the operations are true algebraic correspondences, they act
   within A, and cannot pair nontrivially with r(alpha). Special
   geometries (P1xP1, cubic fourfold with a plane, abelian/CM and K3
   examples) yield genuine constructions only for their stated scopes.
3. Projective anti-graph and integral-current surgery: projective
   cellular parity identities do not extend to arbitrary X without
   independent algebraic basis cycles. A positive smooth closed current
   after an ample shift is NOT an integral rectifiable calibrated
   algebraic cycle; the latter independent geometric replacement is
   unproved for each arbitrary rational primitive Hodge class.

The only successful universal endgame would independently establish
that no nonzero residual r(alpha) is possible for the actual geometric
cycle map, or construct an actual algebraic representative of alpha
without assuming an equivalent reachability, Gram-saturation, or
period-certificate existence statement. We did NOT obtain that theorem.
The experiment eliminates a false universal inference but does not
rule out a fundamentally new GST geometric construction.

Next direct research attack, rather than more formal rank wrappers:
construct from alpha a genuinely closed integral (p,p)-calibrated
rectifiable representative in the exact rational homology class after
clearing denominators and a known algebraic ample correction. Check
every proposed GST N-current surgery preserves the prescribed
homology class and integral multiplicities; a smooth positive or weak
limit alone cannot discharge this. Independently investigate
geometrically obtained cross-carrier correspondences whose native
cycle outputs provably cover a previously unavailable primitive
Hodge direction, without using alpha as a preexisting cycle input.


## Mathbox 2026-10-16: exact all-X projective stabilization to primitive MIDDLE Hodge classes

**Unchanged universal target.** For every smooth projective complex
X, dimension d, rational Hodge (p,p) class alpha (primitive when 2p<=d),
construct an ACTUAL rational algebraic cycle representing alpha.
The target remains open: the following is an unconditional geometric
REDUCTION, not existence of a middle primitive cycle.

### An explicit construction on EVERY X, every p with 2p<=d

Put m=d-2p and Y=X x P^m (complex dimension d+m=2(p+m)),
with projections pi_X, pi_P. Choose an actual ample class h on X
and the actual P^m hyperplane class t. If alpha is primitive,
h^(m+1)*alpha=0.

Set the RATIONAL MIDDLE-HODGE class
  B(alpha) = sum_{j=0}^m (-1)^j pi_X^*(h^j alpha) pi_P^*(t^(m-j)).

All terms have Hodge type (p+m,p+m) and cohomological degree
2(p+m)=dim_C(Y). Multiplication by the PRODUCT ample class
H=pi_X^*h+pi_P^*t produces:
* interior coefficient of h^j alpha t^(m+1-j), j=1,...,m:
  (-1)^(j-1)+(-1)^j=0;
* P^m bottom boundary t^(m+1)=0;
* X top boundary (-1)^m h^(m+1)alpha=0.
Thus H*B(alpha)=0, i.e. B(alpha) is a GENUINE PRIMITIVE
rational middle Hodge class of Y. No chosen Chow preimage is used.

Fiber integration pi_{X*}:H^{2(p+m)}(Y)->H^{2p}(X)
takes the coefficient of t^m, hence pi_{X*} B(alpha)=alpha.
On algebraic cycles, if B(alpha)=[W] with W an actual codimension
p+m rational Chow cycle of Y, the genuine algebraic Chow pushforward
Z=pi_{X*} W has codimension p and [Z]=alpha by cycle-class
naturality. Conversely if alpha=[Z] is algebraic then the explicit
Chow packet sum (-1)^j pi_X^*(H_X^j * Z)pi_P^*(H_P^(m-j))
represents B(alpha). Hence for EVERY individual primitive alpha:

  alpha is algebraic on X  <=>  B(alpha) is algebraic on Y.

This is a pointwise correspondence of ACTUAL Chow classes and Betti
classes, not an invented 'algebraicity' marker in an abstract vector
space, and DOES NOT assume inverse Hard Lefschetz to be algebraic.

### Stronger bijective primitive-fiber theorem

The rational projective-bundle/Kunneth formula uniquely writes ANY
middle rational (q,q) Hodge class b of Y, q=p+m, as
  b=sum_{j=0}^m pi_X^*(b_j) t^(m-j),
where b_j has rational Hodge type (p+j,p+j) on X.
If H*b=0 then its coefficients obey:
  b_(j+1)=-h*b_j (j=0,...,m-1), and h*b_m=0.
Therefore b_j=(-1)^j h^j*b_0 and h^(m+1)*b_0=0.
The top-fiber coefficient b_0=pi_{X*} b is primitive.
Thus B and pi_{X*} are explicit MUTUAL INVERSES

  Prim^{p,p}_Q(X,h)  <==>  Prim^{p+m,p+m}_Q(X x P^m,h+t).

This holds for ALL smooth projective complex X and ALL p in 2p<=d,
without a dimension/rank bound or algebraic cycle assumption.

The verified Lean source GSTAllDimensionProjectivePrimitiveCycles.lean
proves the arbitrary-module signed recursion, boundary cancellation,
recovered source coefficient, inverse unique primitive classification,
and bidirectional primitive condition. Both targeted GitHub CI runs are
GREEN: 38916032821 (source-to-middle) and 38916436720 (both directions).
These are Lean kernel checks of exact rational coefficient algebra. The actual projective-bundle ring,
Hodge functoriality and Chow naturality are independent classical
geometric inputs not constructed inside that Lean module. Do not
mistake a coefficient theorem for complete Lean formalization of
analytification or Chow cohomology.

### Why this cuts down the quantifiers but DOES NOT end Hodge

The usual rational Hard Lefschetz decomposition expresses each
low-degree Hodge class as sums of ample powers of primitive rational
Hodge classes. High-degree classes are ample powers of low-degree
Hodge classes, by rational Hard Lefschetz. Therefore ALL rational
Hodge classes on ALL smooth projective X would be algebraic if,
and only if, EVERY rational primitive MIDDLE Hodge class on EVERY
even-dimensional smooth projective Y were algebraic.

This removes nonmiddle primitive geometry from the universal target
but does NOT establish middle primitive algebraicity on arbitrary Y.
In particular X x P^m is generally NONCELLULAR whenever X is;
no existing GST cellular, CM/NM orbit, or calibrated-current theorem
supplies the missing Chow representative automatically.

### Independent attack: finite projections lose primitive data

For a finite morphism f:X->P^d, let h=f^*H. If 2p<=d and p>=1,
alpha is primitive with h^(d-2p+1)alpha=0, then
f_*alpha = c H^p for rational c. By projection formula,
 c=int_{P^d}(f_*alpha)*H^(d-p)
  =int_X alpha*h^(d-p)
  =int_X (h^(d-2p+1)alpha)*h^(p-1)=0.
Hence f_*alpha=0 for EVERY primitive alpha.
Consequently finite Noether-normalization maps to cellular P^d
erase, rather than realize, the missing primitive Hodge directions.
This is a structural obstruction to using projective cellular
targets alone; it does not contradict Hodge on X.

**Exact unresolved existence obligation:** For each arbitrary
even-dimensional Y and primitive rational middle Hodge class b,
construct an actual algebraic middle-dimensional cycle W on Y
with [W]=b, WITHOUT assuming b already lies in the native image.
Only this new geometric input can promote the reduction to a
solution of the full conjecture.


## 2026-10-16 Mathbox: source-birth GST and rational-host primitive propagation

The proof goal remains construction of genuine algebraic-cycle representatives
of every rational primitive Hodge class on arbitrary smooth projective complex
varieties. GST graph V2 has now been strengthened within its own original
self-expanding world cosmology, not replaced by an alternate theory.

NEW INTERNAL GST THEOREMS in GSTGraphV2SelfExpandingCosmology.lean:
* TwoSourceBirth carries rational-native cycles and genuine rational Hodge
  cohomology for a parent world, independent source world, and a born world,
  with actual native transport, cycle-class compatibility and a genuine
  cohomological two-source decomposition (no native preimage of the target).
* every_newborn_hodge_class_has_native_cycle constructs an explicit native
  newborn cycle from source representatives.
* exceptional_native_birth_creates_new_hodge_direction detects an independent
  exceptional native cycle outside the whole parent Hodge image.
* SplitTwoSourceBirth adds actual native/Hodge retracts;
  split_world_birth_hodge_complete_iff_sources proves that completeness of
  the born world is equivalent to completeness of both source worlds.
* source_missing_direction_survives_birth, its exceptional counterpart,
  and algebraic_host_complete_iff_exceptional_complete characterize
  the inherited defect and the exceptional sector on a complete base.

The first two upgrades passed GitHub CI runs 38919599650 and 38920157401.
The specialized exceptional host theorem is separately run as 38920606718.
CI proves the GST algebraic birth calculus, not Chow blowup compatibility
on an arbitrary genuine scheme.

GEOMETRIC ALL-X HOSTING:
For any smooth projective X of dimension d, choose a closed embedding
X -> P^N with codimension c>=2. Let Y be the smooth projective blowup
Bl_X(P^N), a rational variety. The genuine blowup Chow and rational Hodge
formulas give compatible decompositions:
  Hdg^p(Y)=Hdg^p(P^N) (+) SUM_{j=1}^{c-1} Hdg^{p-j}(X)(-j),
  CH^p(Y)_Q=CH^p(P^N)_Q (+) SUM_{j=1}^{c-1} CH^{p-j}(X)_Q.
They instantiate the GST source-birth packet with source B equal to
the exceptional direct sum. Because P^N is Hodge-complete,
  all rational Hodge classes algebraic on Y (all p)
    IFF all rational Hodge classes algebraic on X (all p).
The unknown Hodge directions of an arbitrary X are thus faithfully
hosted as exceptional geometry INSIDE rational projective blowups.
This is not a proof that the host is automatically algebraic.

UNCONDITIONAL GEOMETRY FAMILY 1 (ALL DIMENSIONS):
Every smooth projective complex UNIRATIONAL variety X has algebraic
rational Hodge (2,2) classes. Resolve a dominant generically finite
rational map P^n --> X as smooth blowups of P^n followed by f:Y->X.
In degree four, the exceptional Hodge contributions for a blowup of
a smooth center Z are only H^2(Z)(-1) and H^0(Z)(-2).
They are genuine divisor and component classes, algebraic on every Z,
regardless of its dimension. Thus codimension-two Hodge algebraicity
passes through every blowup. Given any rational Hodge (2,2) alpha on
X, f^*alpha has an algebraic native representative on Y, and the
projection formula f_* f^* alpha=(deg f)*alpha gives a rational
algebraic representative on X. Hard Lefschetz gives the corresponding
codimension n-2 classes as ample powers when n>=4.

UNCONDITIONAL GEOMETRY FAMILY 2:
All rational Hodge classes on every smooth projective UNIRATIONAL
variety of dimension n<=5 are algebraic. In that range, blowup
centers on the resolution of P^n have dimension <=3, and ALL
rational Hodge classes on smooth projective centers of dimension
<=3 are algebraic by the Lefschetz (1,1) and Hard Lefschetz theorems.
The full Chow blowup decomposition and generically finite descent
finish this family.

The two families are rigorous arguments using genuine algebraic
geometric blowup and pushforward theorems; those SCHEME-level theorems
have NOT been formalized in the GST Lean module. New GST Lean theorems
certify source-birth logic, while these genuine geometric families
are mathematical instantiations, not machine-proved schemes.

REMAINING ORIGINAL SOURCE-DISCOVERY OBLIGATION:
Construct enough independent geometric source births for every primitive
Hodge class of arbitrary nonunirational varieties, with genuine
cycle-class compatibility. The actual new GST birth calculus permits
these births without restricting to old CM/NM within-world orbits,
but it does not postulate their universal existence.
