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
