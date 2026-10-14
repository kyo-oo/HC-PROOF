# Mathbox + Wolfram assessment of the photographed GST/CM proposal

**Date:** 2026-10-14
**Base source:** User-supplied image (not added to Git).
**Live formal artifact:** `GSTMathboxCMNumberBridge.lean` on `mathbox/bd23-single-operator-charge-wedge`.
**Exact public acceptance target:** `HodgeConjecture.ClassicalHodgeTarget` without circular premise of algebraic-cycle surjectivity.

## A. Faithful parsing, no implicit repair of an undefined equation

The first photographed expression appears to be

```text
99*x * sqrt( ((a*x^4)_3 - (b*y^4)_3) / ((psi)^2 * xi_7) ).
```

Both subscripted expressions `(_)_3`, the indexed `xi_7`, and the
`psi` symbol lack typed definitions or quantifiers. The expression
has no visible equality or geometric target, so it is not presently a
theorem. We temporarily call the numerator terms A and B and the
denominator factors psi and xi in a **rational squared-radicand** model.
This does **not** assume subscript 3 denotes a base-three digit,
coordinate component, or third derivative.

The second expression is read approximately as
`L(S)*ell(s) - T(S)*ell(s) != T(Non-Zero N)`.
The right-hand term `T(Non-Zero N)` needs a typed definition; even the
asserted inequality has no supplied universally quantified premises.
We do NOT replace the user's inequality by equality or reverse its sign.
In a vector-space interpretation, `L=T` makes the left side zero and
may defeat the inequality whenever the right side also vanishes. Thus a
new **geometric transversality witness** is required, not symbolic
nonzero postulation.

The third expression visibly features `zeta(s)`, an infinite indexed
sum of `1/(x^1-y^2)`, and a tensor-like `H × Q` or `H ⊗ Q` operation.
Its index label resembles `n→R`, rather than a conventional integer
lower bound. Neither a summation index in the summand nor a defined
tensor-domain map is present. We do not claim the displayed object is
a well-defined convergent zeta series.

## B. Exact Wolfram computations

1. For symbolic A,B,psi,xi,x, Wolfram computed

   `[99*x*Sqrt[(A-B)/(psi^2*xi)]]^2 =
       9801*x^2*(A-B)/(psi^2*xi)`

   on the appropriate real-square-root domain. A=B gives value 0,
   for instance A=B=2,psi=1,xi=7,x=1. With A=9,B=2,
   psi=1,xi=7,x=1 the unsquared expression is 99.

2. CM-multiplication plane model over rational coordinates:

   ```
   M(a,b) = [[a,-b],[b,a]]
   det M(a,b) = a^2+b^2.
   s=(1,0), ell(s)=first coordinate,
   T(s)=M(a,b)s=(a,b).
   ell(s)T(s)-ell(T(s))s = (0,b).
   ```

   The genuinely useful transverse coordinate is b. For a=1,b=0
   the CM determinant is 1 but the charge wedge is zero. For a=0,b=1
   the determinant is again 1 and the charge wedge is (0,1). Thus a
   nonzero CM norm does **not** force geometric rank-gain by itself.

3. For constant `c=1/(x-y^2)`, the N-term sum is exactly `N*c`.
   In particular when x=5,y=2, the first 1..6 partial sums are
   `1,2,3,4,5,6`. A nonzero index-independent summand does not
   define a finite ordinary convergent infinite sum.

4. **Optional repaired candidate**, NOT claimed to be the original law:

   ```
   F(s,u,v) = Sum[ 1/(n^s+u^2+v^2), {n,1,Infinity} ]
   ```

   For real u,v and s>1, denominators are positive, and the
   sum is dominated by the p-series `Sum[1/n^s]`, so it converges.
   Wolfram checked the explicit illustrative case `s=2,u=1,v=0`:

   ```text
   Sum_{n=1}^∞ 1/(n^2+1) = (pi*coth(pi)-1)/2
                            ≈ 1.07667404746858117.
   ```

   This candidate is analytic and nonzero but is **not** an actual
   Hodge class nor an algebraic-cycle representative without a
   separate comparison map to geometric cohomology.

## C. Lean theorems actually attempted

The new Lean file models the first formula via
`conversionRadicand` and proves a nonzero criterion and a zero
counterexample. It models CM multiplication by a rational 2x2 matrix,
proves the determinant identity and computes the charged wedge. It
proves the exact finite partial sum law of the third expression.
Finally, `rank_two_hodge_cycle_of_verified_CM_geometry`
connects a **genuinely realized** correspondence with a verified
nonzero CM-style transverse coordinate to the existing native
charge-wedge Hodge realization theorem.

The crucial required input is an honest geometric equality
```lean
imagRead (movedSpine G E) = b
```
with `b ≠ 0`, plus a functional satisfying
`imagRead (spineHodgeSeed G p) = 0`. These are **not** derived by
the CM matrix algebra itself. The actual realization theorem is
conditional on an independently constructed geometric operator E
and rank two; it is not a proof of the unconditional Hodge conjecture.

## D. Next exact mathematical obligation

Define a specific CM-bearing smooth projective complex scheme V,
a true finite closed correspondence K on it, its canonical
cup/Gysin Betti operator T on all relevant cohomology, and a
rational Hodge coordinate functional `imagRead`. Prove
`imagRead (T(spineHodgeSeed G p)) != 0` by actual intersection/
period arithmetic. Compare that genuine operator to
`RealizedCorrespondenceExpr V H p` and obtain the conditional
rank-two cycle theorem without assuming a target preimage.

For arbitrary higher-dimensional fibers, prove a family of
independent transverse native cycle classes, not merely a nonzero
single-operator CM norm. The user's GST universe remains the
working setting, but formal derivations may not assume the very
rank-generation statement they aim to establish.

## E. Verification record

The new file has an isolated GitHub Actions gate
`.github/workflows/gst-mathbox-cm-number-bridge.yml`.
Report its exact run ID and completed result only after GitHub
finishes. Earlier green runs for the adjacent rank-two and
arbitrary-rank modules do not imply this new source compiles.

## F. New CM source-to-target dictionary in the existing repository

A second mathematically load-bearing issue is the coefficient field.
The original Hodge statement is about rational cohomology and
codimension-p native **Q**-cycles. Zeta and general CM periods
typically take real/complex values and do **not** automatically define
Q-scalar coefficients for those cycles. Wolfram's
`Zeta[2] = Pi^2/6` makes this issue concrete.

The following existing HC-PROOF modules are immediately relevant:

- `GSTClassicalHodgeCMThetaPeriodExtraction.lean` proves that a
  nonzero finite double sum of CM theta periods has a nonzero term.
  It does **not** independently construct a nonzero geometric period.
- `GSTClassicalHodgeCMConstructiveSurfaceDescent.lean` constructs
  target rational native cycles from finite cross-carrier point
  incidence and an actual extension-field coefficient expansion.
  Its exact source and Betti expansion premises remain visible.
- `GSTClassicalHodgeCMGSTNativeBasisCompiler.lean` consumes
  `CMGSTNativeSheetProgram` packets. Each packet carries a
  true source variety, explicit source cycles, a point kernel,
  a geometric pointwise Betti law, a GST program, and a
  coefficient expansion into the desired Hodge basis class.
  It does not automatically generate such packets.

**Bridge obligation suggested by the photograph:** build a genuine
CM theta/incidence construction with a nonzero transverse period
coefficient; compile its Betti action from the geometric source;
then use `GSTClassicalHodgeCMNativeRationalDescent` to show the final
native cycle has Q coefficients. This is a precise mathematical
research route rather than the unjustified assumption that an
arbitrary complex zeta scaling preserves rational Hodge classes.

### Additional Lean equations checked in the next revision

- `indexedCMKernel_pos`: an explicit proposed index-dependent
  CM number kernel is positive at every finite index.
- `indexedCMKernelPartialSum_pos`: every nonempty finite partial
  sum is strictly positive.
- `photographed_E2_nonzero_not_universal`: a rigorous zero-map
  countermodel to the unconditional operator nonvanishing reading.

These are independent arithmetic facts. Positivity of a finite
analytic kernel by itself does not prove a nonzero actual geometric
theta period. The completed new-workflow CI run must be checked
before calling this revised file green.

## G. Literal real 99x radical now formalized (current revision)

The latest `GSTMathboxCMNumberBridge.lean` revision adds
`photographedConversion x A B psi xi` over the reals and its
fully quantified squared-radical identity, subject to the essential
nonnegative radicand condition. It proves
`photographedConversion_ne_zero` from `x != 0` and a strictly
positive radicand, plus a counterexample
`photographedConversion_equal_inputs` where A=B.

This resolves the *algebraic interpretation* of the page's Equation (1)
under symbolic indexed inputs. It does not define the supplied subscript
3 (digit, coordinate, tensor grade, or something else), nor does it
construct a geometric period, CM correspondence, or a nonzero Hodge
direction from that expression.

The fresh GitHub kernel result for this exact source revision must be
checked before the theorem is called Lean-verified.

## H. Exact verified status for the photographed-equation proof file

The latest standalone Lean run **38597550496** completed successfully
for source commit `ffe0dcc2ecee0caa59d8b560c8f22c649d70f885`.
It checked the complete `GSTMathboxCMNumberBridge.lean` source,
including the exact real 99*x radical lemma, scalar operator E2
countermodel, finite CM kernel positivity, rational CM matrix
determinant, and conditional rank-two Hodge-cycle bridge.
Its `#print axioms` audit reported no `sorryAx`.

The earlier revisions also passed: **38596431461** and
**38597081569**. The full public `HodgeConjecture.lean` run
**38585691719** is a distinct, longer check and must never be
presented as passed until its own conclusion is observed.

The user's numbered equations have now yielded real,
kernel-verified algebraic and geometric-conditional results.
Their claimed unconditional geometric conversion and the
all-varieties Hodge conjecture are NOT proved: there is still no
unconditional geometric construction of the required CM transverse
Betti action nor a general rank-full native cycle class family.
