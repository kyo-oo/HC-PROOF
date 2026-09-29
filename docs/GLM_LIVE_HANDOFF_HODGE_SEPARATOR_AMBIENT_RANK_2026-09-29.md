# GLM live handoff — separator ambient-rank closure

Target branch: `sol/hodge-single-separator-successor`.

## Mathematical target

For a smooth projective complex scheme `V`, a native codimension-`p` point `x`, and the canonical projectively-live separator successor constructed by the current branch, prove

```lean
theorem separator_successor_ambient_coheight_exact
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hlive : ProjectivelyLiveSource
      V.projective.n (V.projective.immersion x.1)) :
    Order.coheight
      (carrierSeparatorSuccessor V x.1 hlive) = p + 1
```

Use the exact existing point expression if the current elaborator prefers `pointClosureι ... (pointClosureSeparatorSuccessor ...)`; the branch already proves these are the same carrier point.

## What is already proved and must be reused

Do **not** reconstruct the separator.

1. `GSTClassicalHodgeProjectiveSeparatorHeightOne.separator_minimalPrime_prime_height_one` proves that the selected minimal prime in the quotient by the source projective prime has exact height one.
2. `GSTClassicalHodgeSeparatorAmbientPrimeInterval.no_prime_strictly_between_source_separator` proves that there is no projective prime strictly between source and separator successor.
3. `GSTClassicalHodgeSeparatorRelativeCover.strictAbove_separatorSuccessor_eq_generic` transports that cover to the reduced source-closure scheme.
4. `GSTClassicalHodgeSeparatorRelativeCoheightOne` proves the lifted separator successor has relative coheight exactly one in the reduced source closure.
5. `GSTClassicalHodgeSeparatorRelativeCutLanding` proves that same successor actually lies in the scheme-theoretic principal cut and is non-generic.
6. `GSTClassicalHodgeRelativeSuccessorLowerBound.ambient_coheight_ge_succ` already proves

   `((p + 1 : Nat) : ℕ∞) ≤ Order.coheight (carrier successor)`.

7. `GSTClassicalHodgeSchemeCodimensionStalk.stalk_dimension_eq_coheight` gives

   `ringKrullDim (V.X.presheaf.stalk z) = Order.coheight z`.

So only the **upper bound** remains.

## The local-algebra proof

Let

- `y := carrierSeparatorSuccessor V x.1 hlive`,
- `R := 𝒪_{V.X,y}`,
- `P ⊂ R` be the prime corresponding to the generalization `x ≤/≥ y` under the stalk-localization correspondence (orientation must follow the specialization convention already used in `GSTClassicalHodgeRelativeSuccessorLowerBound`).

The proof is:

### A. `R` is a Noetherian regular local ring

`V.structureMap` is smooth over `Spec ℂ`; smoothness over a field makes every local ring of `V.X` regular. `GSTSmoothProjectiveNoetherian` already supplies the Noetherian scheme side. Do not introduce a new geometric hypothesis.

### B. The source stalk is the localization `R_P`

Because `y` is a specialization of `x`, the canonical generalization map identifies the source local ring with localization of `R` at `P`:

`𝒪_{V.X,x} ≃ R_P`.

Consequently

`dim R_P = dim 𝒪_{V.X,x} = p`

by `GSTClassicalHodgeSchemeCodimensionStalk.stalk_dimension_of_codimensionPoint`.

Equivalently `ht(P) = p` using `IsLocalization.AtPrime.ringKrullDim_eq_height` / the pinned localization-height API.

### C. The source-closure local ring at `y` is `R/P`

The reduced point closure used throughout the branch is the closure of `{x}` with the induced reduced scheme structure. At `y`, its local ring is the reduced quotient of `R` by the prime defining `x`. Since `P` is prime, `R/P` is already reduced, hence

`𝒪_{closure{x}_red,y} ≃ R/P`.

The branch proves the separator successor has relative coheight one, therefore by `ringKrullDim_stalk_eq_coheight` applied to the point-closure scheme,

`dim(R/P) = 1`.

### D. Regular-local rank additivity

For a Noetherian regular local ring `R` and a prime `P`, saturated prime-chain lengths are additive across `P`; equivalently

`dim R = ht(P) + dim(R/P)`.

This is the only local-algebra lemma that may require exposing/deriving an API theorem at the pinned Mathlib revision. It is a theorem of the existing smooth/regular geometry, **not a new assumption**. If Mathlib does not expose the exact combined statement, prove a small GST lemma from regular-local equidimensional/catenary rank behavior; do not add a field/hypothesis saying the equality holds.

Substituting B and C gives

`dim R = p + 1`.

### E. Return to ambient coheight

By `GSTClassicalHodgeSchemeCodimensionStalk.stalk_dimension_eq_coheight V y`,

`Order.coheight y = p + 1`.

This yields the desired upper bound, and combining with the already-existing lower bound is harmless if the chosen formal proof derives only `≤` from the local rank lemma.

## Immediate downstream wiring

Once the theorem above elaborates, add a theorem that feeds it directly to the existing single-successor survival theorem in `GSTClassicalHodgeSingleExactSuccessorSurvival` (use the exact theorem name/signature at current head). The output must be the unconditional nonzero separator/principal-cut operator. There must be no `hExact` parameter left at the public separator-survival entry point.

## Non-circularity firewall

Forbidden repairs:

- no `axiom`;
- no `sorry`;
- no hypothesis `hExact : coheight y = p+1` (or equivalent);
- no assumption of cycle-class surjectivity;
- no assumption that a flag-normal observable equals the bare Lefschetz/Poincare observable;
- no projective-visibility assumption equivalent to the Hodge conclusion;
- do not infer ambient rank equality from the cover relation alone. A cover only gives the lower jump unless catenary/regular rank rigidity is used.

## Mathematical reason this route is sound

The separator quotient-height-one theorem controls the interval **above the source prime**, while source codimension `p` controls the interval **below the source prime**. Smoothness supplies regular-local/catenary rank rigidity, which is precisely what prevents a different longer prime chain from bypassing the source prime on its way to the separator successor. Therefore the two independently certified ranks add to `p+1`.

After this lands, the separator successor is an actual exact codimension-`p+1` geometric state, and `GSTClassicalHodgeSingleExactSuccessorSurvival` can generate the first unconditional nonzero native geometric operator without importing any Hodge conclusion.
