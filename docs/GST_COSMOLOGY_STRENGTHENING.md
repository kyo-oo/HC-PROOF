# GST cosmology strengthening

Base: `c833d9bd23d376eeb14246b675572f2cb8c66e51`.

## Run 86 continuation — verified in run 88

This continuation starts from `624a97f30f53decf45b9fedb8a759b6655096e09`
on `gst-cosmology-strengthening`, preserving the intervening repair work.
Run `35829999299` (number 86) failed in two modules:

- `GSTGhostRayExclusion.ghostRay_iff_residue_shape`: rewriting `3^k`
  throughout the shape identity also changed the modulus of the residue.
  The repair transports only the free scale on the right side of the
  equality, keeping the same residue in the equation and the goal.
- `GSTClayOfficialV2.rational_hodge_iff_all_weights`: the off-diagonal
  hypothesis retained record projections. The repair exposes the carry and
  digit fields and passes the off-diagonal contradiction directly.

Four existing theorem statements are strengthened in place:

| Declaration | Stronger statement |
|---|---|
| `shift_boundary` | Extinction of every world iff some axis boundary is crossed; arbitrary axis sets and zero depths are included |
| `synthesis_injective` | Positive-depth assumption removed |
| `monomial_class_ne_zero` | Arbitrary integer amplitude survives iff nonzero and bounded on every axis |
| `raising_operator_nilpotent` | Extinction by `topDegree / r + 1` steps instead of `topDegree + 1` |

Additional derivations in the existing files give exact displacement-iterate
extinction, accumulated-degree extinction for ordered noncommuting dynamics,
coherent-world reconstruction from arbitrary cofinal observation families,
and exact prefix/tail splitting of finite observations.

The coverage inventory now contains 117 files and 163 named declarations;
these are accumulated counts, not newly verified results. Every added
declaration is included in the transitive axiom audit.

Run 87 compiled the strengthened modules and confirmed both run 86 repairs,
then exposed adjacent documentation comments in
`GSTWorldtraceMahlerRelativePrecision.lean`. Moving the ghost-lock comment
back to its theorem repaired that parser error without changing a proof.

The complete cosmology upgrade gate passed on proof-source commit
`301f7c496b215840455b606b8dd2c20930d162c2` in
[run 88](https://github.com/kyo-oo/HC-PROOF/actions/runs/35833172844):
source proof-escape rejection, upgraded cosmology compilation, absence of
`sorryAx` in the upgraded crowns, the public strengthening declaration axiom
audit, and full `HCProof` integration compilation. This is the verification
receipt for the current continuation; historical runs below validate their
stated commits only.

The existing finite observation checks also pass. Independent finite checks
covered 4,464 ghost-shape cases and 20,480 displacement cases; these supplement
the Lean gate and do not replace it. The gate certifies the formal statements
under the repository's definitions and audited assumptions, not empirical
cosmological validity or an external assessment of novelty.

The work uses the repository's native world cells, shifts, coefficient
lattices, depth boundaries, coherent towers and innovation/current laws.
The new results extend shared structures; they do not replace unrelated
statements or count renamed theorems as strengthenings.

## Exact operator presentation

`GSTExactWorldOperatorPresentation` upgrades the previous kernel inclusion to
an equality for every rectangle, including empty rectangles:

```
ker(evalWorldPoly A B) = truncIdeal A B
WorldCohomologyRing A B ≃+* WorldOperatorRing A B
```

The central certificate is `origin_coefficient`: applying any polynomial
operator to the native origin delta extracts its coefficient at every live
world cell. It proves faithfulness without assuming the desired kernel
identity. Surjectivity follows from generation of the native operator ring.

For positive depths, the merged exact path calculus additionally proves the
optimal lifetime, not just an upper bound:

```
L A B ^ n = 0 ↔ A+B-1 ≤ n
```

The surviving top power is certified by its nonzero origin-to-top binomial
coefficient.

## Arbitrary axis families

`GSTMultiAxisCosmology` replaces a pair of axes by a type `I` with depth
function `d : I → Nat`. Cells are dependent functions `∀ i, Fin (d i)`.
Simultaneous displacement composes additively, all displacements commute,
and crossing any one boundary extinguishes the transport. These laws do
not require `I` to be finite.

For finite `I`, bounded displacements send the origin delta to all distinct
cell deltas. `synthesis_injective` rules out every linear relation among
these native operators. `commuting_operator_ext` says that an operator
commuting with all native transports is completely determined by its
response at the origin. `commutantEquiv` goes further: every such operator is
exactly the mixed-shift synthesis of its origin response, giving a complete
classification of the displacement commutant. Complementary-coordinate probing gives an integral
nondegenerate pairing in every finite dimension.

`GSTMultiAxisCohomology` constructs the corresponding quotient for arbitrary
`I`. `quotient_eq_iff_coeff` is an exact equality criterion: two polynomials
represent the same class iff every coefficient strictly within all depth
boundaries agrees. It also proves a universal property with a unique
representation for every commuting ring-valued axis family obeying the
depths. For finite `I` and positive depths, arbitrary weighted polarization
has exponent bound `1 + Σ_i (d_i - 1)`. Rectangle recovery and direct
nilpotence of the previous `L` inside its quotient are explicit theorems.

The coefficient criterion concerns the abstract arbitrary-axis quotient.
The exact native ring isomorphism is proved separately for the existing
rectangular operator representation; these are distinct certificates.

## Weighted sectors and general dynamics

`GSTMultiAxisGradedDynamics` permits every nonnegative axis weight. It
proves complete orthogonal sector decomposition, exact displacement degree
transport and complementary degree reflection. More generally, any integer
linear operator `T` raising this grading by `r` satisfies:

```
T^n = 0 whenever topDegree < n*r.
```

Thus extinction applies to all operators satisfying the native degree law,
not only the earlier specific sum of digit and carry shifts.

## Coherent infinite reconstruction

`GSTInfiniteWorldRenormalization` proves explicit inverse constructions:

```
WindowTower ≃ (Fin k → Fin 3) × WindowTower
{Y // Y.level k = X.level k} ≃ WindowTower
Nat.card {X // tail k X = Y} = 3^k
```

Dropping innovation layers composes by addition. Every finite current
observation cylinder still contains a full coherent universe, and no
countable list exhausts even one such cylinder. These results follow from
the existing GST innovation classification and finite-current completeness.

## Family coverage

| Existing family | Strengthening |
|---|---|
| Rectangular quotient action | Exact kernel and operator ring equivalence |
| Digit/carry commutation | Arbitrary simultaneous axis displacements |
| Rectangular boundary extinction | Any-axis boundary extinction |
| Bounded monomial action | Unique mixed-shift synthesis |
| Individual operator identities | Exact synthesis classification of the full commutant |
| Two-axis truncation ring | Arbitrary-axis quotient with exact coefficient equality |
| Canonical representation | Unique representation into every suitable commutative ring |
| Lefschetz action nilpotence | Quotient nilpotence and arbitrary weighted polarization |
| Total-degree sectors | Arbitrary nonnegative axis weights |
| Particular Lefschetz dynamics | Every operator raising the selected grading |
| Rectangular complementary pairing | Integral nondegeneracy in any finite dimension |
| Infinite stream classification | Exact prefix/future product decomposition |
| Finite observation completeness | Full-universe structure inside each observation cylinder |
| Information lost under descent | Exact `3^k` renormalization fiber cardinality |

## Verification

The base's dedicated cosmology gate failed on compilation. Repairs address
coefficient/operator type transparency, induction order, a list fold,
sector simplifications, reserved identifier parsing, incorrect use of
injectivity, missing parentheses and dead tactics. No hypothesis is added
to rescue a failed conclusion.

The branch gate checks the frozen commit, builds the strengthened modules,
and audits transitive axioms. `GSTCosmologyStrengtheningAudit.lean` lists the
public declarations individually. Permitted dependencies are only
`propext`, `Classical.choice` and `Quot.sound`.

Initial verified Lean source commit: `51be1fd14b64bdad6351d2461534fa4af4ba7037`.
[Successful verification run](https://github.com/kyo-oo/HC-PROOF/actions/runs/35706311719)
completed on 2026-09-22.

- All upgraded cosmology build targets passed.
- The proof-escape check and `sorryAx` check passed.
- All 85 public declarations across the five new modules were audited:
  83 reported permitted axioms and two required no axioms.
- The full `lake build HCProof` integration passed.
- The new modules contain 59 public theorems plus three private proof lemmas.

This document records the verified theorem-family upgrade. It does not claim
that all 2,044 existing declarations have individually been replaced.
General rational strong Lefschetz and comparisons with Millennium Problems
are not asserted here.
