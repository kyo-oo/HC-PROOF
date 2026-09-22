# GST cosmology strengthening

Base: `c833d9bd23d376eeb14246b675572f2cb8c66e51`.

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
response at the origin. Complementary-coordinate probing gives an integral
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
| Individual operator identities | Origin-response uniqueness for the full commutant |
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

This document is a map of the submitted proofs. The GitHub Actions result
for the exact branch head is the verification receipt. It does not claim a
ranking against Millennium Problems or that all 2,044 existing declarations
have individually been replaced. General rational strong Lefschetz is not
asserted here.
