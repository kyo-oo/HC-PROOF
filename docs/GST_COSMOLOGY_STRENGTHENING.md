# GST cosmology strengthening

Base: `c833d9bd23d376eeb14246b675572f2cb8c66e51`.

## Official Hodge target: reconstruction and its geometric obligation

The Hodge-front continuation starts from
`84a951bfaf5213cd2c4377b0fb916b6ef6f30087`. Its run 108 failed because
`cosmology_coordinate_reconstruct` eliminated a sum of whole coordinate
functions before reducing evaluation at the selected coordinate. The repaired
proof first distributes evaluation and scalar multiplication through the sum.

The strengthened Stage 2G now proves:

- `cosmologyCycleLift`: a rational-linear cycle lift from a supplied cosmology
  realization of the Hodge sector.
- `cosmologyCycleLift_section`: composition with the supplied cycle-class map
  is the inclusion of that Hodge sector.
- `cosmology_cycle_fiber_exact`: all cycle representatives are the constructed
  representative plus an element of the cycle-class kernel.
- `cosmology_chart_realization_iff`: for a fixed coordinate chart, existence
  of the required basis-cycle realization is **equivalent** to the whole Hodge
  sector lying in the cycle-class image.
- `zero_cycleClass_hodge_iff`: a zero cycle-class map realizes precisely a
  zero Hodge sector. An unconstrained linear map field cannot establish
  algebraicity from coordinate reconstruction alone.

The last two results audit the scope of the reconstruction argument. They are
not counterexamples to the official Hodge conjecture. They show why an
arbitrary supplied semantic package cannot be treated as the canonical
geometric package, and why selecting a pure-coordinate chart does not prove
that its basis classes are algebraic.

### What is still required for the official conclusion

`SmoothProjectiveComplexScheme` specifies actual smooth projective complex
schemes, and `codimensionCycles` uses native scheme cycles. The cohomology
construction computes singular cohomology of the supplied topological space.
However, the repository still supplies these pieces as input:

1. `AnalytificationData.space`, together with only a point-set equivalence;
   the genuine analytic topology is not constructed or characterized by that
   equivalence alone.
2. `HodgeBigradedBettiData.hodgeBigrading`, which gives independent spanning
   complex subspaces, but not their identification with the analytic Hodge
   decomposition.
3. `HodgeBigradedBettiData.cycleClass`, an arbitrary rational-linear map of
   the correct type, not a construction of the geometric cycle-class map.
4. `CosmologyHodgeRealization.basisCycle_class`, which must be proved for
   actual algebraic cycles after the above identifications.

Thus the current GST theorems establish a verified reconstruction mechanism
and an exact reduction. They do **not** yet prove the official Hodge
conjecture. Infinite-axis reconstruction, purity classification, and transport
extinction do not by themselves construct the missing geometric identifications
or algebraic-cycle representatives. These fields remain visible in theorem
signatures; none has been promoted to an axiom or silently instantiated with
the desired conclusion.

Verification: proof and audit commit
`73891d76d35c6707d684966984027a72ab451ab1`,
[run 110](https://github.com/kyo-oo/HC-PROOF/actions/runs/35931094769).
The cosmology build, source proof-escape check, `sorryAx` rejection, public
axiom audit, and full `HCProof` integration all passed. Stage 2G is now
included explicitly in the cosmology build and all 26 of its public definitions
and theorems are included in the transitive axiom audit. Only `propext`,
`Classical.choice`, and `Quot.sound` are permitted by that audit. This receipt
verifies the conditional reconstruction and scope theorems above; it is not
an official Hodge-conjecture proof certificate.

## Cohomology continuation from run 103

This continuation preserves Sol's work through
`7e02441b94c0f129580480e2f41356dbeeebd03f` and edits eight existing mathematical
modules. It adds no replacement module or alternate proof route.

### Repair and strengthened statements

Run 103 stopped at two coefficient reductions in the canonical normal form.
The polynomial coefficient accessor and the underlying finite-support accessor
were being conflated. Both sides are now reduced explicitly to
`AddMonoidAlgebra.coeff` before filtering. The stored coefficients and the
mathematical definitions are unchanged.

| Existing module | Strengthened content |
|---|---|
| `GSTMultiAxisCohomology` | Exact bounded faithfulness; positive-depth assumptions removed from finite and weighted polarization; canonical addition/product laws; composition of depth restrictions; surjective restriction with exact fibers; reconstruction from any cofinal uniform-depth schedule, even with infinitely many axes |
| `GSTTruncatedWorldCohomologyRing` | Mixed transport annihilates every world **iff** it crosses a boundary; the reverse direction is witnessed by an explicit live cell |
| `GSTExactWorldOperatorPresentation` | Exact lifetime includes empty rectangles and the zeroth power, without positivity assumptions |
| `GSTGlobalPureHodgeCosmology` | Every world has a unique decomposition into a pure diagonal part and a part with zero diagonal coordinates |
| `waves/GSTWaveCohomology` | Prefix observations through depth K recover exactly the first K local matter classes |
| `waves/GSTWaveCohomologyV2` | Exact finite reconstruction in every translated horizontal window |
| `waves/GSTNCohomology` | Finite prefix reconstruction; one endpoint digit plus Wave-II amplitudes recovers the whole digit window; injective isolated channel readouts |
| `waves/GSTNCohomologyV2` | Isolated canonical channels are injective at positive depth; a single difference-amplitude probe separates two given mode fields exactly |

Nine existing theorem interfaces are strengthened directly. Additional
statements provide the composition, reconstruction and uniqueness laws needed
to use these interfaces together. No unchanged theorem is counted as a new
strengthening merely because an audit entry was added.

### Interpretation

Canonical normalization retains exactly the live coefficients. Multiplying
normalized representatives and normalizing again gives precisely the normal
form of their product: discarded boundary terms cannot return. Two successive
normalizations intersect their depth profiles, while restriction maps compose
through any nested chain of worlds. Every shallower class lifts, and the
coefficients in its live box describe its entire restriction fiber.

For infinitely many axes, each monomial still has finite exponent support.
Consequently any cofinal schedule of uniform depths eventually exposes each
coefficient. Equality at those scheduled observations therefore determines the
complete polynomial; this is not a claim that every infinite compatible family
comes from a finite polynomial.

The old channel family in `ncoho_rank` repeated the same object at every index.
It established diagonal readout availability but did not establish distinct
classes. The revised construction isolates each hole, proves the other
coordinates empty, and uses nonempty windows to prove injectivity. The native
readout type is a family of lists with an integer coordinate; these theorems
do not assert a module rank for that unrestricted list type. At depth zero,
canonical windows are empty and distinctness is not claimed.

The interference probe uses the difference of two given fields as its
amplitude. The response difference is the sum of squared local differences,
so cancellation cannot hide a mismatch. This is an exact comparison theorem
for given fields, not an assertion that one fixed probe reconstructs every
unknown field.

### Verification

Verified proof-source commit: `9ff97bf3fb9c7335412a8ca20b0a3e71d99da4de`.
[Cosmology upgrade run 107](https://github.com/kyo-oo/HC-PROOF/actions/runs/35869033096)
passed upgraded cosmology compilation, source proof-escape rejection,
absence of `sorryAx`, the public declaration axiom audit, and full `HCProof`
integration. The public audit emitted 298 nonempty axiom receipts.
The audit permits only `propext`, `Classical.choice`, and
`Quot.sound`; no custom axiom is admitted by that gate.

Independent finite checks passed for 1,428 normal-form composition/product
cases, including empty axis sets and zero depths, and 15,625 signed field
pairs for the difference probe. The existing coherent-cosmology check also
passed: 12 cell signatures, 1,092 finite signatures, and 25,515 realization
and edge checks. These finite checks supplement Lean verification.

The accumulated inventory now contains 120 files and 225 named declarations.
All inventory declarations have explicit entries in the transitive axiom
audit. These totals include earlier work and are not a percentage of completion
or a count of new discoveries in this continuation.

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
