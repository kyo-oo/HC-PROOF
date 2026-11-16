# 2026-11-15 — The twelve-point CI loop: six runs, one root cause, the systemic kill

**Provenance:** W4-B, the records-keeper wave of the GST campaign's CI-loop session.  This
is the round record for the six-run repair loop on the twelve-point native geometric world
(repair waves 4–8 of the 2026-11-15 session; agent waves W1–W4), written at HEAD `e3693d8`
with the loop's closing CI run 43778820813 in progress.  The construction under repair is
the 2026-11-14 world of `2026-11-14-gst-twelve-point-native-geometric-world.md` (V₀ =
Spec(ℂ¹²), the 26-letter fold word, the live rank-12 discharge); this round changed ZERO
mathematics — every commit in the loop is an elaboration-engineering repair to
`GSTTwelvePointWorldCarrier.lean` (and, in wave 5, to the landing file).  Every lemma name
and line number cited below is the pinned Mathlib's (`mathlib4` @
`51e6992efd06126df61a496bebf8f49482a4e129`).  No Lean kernel verdict is claimed for the
loop's closing run at this record's write time.

## What this is

The twelve-point lane (`.github/workflows/gst-twelve-point-native-world.yml`, registered by
the 2026-11-14 record) had been red since the six modules first landed: the session opened
at run#4 (the wave-3-state baseline, its log the carrier's chart/Lagrange/over_base error
set), and the session then logged six runs in total — runs #4–#8 on the twelve-point lane
plus the landing lane's green interlude.  The loop's shape is the point of this record:
**error counts went 5 → 12 → 9 → (pending)** — non-monotonic by construction, because
each repair wave that fixed an elaboration seam unmasked the cascades hiding behind it —
until the eighth wave stopped patching symptoms and killed the loop's single dominant
root cause; run 43778820813 owns that kill's verdict.

The loop's runs, in order:

| # | wave / SHA (UTC) | lane | verdict |
|---|---|---|---|
| 1 | run#4 — wave-3 state (baseline) | twelve-point | RED (the error set wave 4 addressed) |
| 2 | wave 4 — `ddce112` 19:06 | twelve-point | RED — 5 errors |
| 3 | wave 5 — `2378003` 19:08 | landing | **GREEN — run 43750693353** |
| 4 | wave 6 — `dfa1488` 21:39 | twelve-point | RED — 12 errors (cascade unmasking) |
| 5 | wave 7 — `fa20777` 22:11 | twelve-point | RED — 9 errors (run 43767848609) |
| 6 | wave 8 — `e3693d8` ~23:50 | twelve-point | **verdict pending — run 43778820813** |

## The loop, wave by wave

**Wave 4 (`ddce112`, 19:06Z) — the carrier, first contact.**  `chartRingMap` gets the
intermediate-ring type ascription (unsticks the map's source), the fraction decomposition
moves to generic `j` before the two-chart dispatch (kills the embedded-literal instance
mismatch), the Lagrange degree bridge rewrites in the correct direction, the chart
cancellation uses the `.inv` form with the pinned argument order, `over_base` drops the
regrouping in its new staged form, the coheight `rw` self-closes.  → **run#5 RED, 5
errors.**

**Wave 5 (`2378003`, 19:08Z) — the landing file.**  `mem_bot` takes the ring explicit,
`mem_top` needs no element argument (both pinned-Mathlib signature facts), the `certFold`
orbit-class equality restated in the goal's field-projection shape, a dead `le_rfl`
dropped.  → **the landing lane GREEN: run 43750693353** — `GSTNativeSingleFoldOrbitLawLanding.lean`
kernel-checked at `2378003` (the session's only landed green; the cheap-class discharge,
the no-free-lunch boundary, and the native⇒typed bridge of the 2026-11-14 records are
now kernel facts, independent of the twelve-point lane's fate).

**Wave 6 (`dfa1488`, 21:39Z) — the spine rewrite.**  Five kills: `chartRingMap` rides
Mathlib's goal-driven `refine` spine (kills the stuck away-localization instance search),
`chartRingMap_apply` exposes the composite by a definitional `rfl` and closes by `map_eq`,
the fraction destructure splits the `Subtype` before the power subst (kills the
non-substitutable coercion) with both chart tails rebuilt on `Subtype.coe_mk`
normalization and correct merge directions, the iso-peeling chain rides the `.mpr`
direction of the cancel lemmas (definitional factor matches instead of syntactic),
`over_base` bridges the degree-zero algebra map through `IsScalarTower` with the
definitional route first.  → **run#6 RED, 12 errors — the cascade unmasking:** the spine
repair made elaboration honest, and every seam the stuck spine had been hiding surfaced
at once.  An error count that rises from 5 to 12 in a repair loop is progress, not
regression.

**Wave 7 (`fa20777`, 22:11Z) — twelve claimed kills.**  The side-condition `rw`
self-closes (dead `simp` dropped), the chart `algebraMap` gets its explicit source ring
(unsticks the `refine`), the composite-exposure `rfl` gains unfold/`simp` fallbacks, the
node-zero branch drops the mismatched `zero_pow` arg and the else-branch rides a
definitional `show` for the `ite`, the `hΓ` transport uses `rfl`-exposed `e1`/`e2` lemmas
with corrected merge order, BOTH chart `refine`s flip `.mp` to `.mpr` (the implicant is
the B-side), the `j = 1` `hΓ` rewrite flips to `← hy'`,
`Scheme.toSpecΓ_preimage_basicOpen` takes its explicit scheme argument, the bare
`cancel_left` peels take `_ _` arguments, the adjunction `show` rewrites `hcomp` directly.
→ **run#7 RED — run 43767848609, 9 errors, all in `GSTTwelvePointWorldCarrier.lean`**
(the five sibling modules clean); the run took **23.9 min with a corpus cache miss**.
Twelve kills claimed, three landed — the remaining nine share a cause no symptom patch
can touch.

**The run#7 error inventory** (line numbers at `fa20777`):

* **E1** `283:61` and **E2** `305:30` — stuck `CommSemiring ?R` metavariables inside
  `Localization.Away (MvPolynomial.X j)`: `MvPolynomial.X`'s implicit `CommSemiring`
  argument never unified, because the away/powers instance search ran against an alias it
  could not see through.
* **E3** `406:31` — `rw` pattern failure plus a Γ-type mismatch in the `hΓ` transport.
* **E4** `413:12` — stuck `CommSemiring S✝` at the `IsLocalization.eq_iff_exists`
  application (the localization-data metavariable).
* **E5** `417:4` — no-goals cascade, downstream of E4's failed `refine`.
* **E6** `498:11` — missing `IsIso (toSpecΓ ∣_ basicOpen)` at the fourth peel of
  `chart_closed`.
* **E7** `500:2` — `cancel_left` type mismatch, the same peel's side condition.
* **E8** `580:8` — `RingHom` codomain mismatch in `over_base`'s STAGE 4 adjunction.
* **E9** `589:4` — `rw` pattern `?f ≫ ?g ≫ ?h` failure, same STAGE.
* Plus **sorryAx contamination in the receipts** of `twelvePoint_closedImmersion`,
  `twelvePoint_over_base`, `twelvePointWorld` — not real sorries: a red declaration
  elaborates as `sorryAx`, and every downstream receipt inherits the taint.  The lane's
  sorryAx hard-fail is therefore expected to lift with the nine errors themselves.

## The root cause

Five of the nine — E1, E2, E4, E6, E7 — share **one root cause: the
`twelvePointScheme` def-alias boundary.**  `rw` pattern matching and instance synthesis
run at `.instances` transparency, where a plain `def` is opaque.  The world's carrier had
been declared `def twelvePointScheme : Scheme := Spec (CommRingCat.of (Fin 12 → ℂ))`, so
every proof step that needed to identify `Γ(twelvePointScheme, ⊤)` with
`Γ(Spec (CommRingCat.of (Fin 12 → ℂ)), ⊤)` — the global-sections ring as Mathlib's
localization and restriction lemmas see it — hit an invisible wall:

* E1/E2: the `Localization.Away`/`Submonoid.powers` instance search around
  `MvPolynomial.X j` could not resolve its `CommSemiring` argument against the aliased
  section ring, so `X`'s implicit coefficient ring stayed a metavariable.
* E4: `IsLocalization.eq_iff_exists`'s `S` (the localization-data instance) met the same
  wall.
* E6/E7: the restriction instance `IsIso (f ∣_ U)` for `IsIso f`
  (`Mathlib/AlgebraicGeometry/Morphisms/Restrict.lean:639`) had to be found for
  `twelvePointScheme.toSpecΓ ∣_ basicOpen`, and synthesis could not see the affine
  structure through the alias.

E5 is the no-goals cascade of E4's failed `refine`; E3 is a localized shape defect in
the `hΓ` transport (the `rw` pattern + Γ-type mismatch at 406:31); E8/E9 are localized
shape defects at `over_base`'s STAGE 4 composite (the `Spec.map`/adjunction regrouping).
So the loop's honest accounting is: **one seam behind five errors, two sites behind the
other four.**
The corpus has precedent — `complexBase` and `ProjectiveGrading` are `abbrev`s for
exactly this reason; the twelve-point carrier had been the exception.

## The systemic kill (wave 8)

**Wave 8 (`e3693d8`, ~23:50Z by the session clock; commit-stamped 00:10 UTC 2026-11-16)** —
one surgical repair per root cause, **+70/−41 lines in `GSTTwelvePointWorldCarrier.lean`
only**, no sibling file touched:

1. **`def` → `abbrev twelvePointScheme`** (now `GSTTwelvePointWorldCarrier.lean:55`) —
   the alias dies: pattern matching and instance synthesis unfold it at `.instances`
   transparency, so the Γ-seam ceases to exist.  This one word kills the root cause
   behind E1/E2/E4/E6/E7.
2. **`chartRingMap` term-mode, fully explicit `R S M P T Q`** (`:280-293`) — the
   pinned `toBasicOpenOfGlobalSections` composite
   (`ProjectiveSpectrum/Basic.lean:369-377`) transcribed verbatim, every type argument
   given so each instance resolves against a concrete ring, and every `MvPolynomial.X j`
   feeding an `Away`/`powers` head carries a coefficient-ring ascription pinning the
   `CommSemiring` to `ℂ` (E1/E2).
3. **`eq_iff_exists` explicit `M` and `S`** (`:431`) — the localization submonoid and
   data instance supplied, no metavariable left to guess (E4, and with it E3/E5).
4. **`chart_closed`'s explicit `haveI` chain before the fourth peel** (`:525-531`) —
   `IsAffine twelvePointScheme` by `inferInstanceAs` through the (now transparent) alias,
   `IsIso twelvePointScheme.toSpecΓ` by `IsAffine.affine` (`AffineScheme.lean:59`), the
   restriction instance by `inferInstance` — the chain supplied explicitly, independent
   of the alias's reducibility (E6/E7).
5. **`over_base`'s STAGE 4 via `CommRingCat.ofHom_comp` + the unit triangle
   `toSpecΓ_SpecMap_ΓSpecIso_inv`** (`:607-613`) with a single `show`-level alias bridge
   (E8/E9): the degree-zero algebra map's composite is regrouped at the `CommRingCat`
   level, the adjunction unit triangle closes it, and one `show` bridges the remaining
   `Scheme.toSpecΓ` identification.

## The verification wave (W3) and the numerics (W1-F)

The kill was verified before push by the W3 seven-agent verification wave:

* **Regression sweep GREEN for all five sibling files** — no site in
  `GSTTwelvePointAnalytification.lean`, `GSTTwelvePointCohomology.lean`,
  `GSTTwelvePointHodgeData.lean`, `GSTTwelvePointFoldWord.lean`,
  `GSTTwelvePointLawLanding.lean` depended on the `def`'s opacity; every reference to
  `twelvePointScheme`, `chartRingMap`, and `over_base` remains well-typed under the
  `abbrev`.
* **Peel trace verified against the pinned Mathlib tree** — every cancel/restriction/
  localization lemma's direction, argument order, and side condition in the wave-8 file
  audited against the pinned source lines it cites.
* **Syntax gate PASS** — the wave-8 file parses clean.

The recon wave's numeric agent (W1-F) re-verified the world's arithmetic, **ALL PASS**:

* `det K = −1149656584000 ≠ 0` — the twelve-point Krylov determinant, by **4 independent
  algorithms** (the exact Wolfram orbit computations, the independent SymPy rebuild,
  the fraction-free Bareiss elimination, and the Z3 re-derivation).
* **577/577 Z3 queries UNSAT** — the full certificate-contradiction batch.
* **26 letters reconstruct Twave** — the fold word's point-pair letters rebuild the
  owner's wave matrix exactly.
* `U` order 5 (`U⁵ = I`), `J² = −I`, `UJ = JU` — the operator algebra intact.
* **144/144 `certRow` fractions** verified; largest-magnitude coefficient
  `1495609060489/114965658400` (row 4, column 5); LCM of all denominators
  `574828292000 = |det|/2` (the adjugate/Cramer consistency law).

## Agent-wave accounting

* **W1 — recon, 7 agents** (A–G): the run#7 log triage, the root-cause isolation (the
  def-alias seam), the pinned-Mathlib API audit, and the W1-F numeric re-verification
  above.
* **W2 — kill design, 7 agents**: the five repairs of wave 8 designed against the root
  cause (the abbrev flip, the term-mode `chartRingMap`, the explicit `eq_iff_exists`
  arguments, the `haveI` instance chain, the `over_base` STAGE 4 rewrite), each checked
  against the pinned tree before writing.
* **W3 — verification, 7 agents**: the regression sweep, the peel trace, the syntax gate
  (above).
* **W4 — records** (this record, W4-B): the round record and the INDEX entry; the
  commander commits after the CI verdict.

## Disclosure

* This round's content is **Lean engineering, not mathematics**: the construction is
  byte-for-byte the 2026-11-14 record's (the world, the fold, the certificate); the
  loop's commits change elaboration shape and declaration transparency only.  The
  mathematical claims and their scope are unchanged and governed by the 2026-11-14
  record's disclosure and non-claims.
* The loop's error-count trajectory (5 → 12 → 9) records cascade unmasking, and the
  wave-7 "twelve claimed kills" landed three — the record states this plainly: symptom
  patches in a transparency-bug loop under-deliver by construction, which is why wave 8
  changed strategy from patching the nine symptoms to killing the one seam.
* The wave-8 verification (W3) is **static** — name resolution, peel-trace audit against
  the pinned source, syntax gate, sibling regression sweep.  No Lean compilation is
  claimed from this sandbox; the kernel verdict belongs to run 43778820813 alone.
* The W1-F numerics are external exact evidence (Wolfram/SymPy/Bareiss/Z3), not Lean
  proofs; the in-Lean certificate remains the Gauss-Jordan inverse table of the 2026-11-14
  record.

## Non-claims (exact scope)

* **No kernel verdict for run 43778820813 at this record's write time** — the run is in
  progress; no green is claimed for the twelve-point lane at any SHA of this session.
  Per AGENTS.md rule 7, no green run is cited until the run exists at the pushed SHA.
* The landing lane's green (run 43750693353 at `2378003`) covers
  `GSTNativeSingleFoldOrbitLawLanding.lean`'s closure only; it does not imply the
  twelve-point lane (a different module closure and a different lane).
* The root-cause analysis is an engineering diagnosis; its proof is the pending run, not
  the static verification.  If run#8 remains red, the residual errors are expected at the
  two non-alias sites (the `hΓ` transport and `over_base`'s composite), not a new seam.
* No new mathematics, no new modules, no registration changes this round: the lane, the
  `GSTTwelvePointNativeWorldUpgrade` lib, and the six-file path filter are the 2026-11-14
  record's, untouched by all five commits of the loop.

## CI status

**Verdict pending — run 43778820813 at `e3693d8`, in progress at this record's write
time.**  The session's only landed green is the landing lane's run 43750693353
(`GSTNativeSingleFoldOrbitLawLanding.lean` at `2378003`).  The twelve-point lane's kernel
verdict at HEAD belongs to GitHub CI; this record will be supplemented by the commander's
commit round once the run lands.
