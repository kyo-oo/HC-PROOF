# WAVE 13 — THE HAMSANDWICH PORT: the sphere-homology machine vendored onto the pin (the X-focused audit's kill wave)

Date: 2026-11-28.  Branch: `research/gpt6-gst-hypothesis-part1-chow-square-20261110`.
Lane: `ham-sandwich-port.yml` (NEW, five ladders).

## §0 The frame (BOSS's order, executed)

The work is X — the GST hypothesis `NativeGSTSingleFoldOrbitLaw`.  Y (the
Hodge conjecture statement) follows from X by the kernel-certified
conditional; no Y-side work.  The X-side ledger after wave 12: the law is
proved unconditionally on the complete constructed domain, and the ONE
remaining problem in X's own ledger is the fence chain's final link —
FENCE-Ω (`∃ ω : singularCohomologyOf (TopCat.of unitSphereType) 2, ω ≠ 0`),
the hypothesis the kernel-certified wave-9 apex package carries (the
independence conjunct of the 8-conjunct master).  Wave 12 reduced the
designated route to FENCE-S (the separator at the fundamental cycle).
Wave 13's audit re-derived the full map and found the fourth door.

## §1 The audit (three recon waves, 11 sub-agents)

**Wave 13-A (the inventory).**  The pinned Mathlib (v4.33.0-rc2,
`51e6992e`) re-surveyed at ground truth — the wave-10D survey was STALE:

- PRESENT (the wave-10D record missed these): topological homotopy
  invariance of singular homology at the CHAIN level
  (`TopCat.Homotopy.singularChainComplexFunctorObjMap`, the prism in
  substance), the normalized-chains machinery with its QuasiIso
  (`SSet.normalizedChainComplex`, `homotopyEquivNormalizedChainComplex`),
  geometric realization with the adjunction (`SSet.toTop`, `sSetTopAdj`),
  `SSet.Boundary`, the `sd`/`ex` subdivision functors (bare), the
  Eilenberg-Steenrod pretheory framework.
- ABSENT (confirmed): chain-level subdivision theorems, simplicial
  approximation, Mayer-Vietoris for singular homology, excision, sphere
  homology, degree theory, no-retraction, Sard.
- The corpus's own sphere arsenal inventoried (12 files, every signature):
  the wave-12 realization machinery is GENERIC — it consumes any
  non-bounding cycle, not just `fundCycle`.
- The algebraic half of FENCE-S verified at the pin in five lines:
  `LinearMap.exists_extend_of_notMem (0) hv 1` (artifact banked at
  `/home/z/recon-13A2/SEPARATING_FUNCTIONAL_13A2.lean`) — from
  `v ∉ W` a ℚ-linear functional vanishing on `W` and reading `1` on `v`.

**The wall, restated exactly.**  `FundSeparator ⟺ fundCycle ∉ im d₃` —
the non-bounding of the radial fundamental cycle, i.e. the classical
H₂(S²;ℚ) ≠ 0 content.  Every hand-roll route dies at the same stone: the
wildness of continuous singular simplices (subdivision, approximation, or
integration each domesticate it; none exist at the pin; each priced
multi-week).  The corpus's own wave-57 council had priced the transfer
wall "multi-month" — with stale pin data.

**Wave 13-B (the war council).**  The community search — the move the
campaign had never made: the machine EXISTS in the wild.

| Source | Content | Base | Verdict |
|---|---|---|---|
| **akopjan/HamSandwich** | `sphereTopHomologyIso_unconditional (n) (1 ≤ n) : H_n(S^n;ℤ) ≅ ℤ` on Mathlib's own `singularChainComplexFunctor` — the COMPLETE last mile: barycentric subdivision (chain map + homotopy + diameter + iteration), small chains + Lebesgue, the MV SES + step iso, the S¹ base + suspension tower | v4.28.0 | **THE PORT** — forward-portable, zero Mathlib overlay |
| joelriou/excision | subdivision + small simplices + excision (no spheres, MV WIP) | ~v4.36 | the quality fallback; stops 95% short |
| TauCetiProject/TauCeti | everything incl. H̃ₙ(Sⁿ) = R | ~v4.37 | statement-donor only; cone 3.7× bigger |

**Wave 13-C (the port recon, two agents, independent convergence).**  The
HamSandwich cone: 65 files, ~12.2k lines, zero sorry/axiom, CI
axiom-audited upstream (their CI greps `#print axioms` for `sorryAx`;
`sphereTopHomologyIso_unconditional` is itself an audit target).  The
drift inventory (all 326 identifiers checked against the pin): **ONE hard
rename** (`Finset.sum_eq_sum_diff_singleton_add` →
`Finset.sum_eq_sum_sdiff_singleton_add`, the 2026-06-03 sdiff migration),
one deprecation (`SSet.singularChainComplexFunctor`, warning-only),
one false alarm (`HomologicalComplex.homologyFunctor_map` — the
`@[simps]`-generated lemma exists at the pin; source-grep invisible).
The carrier: `Sphere 2 = ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)`
— the corpus's `unitSphereType` VERBATIM.  The ring: the machine is
`[CommRing R]`-generic; the sphere layer is ℤ-instantiated in a thin,
re-instantiable skin.

## §2 The decisive architectural fact (why the port kills the fence)

The fence consumption (`GSTFiniteLineFenceDischarge`) needs ONLY
`∃ ω : H²(S²;ℚ), ω ≠ 0`.  The wave-12 realization machinery replays for
ANY non-bounding cycle:

1. The port supplies `H₂(S²;ℤ) ≅ ℤ` (this round's ladders) and, at the
   next strike round, the ℚ-instantiated endpoint — H₂(S²;ℚ) ≅ ℚ.
2. From `Nontrivial H₂(S²;ℚ)`: a homology class x ≠ 0, a representing
   cycle z ∈ ker d₂ with z ∉ im d₃ (else x = 0).
3. The banked five-line extension lemma at `z ∉ im d₃`:
   φ : C₂ →ₗ[ℚ] ℚ vanishing on im d₃ with φ z = 1.
4. The wave-12 replay: φ is a cocycle of the dual complex (the
   boundary-vanishing IS the cocycle law, `cochains_d_two_three` /
   `dual_eval_two_three`), its class through `moduleCatHomologyIso` is
   nonzero (a coboundary reads ψ(d₂ z) = ψ(0) = 0 ≠ 1 on z) —
   `∃ ω ≠ 0`.
5. The kernel-certified exists-flip master closes the wave-9 package's
   independence conjunct — the last subcase of the X-audit.

FENCE-S (the fundCycle-specific separator) is NOT consumed by anything
downstream; the fence falls without it.  Its status after the port: a
well-posed question (fundCycle's class against the tower generator —
classically ±1, the generator identification), recorded as such.

## §3 The wave-13 execution (this round's landed work)

- **The vendor**: `HamSandwich/` — the 65-file cone at upstream `76202db`
  (Apache-2.0, license preserved as `LICENSE.HamSandwich`), module paths
  preserved so intra-cone references compile unchanged.  Import closure
  machine-verified: 65 internal imports, zero gaps.  The ONE drift fix
  applied (the sdiff rename at `BarycentricSubdivisionDiameter.lean:110`).
  Provenance + port notes: `HamSandwich/VENDOR_NOTES.md`.
- **The audit file**: `HamSandwich/H2SphereAudit.lean` —
  `#print axioms SphereOddDegree.sphereTopHomologyIso_unconditional`
  (the expected three: propext, Classical.choice, Quot.sound).
- **The wiring**: `HamSandwichLib` in `lakefile.toml` (globs
  `HamSandwich.+`); the NEW lane `.github/workflows/ham-sandwich-port.yml`
  — five ladders: (1) the subdivision machine (`BarycentricSubdivisionIter`
  + `Diameter`), (2) the small-chains quasi-iso (`SmallChainsQuasiIso`),
  (3) Mayer-Vietoris (`MayerVietoris`), (4) the sphere tower
  (`SphereOrientationPosFromMV`) + the sorryAx audit, (5) the axiom audit
  (`H2SphereAudit`), the fence-lane's cache/toolchain discipline
  throughout.

## §4 The strike plan (the campaign's wave discipline)

The vendored 12.2k lines face: the tactic-drift tail (`grind`/`simp
+decide` brittleness across five months of simp-set drift — the recon's
designated watchpoints: `SubChainSubspaceBridge`, `BarycentricSubdivisionIter`,
`BarycentricSubdivisionDiameter`), the `rfl`-cast anchors (the
`AlternatingFaceMapComplex` identification — the recon verified the
definitional structure is unchanged at the pin), and the elaboration load.
Expected shape: a multi-strike cascade exactly like waves 9F-I/10/11/12,
each strike diagnosed from the CI artifact (the lane uploads the log).
The ℚ endpoint (the thin-layer re-instantiation of the sphere files) and
the corpus-side composition file (the wave-12 replay at the port's
nonvanishing — §2 steps 2-4) are the designated follow-up strikes,
authored against this round's frozen interface.

## §5 The honesty ledger (the two-status law)

NOTHING in the vendored tree is a claim of the corpus until its lane runs
green at the pushed SHA — KERNEL-CERTIFIED or NOT A CLAIM OF THE CORPUS;
status is spoken by Lean alone.  The upstream receipts (their CI green at
`76202db`, axiom-audited) are PROVENANCE evidence, not kernel receipts on
THIS pin — the port's kernel verdict is the five ladders above.  The
wave-12 theorem (`exists_nonzero_sphere_cohomology_two_of_fundseparator`,
run 46093265298) remains green and standing; the port route is COMPLEMENTARY
(FENCE-Ω direct), not a replacement of the FENCE-S design.

## §6 The receipts

- Upstream: github.com/akopjan/HamSandwich @ `76202db`, Apache-2.0, CI
  green, zero sorry, axiom audit targets
  `SphereOddDegree.sphereTopHomologyIso_unconditional`.
- The pin dossier: Mathlib `51e6992efd06126df61a496bebf8f49482a4e129`
  (v4.33.0-rc2); the 326-identifier drift scan; the sdiff-migration fix
  verified at `Mathlib/Algebra/BigOperators/Group/Finset/Piecewise.lean`
  (`sum_eq_sum_sdiff_singleton_add`, the `to_additive` image of
  `prod_eq_prod_sdiff_singleton_mul`).
- The closure check: 66 files (65 + the audit), 65 internal imports, zero
  missing; the lakefile + lane wired per the corpus conventions.
- The port-recon war council: agents 13-C1/13-C2 (independent convergence
  on the route); the recon artifacts: `/tmp/ham` (the upstream clone),
  `/tmp/ml4` (the pinned Mathlib oracle), `/home/z/recon-13A2/` (the
  extension-lemma artifact).
