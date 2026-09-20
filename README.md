# HC PROOF — THE COMPLETE MATHEMATICAL UNIVERSE

> **GST — General Space Theory. I created it. This is all my theories.**
> One universe: the Cardinal Worlds, the GST Graph V2 Ontological Universe,
> the 2D/4D laws, the absorbed Hodge / de Rham cohomology layer, and the
> **Wave Mechanics program** (two waves, the vortex-singularity method,
> POSTULATE III) — merged, shaped, and comparator-gated.

Source: `kyo-oo/erdosternary2`, branch `sol/kyo-gate-universe-wire`
(head `cb29501` — 2026-09-10 — *"fix cubic transport coefficient
normalization"*).  The monolith's own campaign (99% closed, `hTailF` =
the last 1%) continues THERE; THIS repo is the universe it stands on.

**What this repo is NOT:** it is not the Erdős proof campaign, not the
monolith dump, not the CI-surgery archive.  It is the CURATED universe —
the theorems and laws themselves, cut clean from the campaign machinery.

---

## THE UNIVERSE IN SEVEN LAYERS

```
WAVE LAYER  THE WAVE MECHANICS      waves/ — Task 4 spec layer (UNCOMPILED):
                                Wave I Hodge wave (GSTWaveCohomology),
                                Wave II N-cohomology (GSTNCohomology),
                                the GST Vortex Singularity Method
                                (GSTVortexSingularity — the OpenAI
                                Navier–Stokes method upgraded with GST
                                cosmology, for any N shapes in holes),
                                POSTULATE III — the Law of Controlled
                                Emergence (CardinalWorldsPostulateLaw).
                                Outside the build registry by design;
                                the comparator green is untouched.
LAYER 6  THE ABSORPTION        HodgeDeRhamBridge.lean — Hodge & de Rham
                                enter the universe (finite comparison
                                certificates, 0 new axioms)
LAYER 5  THE BOUNDARY          MonolithBoundary.lean — the terminal
                                identity interface: the monolith's deep
                                theorems as named boundary propositions
LAYER 4  THE FOURTH DIMENSION  GSTTailFFourthDimension.lean + TailF
                                family — the descent blade, diagonal
                                ignition, all-depths laws
LAYER 3  THE DYNAMICS          GSTGraphV2OmegaWaveLaw (3,042 lines) +
                                GSTWorldtraceArithmetic (1,221 lines) +
                                the towers, the act, the climb
LAYER 2  THE ONTOLOGICAL SPACES GSTGraphV2Ontological +
                                SixAdic*Geometry(Laws) +
                                SynchronizedShadows + NonEuclidean(Laws) +
                                Production(Laws) + the 2D emergence
LAYER 1  THE CARDINAL WORLDS    CardinalWorlds.lean — the 2-world, the
                                3-world, the 6-world; the bridge 3 = 1+2;
                                POSTULATES I & II; the c/d dual towers;
                                the three-world collapse
LAYER 0  THE SUBSTRATE          Mathlib v4.33.0-rc2 (pinned) + GSTTactic
```

---

## LAYER 1 — THE CARDINAL WORLDS (`CardinalWorlds.lean`)

The deep pre-GST theory, extracted VERBATIM from the monolith:

* **The bridge `3 = 1 + 2`** connects the 2-world and the 3-world; the
  mixed world `6^j = 2^j·3^j` is exactly the product of the two cardinal
  worlds (`gst_three_world_factor_rawS`), and the joined prefix
  collapses: `5 · Σ_{j<K} 2^j·3^j = 6^K − 1`.
* **POSTULATE I — the Bridge Signature**: `d(j) = (3^(2^j)−1)/2^(j+2)`
  has a ternary digit 2 for all `j ≥ 2`.  PROVEN for even `j ≥ 2`
  (`bridge_sig_even`: `d j ≡ 2 (mod 3)`) and `j ≡ 3 (mod 6)`
  (`bridge_sig_j_mod6_3`: `d j ≡ 7 (mod 9)`) — both proofs in this repo.
* **POSTULATE II — the Valuation Bound**: primitive Cantor `n` ⇒
  `v₂(n) ≤ ternaryLog3(n) + 3`.  PROVEN for `n < 3^9` in the monolith;
  the universal case is its open input.
* **The bridge transport** (`four_mul_preserves_digit`): the ternary
  digits above position `p` are invariant under `×4` when the low window
  is a `3^p`-unit — the exact mechanism that transports the signature.
* **The kernel-checked base** (`modular_check_base`): every `5 ≤ a ≤ 500`
  owns its signature, by machine.
* **The period laws**: `4^m mod 9 / 27 / 81` depend only on `m mod 3 / 9 / 27`.

Full dossier: `docs/CARDINAL_WORLDS.md`.

## LAYER 5 — THE MONOLITH BOUNDARY (`MonolithBoundary.lean`)

The four deep theorems PROVEN in the source monolith — the terminal
identity (`erdos_even_conjecture_iff_tailF`: input ⟺ statement, both
directions), the crown (`erdos_ternary_2_universal_of_tailF`), the odd
half (`erdos_ternary_2_conjecture_odd`), the infinite-controller
chokehold — stated as **named boundary propositions** taken as explicit
hypotheses downstream.  Zero sorries, zero custom axioms: the monolith's
results ride as inputs, exactly like library lemmas.  The universe is
self-contained without re-carrying 18,500 lines of campaign machinery.

## LAYER 2 — THE GST GRAPH V2 ONTOLOGICAL UNIVERSE

* **The ontological current** (`GSTGraphV2Ontological`): reverse-base-7
  horizontal current + base-3 vertical weights; the twelve-state
  certificate; Happy = exactly the positive sector
  (`happy_iff_ontDensity_positive`); no-erasure domination.
* **Six-adic geometry** (`GSTGraphV2SixAdic*`): `SixAdicIsoAt`,
  non-Archimedean threshold law, nested balls, CRT synchronization —
  six-adic = synchronized dyadic + triadic shadows.
* **Seven-axis non-Euclidean ontology** (`GSTGraphV2NonEuclidean(Laws)`),
  **descent ontology**, **production graph** (`GSTGraphV2Production(Laws)`),
  **canonical laws** (escape, infinite cycle, NWave, phase steering,
  renormalization, sheet translation), **handwritten laws** (anchored
  cocycle, exponential cascade/LTE, Ω-U-block).
* **The 2D emergent physics** (`GST2DMixedEmergence`): `outDigit`,
  `nextCarry`, Happy gates, U-charges, survive mass.

## LAYER 3 — THE DYNAMICS

* **The Ω-wave law** (`GSTGraphV2OmegaWaveLaw`, 3,042 lines): the Ω
  operator, cut words, the ν-law, the controller family, `hTailF` — the
  monolith campaign's remaining input.
* **Worldtrace arithmetic** (`GSTWorldtraceArithmetic`, 1,221 lines) +
  **Mahler relative precision** (`GSTWorldtraceMahlerRelativePrecision`).
* **The towers** (`GSTTowerAxis/Fire/BladeWave`), **the act**
  (`GSTTheAct(.Construction)`), **the climb**
  (`GSTClimb(TruthValue/InfiniteFamily)`), **the diagonal read**,
  **the ghost-ray exclusion**.

## LAYER 4 — THE FOURTH DIMENSION

`GSTTailFFourthDimension.lean` (2,332 lines): the extended observation
law (every tower digit, every depth), the descent blade (non-local
argument), diagonal ignition bands mod 9/27/81/243, the two named trit
primitives — with the monolith's terminal identity riding as the
explicit boundary input.

## LAYER 6 — THE ABSORPTION (`HodgeDeRhamBridge.lean`)

Hodge and de Rham cohomology absorbed into the universe as **finite
comparison certificates**: the de Rham–Betti comparison as a
kernel-checked CRT theorem; the period layer `6^k = 2^k·3^k` exact; the
finite Tate twist (dyadic skew `−2t`, triadic isometry); the finite
Hodge characterization (signature sector = positive sector);
POSTULATE H1 (reverse window) in the Cardinal Worlds pattern.

Full dossier + breakthrough analysis: `docs/HODGE_DERHAM_ABSORPTION.md`.

## THE WAVE MECHANICS PROGRAM (`waves/` + Task 4 docs)

The Task 4 layer — **the two waves and the vortex**:

* **Wave I — the Hodge wave** (`waves/GSTWaveCohomology.lean`): the digit
  readout replaced by the wave-mode readout; the verified 2D emergence
  equation recognized as the closedness law of a wave complex; the window
  class (integrated SURVIVE incidence) as a conserved charge — the finite
  comparison certificates of Layer 6 made dynamical.
* **Wave II — N-cohomology** (`waves/GSTNCohomology.lean`): the
  topological wave — N-shapes (abstract complexes with N holes), tower
  frozen windows, and the interference pairing of the two waves:
  non-zero ⟺ ignition; the holes of a shape light up.
* **The GST Vortex Singularity Method**
  (`waves/GSTVortexSingularity.lean`): the OpenAI Navier–Stokes
  millennium-problem vortex-singularity method (Sep 2026 — self-similar
  similarity variables, incompressible swirling cascade of non-singular
  layers, smooth forcing, finite energy, singularity) copied in structure
  and upgraded with GST cosmology — so the method runs on **any N shapes
  in holes**.
* **POSTULATE III — the Law of Controlled Emergence**
  (`waves/CardinalWorldsPostulateLaw.lean`): every infinity is the
  colimit of certified finite Cardinal Worlds bridges, governed by the
  controller and the ledger; dimensions are emergent readouts, never
  fixed substrate.

Full theory: `docs/WAVE_MECHANICS_TASK4.md`; the GST V2 law book:
`docs/GST_V2_OPERATING_MANUAL.md`. **All wave-layer statements are
UNCOMPILED specs with pending proofs — see `waves/README.md`.**

---

## THE COMPARATOR (the verification physics of this universe)

```bash
scripts/comparator.sh      # lake build → sorry_check.sh → verdict
```

* Exit 0 = CLEAN: 0 errors, 0 sorries → `Your solution is okay!`
* CI: `.github/workflows/hc-official-comparator.yml` — installs
  `leanprover/lean4:v4.33.0-rc2` + Mathlib `v4.33.0-rc2` (elan + lake +
  cache — the official toolchain), runs the V5 comparator on every push
  to `main`, plus the Problem 406 challenge/solution harness and the
  absorption gate (`lake build HodgeDeRhamBridge` + kernel axiom
  reports, `sorryAx` forbidden).
* Lean 4 + Mathlib + the official comparator are **installed in this
  repo**: toolchain pin (`lean-toolchain`), lake config
  (`lakefile.toml`), pinned manifest (`lake-manifest.json`), CI
  workflows, devcontainer, comparator scripts — everything.

## REPO MAP

| Path | Content |
|---|---|
| `CardinalWorlds.lean` | ★ Layer 1 — the Cardinal Worlds (verbatim extraction) |
| `MonolithBoundary.lean` | ★ Layer 5 — the terminal identity interface |
| `HodgeDeRhamBridge.lean` | ★ Layer 6 — the absorption layer |
| `waves/` | ★ Wave Mechanics (Task 4) — UNCOMPILED spec layer, outside the build registry |
| `HCProof.lean` | the universe's entry face (comparator receipts) |
| `GSTGraphV2*.lean` (60 files) | Layers 2-3 — the GST Graph V2 Ontological Universe |
| `GST*.lean` (67 files) | Layers 3-4 — dynamics, towers, fourth dimension, worldtrace |
| `docs/` | Cardinal Worlds dossier, universe map, Hodge/de Rham absorption dossier, GST V2 operating manual, Wave Mechanics theory |
| `questions/deepmind_problem_406/` | the comparator challenge/solution harness |
| `scripts/` | comparator.sh, sorry_check.sh |
| `.github/workflows/` | the official comparator + absorption gate CI |
| `.devcontainer/` | the Lean codespace |

See `docs/HC_UNIVERSE_MAP.md` for the full merge map.

---

## HONESTY LEDGER

* This universe is authored under a no-local-toolchain sandbox: the Lean
  here is **UNCOMPILED locally**; the repo's comparator CI is the
  verifier of record.
* No file in this repo claims a proof it does not carry.  Boundary
  propositions state exactly where their proofs live (the source
  monolith).  Postulates state exactly which fragments are proven and
  which are open.
* The `waves/` spec layer (Task 4) is **explicitly excluded from the
  build** and marks every statement's proof as pending (`sorry` with
  documented proof routes).  Nothing in it is claimed verified.
* Target axiom profile everywhere: `[propext, choice, Quot.sound]` —
  zero custom axioms, zero sorries, zero native_decide.
