# THE WAVE MECHANICS LAYER — Task 4 spec modules

**STATUS: UNCOMPILED.** This directory is the Task-4 Wave Mechanics
specification layer. The sandbox that authored it operates under a
permanent **Lean toolchain ban** (Boss Override, see worklog). Therefore:

* nothing in `waves/` is part of any build target;
* the CI comparator on the curated universe does **not** compile these
  files (they are not roots of the `HCUniverse` registry and are not
  imported by `HCProof.lean`) — the green verdict of commit 5eecc25 and
  successors is unaffected;
* every theorem below is a **statement with a pending proof** (`sorry`),
  following the repository's own Challenge-file discipline: the statement
  is the deliverable, the proof is the work, and no claim of
  machine-verification is made here (Ledger 012/037 discipline).

## To compile on the boss's side

Add the desired modules as roots of the `HCUniverse` registry in
`lakefile.toml` (module names acquire the `waves.` prefix from this
directory), then run the comparator as usual:

```toml
[[lean_lib]]
name = "HCUniverse"
roots = [
  # ... existing 129 roots ...
  "waves.GSTWaveCohomology",
  "waves.GSTNCohomology",
  "waves.GSTVortexSingularity",
  "waves.CardinalWorldsPostulateLaw",
]
```

(Note: the module prefix is lowercase `waves` — it matches the lowercase
directory, and Lean module resolution is case-sensitive.)

`sorry_check.sh` will then report exactly which statements still carry
pending proofs.

## Contents

| File | Wave | What it specifies |
|------|------|-------------------|
| `GSTWaveCohomology.lean` | **WAVE I** | The Hodge wave: digit readout replaced by cohomology-class readout; the emergence equation as the closedness law; finite comparison certificates as wave amplitudes. |
| `GSTNCohomology.lean` | **WAVE II** | N-cohomology: the wave parameterized by N; shape complexes, tower windows, and the interference pairing with Wave I. |
| `GSTVortexSingularity.lean` | **THE METHOD** | The OpenAI / Córdoba–Martínez-Zoroa Navier–Stokes vortex-singularity method, copied in structure and upgraded with GST cosmology, for any N shapes in holes. |
| `CardinalWorldsPostulateLaw.lean` | **THE LAW** | POSTULATE III — the Law of Controlled Emergence: infinity admitted only as the colimit of certified finite towers; dimensions are emergent readouts. |

The full theory document is `docs/WAVE_MECHANICS_TASK4.md`; the law book
of the underlying GST Graph V2 is `docs/GST_V2_OPERATING_MANUAL.md`.
