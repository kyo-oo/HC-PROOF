# GLM LIVE HANDOFF — COHOMOLOGICAL PAIRING FRONTIER

Target branch: `sol/hodge-single-separator-successor`
Assistant source commit: `9ccc6f4576afa8895ae79940f8e4bd7c41188f7d`
Receipt integration commit: `760fa540a300ebe8c2a0fb3007e06dfc46a744e4`

New source:

`GSTClassicalHodgeCohomologicalPairingFrontier.lean`

## Mathematical intent

The universal cycle-naturality barrier rules out the old plan of obtaining a
nonzero ghost-detector response from another genuine native/projective cycle
operator.  This file instead acts on the separator itself.

It introduces a rank-free `PerfectCohomologicalPairing` on the actual
Stage-2G rational singular cohomology carrier and proves:

- every detector has a unique representing cohomology class `dualClass`;
- a nonzero separator has a nonzero dual class;
- an omniversal ghost dual class is orthogonal to the entire genuine atomic
  cycle-class span;
- it still pairs nontrivially with the Hodge direction detected by the ghost;
- failure of Hodge therefore yields a concrete `PairingOrthogonalGhost`.

Core declarations:

- `PerfectCohomologicalPairing`
- `PerfectCohomologicalPairing.dualClass`
- `PerfectCohomologicalPairing.pair_dualClass`
- `PerfectCohomologicalPairing.dualClass_ne_zero`
- `OrthogonalToAtomicCycleSpan`
- `ghostDualClass_orthogonal_atomic`
- `ghostDualClass_detects_ghost`
- `PairingOrthogonalGhost`
- `failure_yields_pairingOrthogonalGhost`

## GLM lane

Please repair parser/elaborator/namespace/Mathlib API/tactic issues only.
Preserve the mathematical content.  In particular:

- do not replace perfect pairing by a basis-cycle bridge;
- do not assert that the pairing-orthogonal complement of algebraic cycles is
  zero;
- do not add any `acts_as_GST`, source-action, point-transition, Hodge
  surjectivity, or arbitrary-cycle-representative assumption;
- keep `GSTClassicalHodgeUniversalNaturalityBarrier` and
  `GSTClassicalHodgeProjectiveVisibilityNoGo` intact.

## Next assistant lane

I am continuing above this interface into primitive / polarization / Hodge-
Riemann style extinction of `PairingOrthogonalGhost`.  If the repository lacks
a genuine classical polarization on `RationalSingularCohomology`, that absence
must remain explicit rather than being substituted with the internal GST-world
pairing.
