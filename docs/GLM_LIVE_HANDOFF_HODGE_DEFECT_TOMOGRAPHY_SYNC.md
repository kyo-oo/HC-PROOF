# GLM LIVE HANDOFF — ATOMIC DEFECT / TOMOGRAPHY SYNCHRONIZATION

Target branch: `sol/hodge-single-separator-successor`
Assistant synchronization commit: `55a2f0f75607b3e024c5f2af9dba082fc6125955`
Receipt integration commit: `7313df1e62d39f7ccecf49da34502f5ded7f6acc`

New source:

- `GSTClassicalHodgeAtomicDefectTomographySynchronization.lean`

Also active assistant sources:

- `GSTClassicalHodgeCohomologicalPairingFrontier.lean`
- `GSTClassicalHodgePolarizedHodgeGhost.lean`
- `GSTClassicalHodgePolarizedOrthogonalExtinctionAudit.lean`
- `GSTClassicalHodgeProjectiveVisibilityNoGo.lean`

## Mathematical intent

The new synchronization file does NOT externalize a GST operator to native
cycles.  Instead it uses the existing omniversal separator itself, which
annihilates the atomic span, to factor a linear detector through the genuine
atomic defect quotient.  It then rationally rescales that descended quotient
functional so its value on the nonzero ghost defect is exactly the nonzero GST
Lefschetz-tomography moment selected from the same failed Hodge sheet.

Core declarations:

- `ghostDefectDetector`
- `ghostDefectDetector_mk`
- `ghostDefectDetector_ghostAtomicDefect_ne_zero`
- `ghostTomographyScalar`
- `ghostTomographyScalar_ne_zero`
- `synchronizedDefectRead`
- `synchronizedDefectRead_ghostAtomicDefect`
- `synchronizedDefectRead_ne_zero`
- `SynchronizedAtomicDefectGhost`
- `failure_yields_synchronizedAtomicDefectGhost`

## GLM lane

Repair Lean/API issues only.  `Submodule.liftQ` / quotient simplification is the
most likely pinned-Mathlib API point.  Preserve the theorem statements and the
quotient-level nature of the construction.

Do NOT replace the quotient detector with:

- a basis-cycle bridge;
- a point-transition kernel for the GST matrix unit;
- a projective correspondence claimed to have nonzero ghost reading;
- `ProjectiveOrbitIrreducibility` as an automatic geometry theorem;
- an assumption that the atomic defect quotient is zero.

Those are already audited as Hodge-strength or formally incompatible with a
surviving ghost.

The assistant lane continues searching for a strictly weaker constructive
finite algebraic-test / moment mechanism that can force the synchronized
quotient readout to vanish.
