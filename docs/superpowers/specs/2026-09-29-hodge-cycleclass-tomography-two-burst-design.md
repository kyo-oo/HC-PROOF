# Hodge cycle-class / tomography closure — two-burst design

Date: 2026-09-29
Target branch: `sol/hodge-single-separator-successor`
Inspected head before this spec: `afd9bd39ffddec7c93036498ab44d1c139b98bcb`

## 1. Goal

Upgrade the current classical-Hodge landing so that the existing GST tomography,
fibered multiplicity, projective correspondence, omniversal ghost, and canonical
spine machinery attach to **genuine cycle-class geometry** strongly enough to
rule out a surviving separator ghost without assuming any statement equivalent
to Hodge surjectivity.

The desired final route is:

```
hypothetical Hodge failure
  -> omniversal/minimal separator ghost
  -> canonical nonzero algebraic spine source
  -> GST tomography selects a nonzero ghost moment / live sheet
  -> independently constructed geometric cycle-class observable/correspondence
     has nonzero separator visibility on that spine source
  -> projective detector visibility / detector-moment collision
  -> contradiction
  -> BigradedBettiHodgeStatement
```

The proof must not close by storing a field such as `acts_as_GST`,
`source_action`, `RealizesCosmicOnPoints`, an arbitrary point-transition kernel,
or a basis-cycle bridge whose content is already the missing Hodge conclusion.
Those remain valid reduction interfaces, but they are not accepted as the new
foundation theorem.

## 2. Why the semantic layer must change

The current `HodgeBigradedBettiData` stores `cycleClass` as an arbitrary
rational-linear map. The existing Stage-2G semantic-rigidity files construct a
zero-cycle-class package with the same analytification and Hodge bigrading and
prove that Hodge then fails whenever a rational `(p,p)` fiber is nontrivial.

Even the current `GeometricCycleClassSpine` survives that zero-map model because
its naturality squares can commute trivially with zero cohomological maps.
Therefore no composition of the existing Stage-2G package + current spine +
pure GST coordinate/tomography machinery can prove the unconditional target.

The new layer must contain **independently geometric laws that the zero map
cannot satisfy**. `ProjectiveDegreeTraceSemantics` is the first such law: a
native codimension point has strictly positive projective degree and its genuine
cycle class has the same trace, so the cycle class cannot vanish.

This design extends that idea from nonvanishing/vertical information to the
horizontal separator/tomography direction.

## 3. Existing machinery to preserve and reuse

Do not replace or re-route the following architecture:

- `GSTClassicalHodgeStage2GSemanticRigidity`
- `GSTClassicalHodgeSpineSemanticSeparation`
- `GSTClassicalHodgeProjectiveDegreeTrace`
- `GSTClassicalHodgeFiberedTransferCompletion`
- `GSTClassicalHodgeLiveSheetIntertwining`
- `GSTClassicalHodgeNormalizedFiberedSpectralAtom`
- `GSTClassicalHodgeLefschetzTomography`
- `GSTClassicalHodgeGhostSpineCosmicLeak`
- `GSTClassicalHodgeOmniversalSeparatorGhostCrown`
- `GSTClassicalHodgeFiniteClosedCorrespondence`
- `GSTClassicalHodgeFiniteClosedCorrespondenceOperator`
- `GSTClassicalHodgeProjectiveCorrespondenceAlgebra`
- `GSTClassicalHodgeProjectiveDetectorMomentCollision`
- `GSTClassicalHodgeProjectiveDetectorVisibility`
- the canonical projective spine / principal-cut successor machinery.

The newest visibility reduction is the preferred terminal collision surface:
for a ghost `E`, it is enough to construct one genuine projective/native kernel
whose cohomological action on `ghostSpineSeed` has nonzero reading under
`E.separator.detector`.

## 4. New semantic architecture

### 4.1 Genuine cycle-class geometry package

Introduce a stronger geometry package layered *above* `HodgeBigradedBettiData`
rather than changing every historical theorem immediately.

Working name:

```lean
structure GenuineCycleClassGeometry
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) extends
      GeometricCycleClassSpine V H,
      ProjectiveDegreeTraceSemantics V H where
  ...
```

The new fields must be geometric and zero-map excluding. They must not mention
`BigradedBettiHodgeStatement`, algebraicity of arbitrary Hodge basis vectors,
`ProjectiveDetectorVisible`, or exact GST matrix-unit realization.

The preferred additional primitive is a family of genuine projective
cycle-class readouts/operations generated from native projective geometry:
closed correspondences, hyperplane/principal sections, push-pull, intersection,
and rational linear combinations already present in the projective kernel
algebra.

The semantic package should expose only laws that are standard for the actual
cycle-class construction, e.g. compatibility of cycle class with those native
projective operations and trace/pairing evaluations.

### 4.2 Separator-visible geometric algebra

Construct a theorem rather than an assumption:

```lean
exists_projective_detector_visible :
  ∀ E : OmniversalSeparatorGhost G,
    Nonempty (ProjectiveDetectorVisible G M E)
```

or a strictly more primitive theorem from which this follows.

This theorem is the horizontal geometric upgrade. It must be obtained by:

1. taking the canonical algebraic spine source at `E.weight`;
2. using the finite projective/correspondence algebra to produce a finite
   family of genuine native images;
3. applying a nondegenerate geometric readout/pairing to show those images
   separate the live Hodge/tomography direction selected by the ghost;
4. converting one nonzero readout into `ProjectiveDetectorVisible`;
5. using the already-proved rational rescaling theorem to hit the exact
   tomography moment if needed.

The critical noncircularity condition is that Step 3 is proved from an
independently geometric nondegeneracy/separation theorem, not from an assumed
basis representative.

### 4.3 Tomography role

Do not “fix” tomography by changing its internal GST statement unless a formal
bug is found. Current tomography already detects nonzero finite multiplicity
states. The upgrade is to prove that genuine projective geometry has enough
observable directions to couple to at least one nonzero tomography moment.

The intended interface is:

```text
nonzero ghost
  -> nonzero tomography moment
  -> geometric pairing/nondegeneracy produces a native projective kernel
     with nonzero detector response
  -> existing ProjectiveDetectorVisible.toMomentHit
  -> existing detector-moment contradiction
```

Thus tomography remains the spectral detector; geometry supplies the missing
horizontal visibility.

## 5. Candidate geometric proving mechanisms

Use them in this preference order and keep only what survives the formal audit.

### Approach A — projective pairing separation (preferred)

Exploit actual projective degree / complementary hyperplane intersection /
Poincare-style readouts on classes produced by the projective correspondence
algebra. Prove a finite family of such projective readouts separates the finite
live support used by tomography. Then a nonzero ghost moment forces one
projective-native image to have nonzero separator reading.

Advantages:
- directly extends the already-valid projective-degree semantics;
- zero cycle class fails immediately;
- needs only finite support selected by each ghost;
- avoids global basis-cycle realization.

Risk:
- requires enough actual cohomological pairing structure to be available in
  the current Betti carrier / Hodge package.

### Approach B — correspondence moment matrix

For the finite live support of a ghost, build a finite matrix

```
M[r,s] = detector (cl (K_r (spineSource_s)))
```

from genuinely constructed projective kernels `K_r`. Prove the matrix has
nonzero determinant / full separating rank using projective incidence or GST
triangularity after a separately proved geometric comparison theorem.

Advantages:
- naturally matches the finite tomography matrix;
- does not require all-pairs/global realization.

Risk:
- the comparison theorem must not smuggle in the desired target action.

### Approach C — enriched fibered defect propagation

Use the fibered native/Hodge pullback and an actual geometric operation with a
proved cycle-class commuting square. Start from the canonical zero-defect spine
state and propagate zero defect to a state whose Hodge face has nonzero ghost
reading.

Advantages:
- fits the existing synchronized-defect infrastructure.

Risk:
- current no-descent results show that arbitrary multiplicity matrix units
  cannot simply descend to unlabeled native cycles. This route is accepted only
  if the new operation is independently geometric rather than a relabeled GST
  sheet motion.

Approach A is the default implementation route. B and C are fallback proving
routes, not parallel architectural forks.

## 6. Burst 1 — foundation and handoff

Burst 1 writes the new geometric semantics and the lowest-level theorems first.
Expected files (names may be refined to match existing conventions):

1. `GSTClassicalHodgeGenuineCycleClassGeometry.lean`
   - aggregate current spine + projective degree semantics;
   - add the minimal genuine projective pairing/correspondence laws;
   - prove explicit zero-map exclusion;
   - provide projections back to old interfaces.

2. `GSTClassicalHodgeProjectiveTomographyReadout.lean`
   - define geometric finite readouts on the canonical spine/correspondence
     orbit;
   - connect them to the finite GST tomography coordinates without assuming
     target algebraicity;
   - prove scaling/linearity/finite-support formulas.

3. `GSTClassicalHodgeProjectiveVisibilitySeparation.lean`
   - prove the key finite separation lemma;
   - derive a nonzero projective separator read whenever a nonzero ghost exists;
   - package the result as `ProjectiveDetectorVisible`.

4. A temporary/current branch receipt file if needed, e.g.
   `GSTClassicalHodgeTwoBurstClosureReceipt.lean`, importing the new Burst-1
   files and exposing the exact theorem names for GLM/CI.

After Burst 1 source is committed:

- publish a GLM handoff in the repository containing:
  - target branch and exact commit;
  - new files/theorem names;
  - which theorem bodies are mathematically intended but may need Lean repair;
  - strict instruction to repair compiler/API issues only, not replace the
    geometric route with assumptions or alternate Hodge-equivalent interfaces;
  - do not delete semantic-rigidity audits.

- trigger the repository CI/workflow on that commit so GLM has concrete logs.

The handoff must happen **after** the Burst-1 source exists, not before.

## 7. Burst 2 — consume the repaired foundation and close the transformed route

While GLM repairs Burst 1 in parallel, continue writing the higher-level proof
files against the intended theorem signatures:

1. `GSTClassicalHodgeTomographyVisibilityCrown.lean`
   - `GenuineCycleClassGeometry`
   - omniversal ghost
   - projective-tomography separation
   - `ProjectiveDetectorVisible`
   - existing `toMomentHit`
   - existing detector-moment contradiction.

2. `GSTClassicalHodgeGenuineSemanticClosure.lean`
   - prove no omniversal separator ghost can survive under genuine geometry;
   - derive `BigradedBettiHodgeStatement V H` from the strengthened geometric
     package.

3. Integrate a final theorem into the public Hodge landing surface only after
   the strengthened geometry instance for the intended genuine classical
   cycle-class construction is present. Do not claim an unconditional theorem
   over arbitrary `HodgeBigradedBettiData`.

4. Re-check GLM commits/CI, reconcile theorem-name or Mathlib API repairs, and
   run/trigger the final CI receipt.

## 8. GLM division of labor

Assistant lane:
- mathematical architecture;
- theorem statements;
- proof derivations;
- Lean source files;
- integration logic;
- noncircularity audit.

GLM lane:
- Lean parser/elaborator/API repair;
- namespace/import fixes;
- tactic repair;
- compile failures and CI diagnostics;
- no mathematical rerouting unless a formal contradiction is demonstrated.

Both lanes work on the same branch. Before every write burst, refresh branch
head to avoid overwriting parallel commits.

## 9. CI strategy

After each burst:

1. refresh current branch head;
2. inspect whether GLM has advanced it;
3. commit only against the latest compatible head;
4. trigger the existing Hodge/Lean workflow;
5. read failing job logs;
6. classify failures as:
   - parser/API/tactic repair -> GLM;
   - theorem statement mismatch / mathematical gap -> assistant;
7. never change a green mathematical route merely to silence CI.

No new branch is created.

## 10. Acceptance criteria

The upgrade is successful only if all of the following hold:

- [ ] current zero-map countermodel cannot instantiate the new genuine geometry
      package;
- [ ] projective-degree/nonvanishing semantics remain derivable/embedded;
- [ ] no new field is equivalent to arbitrary Hodge basis algebraicity,
      `BigradedBettiHodgeStatement`, or exact cosmic matrix-unit realization;
- [ ] tomography remains a derived detector, not a geometric assumption;
- [ ] a surviving omniversal ghost yields a nonzero tomography moment;
- [ ] independent projective geometry produces a nonzero detector-visible
      native/correspondence action on the canonical spine source;
- [ ] existing `ProjectiveDetectorVisible.toMomentHit` and collision theorems
      eliminate the ghost;
- [ ] the final closure theorem is stated over strengthened genuine geometric
      semantics, not arbitrary Stage-2G data;
- [ ] GLM handoff and CI are triggered after Burst 1;
- [ ] final CI is checked after Burst 2;
- [ ] no `sorry`, custom Hodge-surjectivity axiom, hidden basis bridge, or
      renamed conclusion is introduced.

## 11. Non-goals

- Do not rewrite the entire GST cosmology.
- Do not replace the omniversal ghost route.
- Do not require all-pairs matrix-unit externalization.
- Do not assume native lifts for bare `L²` on a ghost sheet.
- Do not use the zero-map-compatible old spine as if it were the genuine
  cycle-class construction.
- Do not create a new branch.

This is a semantic/geometric strengthening that lets the already-developed
GST tomography and ghost machinery attach to actual classical cycle-class
geometry.