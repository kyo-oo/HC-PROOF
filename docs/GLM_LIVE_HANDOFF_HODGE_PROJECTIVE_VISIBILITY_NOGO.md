# GLM LIVE HANDOFF — PROJECTIVE VISIBILITY NO-GO / BURST-2 CORRECTION

Target branch: `sol/hodge-single-separator-successor`
Assistant source commit: `46669bcd5fa6919d2ccb4f29e011eff9b8acf72a`

New file:

`GSTClassicalHodgeProjectiveVisibilityNoGo.lean`

## Mathematical correction

Do **not** repair the two-burst route by making
`ProjectiveOrbitIrreducibility` an automatic theorem of ordinary projective
correspondence geometry.

The new file formalizes the reason:

1. the canonical ghost-spine source is already an actual algebraic cycle class;
2. every `ProjectiveNativeKernel` is a genuine native/projective cycle operator;
3. its image is therefore again an actual algebraic cycle class;
4. an omniversal separator ghost annihilates every such class;
5. consequently the projective detector readout is identically zero for every
   genuine projective kernel in a ghost world.

Core theorem:

`projectiveDetectorReadout_ghostSpine_eq_zero`

and consequences:

- `no_nonzero_projectiveDetectorReadout_on_ghostSpine`
- `projectiveOrbitIrreducibility_isEmpty_of_ghost`
- `universal_projectiveOrbitIrreducibility_is_hodge_strength`

This is a hard noncircularity firewall.  Keep these theorem statements intact.

## GLM lane

Please repair only parser/elaborator/namespace/API/tactic issues in this new
file and its imports.  Do not change the mathematical route by:

- weakening the separator annihilation statement;
- inserting `ProjectiveOrbitIrreducibility` as a field of
  `GenuineCycleClassGeometry`;
- adding a basis-cycle bridge, `source_action`, `acts_as_GST`,
  `RealizesCosmicOnPoints`, arbitrary point-transition kernel, or Hodge
  surjectivity assumption;
- deleting the semantic-rigidity, visibility-equivalence, normalized-fibered
  defect, or new projective-visibility no-go audits.

## New Burst-2 target

The only legitimate remaining coupling is **not** “ordinary projective output
has nonzero ghost read.”  Instead we need an independently derived theorem
identifying a GST/cohomological multiplicity motion with genuine cycle geometry
on a controlled source, while respecting the defect barrier.  If such an
identification is proposed, audit it against:

- `GSTClassicalHodgeNormalizedFiberedDefectBarrier`
- `GSTClassicalHodgeProjectiveOrbitIrreducibilityAudit`
- `GSTClassicalHodgeProjectiveVisibilityNoGo`

Any proposed bridge that immediately manufactures a basis cycle is Hodge-strength
and must remain explicit rather than silently promoted to foundational geometry.
