# GLM LIVE HANDOFF — normalized fibered defect barrier

Target branch: `sol/hodge-single-separator-successor`
Barrier source commit: `f40de3f9eabfd37b94e7e79f7ceaef15a3a79ef4`

New file:

`GSTClassicalHodgeNormalizedFiberedDefectBarrier.lean`

## Mathematical intent

This is a noncircularity/barrier theorem, not a new closure assumption.

The normalized fibered spectral atom simultaneously exposes:

- native face = `codimensionPointCycle V.X p x`;
- Hodge sheet = `classicalHodgeBasis ... (shapedLiveBasisIndex ...)`.

The new synchronized state uses exactly those two faces. The core theorem is:

`normalizedSpectral_defect_zero_iff_point_represents_basis`

which states that zero synchronized defect is equivalent to

`H.cycleClass p (codimensionPointCycle V.X p x) = selected basis vector`.

Thus GLM must NOT repair this by weakening the RHS or by inserting a generic
cycle witness. The point of the theorem is to show that declaring the enriched
spectral atom defect-free is exactly the missing basis-cycle equality.

The file also proves recoordination preserves the target basis and hence cannot
change this zero-defect requirement.

## Repair hotspots

- unfolding/rewrite order for `normalizedSpectralSynchronizedState_native`;
- `sub_eq_zero` orientation in the iff theorem;
- universe/implicit args of `worldRecoordinate`;
- simplification of the two normalized defect equivalences in
  `recoordination_defect_zero_iff`.

Keep theorem statements intact if possible. No `sorry`, no basis bridge, no
new Hodge-surjectivity assumption.

Please wire this module into `HodgePureMath`/the active Hodge gate once it
elaborates.
