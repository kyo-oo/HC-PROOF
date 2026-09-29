# GLM live handoff — first primitive defect sector

Target branch: `sol/hodge-single-separator-successor`

This handoff is for **Lean repair/registration only**.  Preserve the mathematics and do not strengthen any hypothesis into Hodge algebraicity, basis-cycle realization, projective irreducibility, or full matrix-unit externalization.

## New mathematical chain

The new files, in dependency order, are:

1. `GSTClassicalHodgePrimitiveProjectiveMomentProfile.lean`
   - commit `f27c68bbc91ad88269f738b7b12b2750f9ed25fc`
   - descends the primitive failure to a genuine projective matrix coefficient
     `projectiveGhostMoment`.
   - nonzero moment implies nonzero descended projective defect state.

2. `GSTClassicalHodgePrimitiveProjectiveDualOrbit.lean`
   - commit `7fd21bca447b82476a65d7fe4d17cf25c8069dd3`
   - constructs the contragredient projective action on algebraic-annihilating
     Hodge functionals and packages a primal/dual projective failure packet.

3. `GSTClassicalHodgeFirstPrimitiveProjectiveFailure.lean`
   - commit `876f099c48ef1b041952feb5035ebe1694616282`
   - globalizes a counterexample to its least positive atomic-defect weight.
   - all lower weights are defect-free.

4. `GSTClassicalHodgeHodgeDefectImageFunctoriality.lean`
   - commit `96e775b053d3ef92e4867229e72dfd4d72795573`
   - defines the correct realized defect sector
     `HodgeDefectImage = range atomicDefectLinearMap`.
   - proves it is bottom iff the Hodge defect map is zero.
   - genuine Hodge-stable graded operators act functorially on these sectors.

5. `GSTClassicalHodgeFirstFailureCokernelRigidity.lean`
   - commit `ae8ff300845fb990a6eefc7a879563774ec97d07`
   - proves a first nonzero defect lies outside the genuine principal-cut Hodge
     image.
   - proves no nonzero-scaled modulo-atomic or polarized adjoint/scaled return to
     a lower weight can exist at the least failure.

6. `GSTClassicalHodgeFirstFailurePrimitiveImage.lean`
   - commit `abe3980b9f34f1fa8586c4d56028ca4bf3f9ec85`
   - defines `PrimitiveDefectImage`.
   - proves at a first bad successor:

       `PrimitiveDefectImage = HodgeDefectImage != bottom`

     and the previous-weight principal-cut action on realized defects is zero.

7. `GSTClassicalHodgeFirstPrimitiveProjectiveSector.lean`
   - commit `9496bc5fee930de3e3165e9bf65c764672305a84`
   - proves the entire first primitive defect image is invariant under every
     genuine projective Hodge word.
   - every chosen ghost projective orbit module lies inside this canonical
     primitive residual sector.

8. `GSTClassicalHodgeFirstPrimitiveProjectiveDualSector.lean`
   - commit `1da7170a5dcaf59a4e94a7f83367c90227b22416`
   - uses `Submodule.liftQ` to descend the ghost separator directly to the
     atomic-defect quotient.
   - restricts it to a nonzero covector on the canonical first primitive sector.

9. `GSTClassicalHodgeFirstPrimitiveSectorRetraction.lean`
   - commit `2c92864d50fa046e66605ad515797c2fc09e8c0c`
   - smallest extinction interface so far.
   - at a least failure, even a **one-state** nonzero-scaled down/up return for
     the distinguished ghost through any lower realized defect sector is
     impossible.

## Mathematical normal form now reached

A hypothetical Stage-2G Hodge failure is reduced to a least weight `p+1` with

- `atomicDefectLinearMap q = 0` for every `q <= p`;
- `HodgeDefectImage (p+1) != bottom`;
- `HodgeDefectImage (p+1) = PrimitiveDefectImage (p+1)`;
- the previous principal-cut realized defect action is zero;
- the primitive sector is invariant under all genuine projective words;
- a trace-zero primitive ghost supplies a nonzero quotient-native covector on
  that sector;
- one nonzero-scaled lower return of that single ghost would contradict
  minimality.

In symbols, the residual is now

`0 != D_first^prim = D_first^Hdg`

with genuine projective action and nonzero dual covector, while every lower
`D_q^Hdg` is zero.

## Repair firewall

Do **not** repair these files by inserting any of the following:

- `BigradedBettiHodgeStatement` as a hypothesis;
- target-basis algebraicity;
- `ProjectiveOrbitIrreducibility`;
- bare same-weight `L^2` native realization;
- `AtomCosmicExternalization` / full cosmic matrix-unit realization;
- projective live-source-to-arbitrary-target realization;
- a return law on the whole Hodge fiber when only the stated one-state law is
  needed.

Those stronger routes have already been audited and are Hodge-strength or
strictly stronger than the present frontier.

## Expected repair style

Surgical syntax/API repair only.  Preserve theorem statements unless a Lean API
name/coercion must be adjusted.  If a theorem statement itself is ill-typed,
make the smallest type-correct restatement preserving the mathematical claim.
Do not replace proofs with `sorry`, axioms, or opaque custom hypotheses.

Likely API-sensitive spots:

- `Submodule.Quotient.mk_eq_zero` coercions;
- `LinearMap.range` subtype witnesses;
- `LinearMap.comp` / `Module.End` coercions;
- `ProjectiveHodgeWord.id` implicit `R,p` inference;
- scalar action on linear maps in the sector-retraction file;
- `Nat.find_min'` / least-weight proof shape;
- rewriting subtype equalities and `Subtype.ext`.

## Next mathematics after repair

Do not expand back to whole-fiber matrix units.  The next target is to derive the
**one-state lower return** in
`GSTClassicalHodgeFirstPrimitiveSectorRetraction.lean` from independently
constructed cross-weight geometry (principal cut + genuine correspondence /
adjoint / polarization data), only on the distinguished primitive ghost state.
That is now the narrowest noncircular closure target.
