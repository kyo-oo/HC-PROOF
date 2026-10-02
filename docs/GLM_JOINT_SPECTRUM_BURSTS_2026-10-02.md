# Joint-spectrum mathematics: three bursts

Branch: `sol/hodge-conjecture-final-integration`.
Base: `a54623e744df7b2cbeaae0404dc2e68b4d7a4255`.
Confirmed green base gate: `36985031436`, including its final trust audit.

BOSS assigned mathematics to this pass and compilation/repair to GLM.
No Lean/Lake command was run in this pass. These are source-complete proof
bodies awaiting elaboration and kernel verification, not new green receipts.

## Compile order

1. `GSTClassicalHodgeJointProgramInterpolation`
2. `GSTClassicalHodgeJointProgramCycleExtraction`
3. `GSTClassicalHodgeJointSpectrumFiniteLanding`

All three are registered in `HodgePureMath`; its existing integration workflow
will therefore compile them. Each module contains axiom-report commands.

## Mathematics

For a selected finite family `v_k`, each ordered pair `(i,j)` can have its own
genuine geometric program `T_ij`, diagonal on that family. The only spectral
separation is `lambda_ij(i) != lambda_ij(j)` for `i != j`. The compiled factor is

`(lambda_ij(i) - lambda_ij(j))^-1 * (T_ij - lambda_ij(j) * id)`.

The ordered product preserves `v_i` and kills every competing `v_j`. No ambient
commutation is used: every factor's action is computed on the common finite
family. The source proves prefix execution, extraction, reconstruction, and
projector composition on its spectral span.

Executing this exact program on a native cycle with expansion `sum a_k v_k`,
then dividing by `a_i != 0`, produces a native cycle with class exactly `v_i`.
Different targets can use different native seeds. The stronger orbit version
compiles source, projector, and normalization into one program from weight zero.

The third burst allows a different finite spectrum for each live direction of
a Hodge class, assembles the extracted cycles with the original coefficients,
and proves the exact class equation. Existing single-observable spectral covers
convert to this route directly from their coordinatewise-visible orbit seeds.

## Exact scope

The explicit finite-separation and native/orbit-seed expansion inputs remain
mathematical inputs. This pass does not construct those data for every smooth
projective variety, does not prove unconditional classical Hodge surjectivity,
and does not remove the geometric spine hypothesis. No pre-existing theorem
statement, proof, workflow, or geometric primitive was changed.

Static checks: all three modules registered; 246-module local import closure
has no missing imports or import cycles; no new proof-escape tokens; clean
whitespace diff. These checks do not establish Lean compilation.
