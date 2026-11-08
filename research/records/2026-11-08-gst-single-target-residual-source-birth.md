# 2026-11-08 — Single-target reduction: universal residual source-birth

## Status

A new conditional theorem module has been added on the isolated branch
research/gpt6-residual-source-birth-conditional-20261108:

- GSTUniversalResidualSourceBirth.lean
- research/derivations/GST_single_target_residual_source_birth_alpha_superfold_2026_11_08.tex
- .github/workflows/gst-universal-residual-source-birth.yml

The dedicated Lean workflow is running at creation time; no green result is claimed in this record until its run completes.

## Exact single target

For the actual rational Hodge fiber B_p(X) and canonical cycle-class image
A_p(X), fix a positive perfect rational polarization Q_p. The one
source-generation law is

\[
\forall\,0\ne r\in B_p(X),\quad
\exists Z\in \operatorname{CH}^p(X)_{\mathbb Q}:
Q_p(r,\operatorname{cl}_p(Z))\ne0.
\]

Under finite-dimensionality and perfectness of the polarization, this law is
equivalent to surjectivity of the cycle-class map, hence equivalent to the
Hodge conjecture in codimension p. It is not an easier substitute for the
conjecture; it is the exact dual source-birth formulation.

The Lean module formalizes the equivalence through injectivity of the dual
map. It also specializes the result to the supplied Stage-2G cycle-class
map, using the existing GeometricCycleClassSpine only to restrict cycle
classes to the Hodge subspace.

## Conditional theorem

The module proves:

- residual source-birth iff surjectivity of the cycle-class map;
- universal residual source-birth implies
  EveryHodgeClassIsRationalAlgebraic;
- under the same polarized semantics, universal residual source-birth is
  equivalent to the Stage-2G Hodge target.

The theorem is conditional on finite-dimensional polarized Hodge semantics.
Stage-2G still stores the cycle-class map as supplied data. The result is
classical Hodge only after that map is instantiated by the canonical
geometric cycle-class map.

## Mathematical integration

The accompanying derivation consolidates three existing source routes:

1. GSTActualXHodgeResidualProjection and
   GSTPolarizedHodgeResidualEnergy: a nonzero residual/cycle pairing gives
   a genuine rank-increasing native source.
2. The alpha-indexed finite-pole projector algebra: a genuine regular
   idempotent solution is converted by Fitting/Newton into an actual
   original-X Chow source; the universal period-birth statement remains the
   missing step.
3. The spatial-fold alpha-bundle: one-fold Dolbeault integrability is a
   sufficient source-return condition; the plus/minus pair-fold integrability
   condition is the exact algebraization criterion.

The derivation explicitly separates the abstract rational GST curvature
tower from endomorphism-valued Dolbeault curvature on the alpha-selected
bundle. The missing bridge is a multiplicative, graded,
differential-compatible representation of the GST carrier on that bundle.
A local nilpotent endomorphism example shows why scalar trace curvature
cannot stand in for the full matrix-valued (0,2) curvature.

## No-go corrections retained

- Doubling an abstract carrier alone does not create an original-X cycle.
- Scheme self-maps are too restrictive to realize arbitrary off-diagonal
  correspondence operators.
- The current finite-closed-correspondence word algebra is not the full
  proper-correspondence algebra.
- GraphV2 cycle-path/source-realization fields remain inputs, not source
  construction theorems.
- The Stage-2G semantic boundary remains explicit.

## Next research target

Construct the GST-to-Dolbeault representation on the alpha-selected
topological K-class, or directly establish the universal residual
source-birth law by the alpha-indexed finite-pole projector construction.
No unconditional Hodge proof is claimed.
