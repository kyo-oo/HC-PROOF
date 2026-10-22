# GST dimension-emergent causal graph geometry: actual Hodge alignment and topology-born mixed weight

- **Date:** 2026-10-23, Asia/Kolkata
- **Mathematical research protocol:** Mathbox research-program, research-attempt and proof-audit; Wolfram exact computation audit. Original user requested a geometry/topology-first experiment, not repetition of the algebraic-image defect compiler.
- **Owner's actual hypothesis:** The dimensionless GST General Space admits arbitrary emergent geometric dimensions and higher causal graph cells; vary whole realized geometry and topology to determine which Hodge structures or types persist and which break. For the original experiment one may provisionally assume universal Hodge algebraicity but must not use that assumption as proof. Preserve the full spatial and whole-structure meaning of the question.
- **Base:** branch `research/gpt6-native-point-primitive-span-20261017` with start HEAD `362904b71f85b2010d4fdf725bb4b4615d0830be`.
- **Fixed exact classical theorem:** Each rational (p,p) Hodge class on each smooth projective original X has a genuine canonical rational algebraic cycle representative. This remains a goal, not a presupposition.
- **Source ontology:** `GSTGeneralSpace.lean` provides a dimensionless carrier; `GSTGeneralSpaceRealization.lean` and `GSTGeneralSpaceSchemeDimensionObservation.lean` supply optional realized geometry/dimension; `GSTGraphV2UnboundedHigherCausality.lean` has unbounded globular causal cells and signed boundary; `GSTGradedWorldAlgebra.lean` carries causal signed charges; previous [intrinsic topology-fold derivation](../derivations/GST_intrinsic_causal_dimension_topology_fold_weight_birth_2026_10_21.tex) established actual MHS weight-zero birth from graph nodal folds. These are inspected and reused, not ignored.
- **New full theorem:** [GST causal graph dual geometric realization derivation](../derivations/GST_causal_graph_emergent_hodge_alignment_topology_duality_2026-10-23.tex). All original smooth projective X; all finite loop-free causal graphs Γ; any vertex complex moduli τ_v in upper half-plane. Two actual realizations of Γ simultaneously: smooth projective Y_τ=X×ΠE_τv and proper singular topology-folded T_Γ=X×C_Γ, where C_Γ is a nodal projective curve with dual graph Γ.
- **Source availability:** No fabricated rational Chow map; at geometric alignment each marked rational edge class has an explicitly constructed algebraic diagonal divisor. This restricted family gives actual *geometry→algebraicity* as requested.

## Outcome of geometry-first Hodge/break test

For a graph edge e:v→w, the integral topological class Ω_e=(dx_v−dx_w)∧(dy_v−dy_w) on the actual smooth projective product has exact holomorphic-period wedge

`Ω_e ∧ dz_v ∧ dz_w=(τ_w−τ_v) dx_v∧dy_v∧dx_w∧dy_w`.

Therefore Ω_e is rational (1,1) **iff** τ_v=τ_w. When equality holds the marked complex elliptic curves are identical and the **actual algebraic diagonal** Δ_vw realizes the class through the genuine canonical rational Betti cycle map. Changing τ while keeping the smooth topological torus fixed can break an individual rational class's (1,1) condition, even though the whole smooth projective Hodge structure of every product remains pure.

The simultaneous edge-class Hodge locus is exactly ker B_Γ∩H^V, i.e., one complex parameter per graph component; its complex codimension is |V|−c.

For the actual projective nodal topology fold T_Γ, the normalization MHS sequence gives W0 H¹(T_Γ,Q)≅coker B_Γ, of dimension |E|−|V|+c. A graph cycle births actual weight-zero H¹; a forest gives none. This Hodge purity break happens in a **singular** projective realization (outside the smooth-projective class of the rational Hodge conjecture), not in the smooth projective Y_τ.

The **complementarity law** between these two distinct geometric realizations is
`codim_C(Hodge alignment locus) + dim_Q W0 H¹(T_Γ) = (V−c)+(E−V+c)=E.`
It is an exact integer identity for ANY finite graph, without interpreting its causal cell index as an intrinsic geometric dimension. Both realizations work with every arbitrary original X as a product factor; this is not a substituted special-Hodge X.

## Wolfram audit

- Actual [Wolfram source](../computations/gst_causal_hodge_alignment_topology_graph_2026_10_23.wl), committed and fetched/re-executed at blob `04ec4586c23f5f479f56d4fb6562619a8594b8c2`.
- Exact 4×4 exterior coefficient determinant = `ss−tt` (no floating values).
- Independently enumerated **all 1099 labelled simple graphs on 1..5 vertices**; tested ordinary graph ConnectedComponents and the signed rational incidence MatrixRank separately. Graph rank, weight-zero loop count and nonnegative Euler characteristic identities passed all cases. No failures.
- Triangle: `V=3,E=3,c=1`, alignment rank 2, mixed-weight birth 1. Complete 5-vertex graph: `V=5,E=10,c=1`, alignment rank 4, mixed-weight birth 6.
- The finite exhaustive domain is labelled **simple** graphs of 1..5 vertices; the LaTeX general theorem follows from incidence rank/nullity and also covers multigraphs with parallel edges. Wolfram does not establish all-world Hodge algebraicity.

## In-place formal integration

- Edited existing `GSTGraphV2UnboundedHigherCausality.lean` at commit `95b127468e20c31f767b3d426ae4d975cd4fb164` to add **realized** `CausalHodgeAlignment.edgePeriodDrift`, `edgePeriodDrift_zero_iff`, `CausalReach`, `edgeAlignment_constant_on_causal_paths`, and converse, without positing any unproved Chow surjectivity.
- CI workflow `gst-intrinsic-causal-fold-boundary.yml` automatically builds that source on the active branch; run **39838395103** is revision-specific. Check its completion before saying green. This Lean law is a typed graph-plus-complex-period identity, **not** a Lean proof of the geometric MHS theorem or the general rational Hodge conjecture.

## Proof-audit verdict

- **Proved in mathematical derivation (standard explicit real geometry and MHS):** geometric Hodge period, exact alignment locus, actual diagonal representative on aligned edge, topology-born mixed-weight dimension and causal incidence complementarity.
- **Not proven or refuted:** the universal assertion that purity of every smooth-projective Hodge realization forces all of its rational diagonal Hodge classes to be algebraic. As a theorem for actual smooth projective varieties that assertion would be the rational Hodge conjecture. There is no known actual smooth-projective counterexample supplied by this experiment; the failure of an abstract inference is NOT a counterexample to the conjecture.
- **Critical conceptual distinction:** full *purity* of Hodge decomposition; *Hodge status* of a marked integral cohomology class; canonical *algebraicity* of a class of type (p,p) are distinct typed predicates. In the edge family the extra geometric diagonal law proves algebraicity where the class is Hodge, directly and constructively. A general geometry-to-algebraicity theorem for all rational Hodge fibers on all original X is not yet derived.

**Program continuation direction:** pursue new actual realized causal geometry laws capable of producing a universal geometric identification for arbitrary rational diagonal Hodge classes, not a theorem conditional on their prior algebraicity. Maintain original-X/whole-space scope.