# GST causal-graph double-fold weight-emergence law

- **Date:** 2026-10-22
- **Kind:** bounded mathematical research attempt and exact finite verification
- **Base checkpoint:** branch research/gpt6-native-point-primitive-span-20261017 at a561857fc24edf835c66c559ad6128c27bba0736
- **Target:** Realize the user's dimension-free GST causal fold as an actual topological identification, derive a dimension-emergence equation, and distinguish pure Hodge structure from misleading charge-zero nonpure classes
- **Types:** Connected finite multigraph Γ with r≥1 rational P¹ normalization components and e ordinary nodal identifications; β=e-r+1; projective nodal curve C_Γ with mixed Hodge cohomology H^k(C_Γ,Q)
- **Conventions:** Cohomological degree k, weight w=p+q, Hodge charge χ=p-q, purity gap δ=w-k, Tate Q(-j) of type (j,j) and weight 2j
- **Nearest prior work:** 2026-10-21-gst-emergent-dimensional-causal-hodge-fold-program.md had one nodal curve plus separate charge leakage. This attempt generalizes causal incidence graphs and produces an **even-degree rational diagonal yet nonpure** class through two independent graph-cycle identifications
- **Outcome:** Proved under standard mixed-Hodge and normalization-sequence facts; self-reviewed, not Lean-kernel-verified. Exact Wolfram computations pass in stated finite ranges
- **Route disposition:** Causal-topology/Hodge purity diagnostic derived; no original-X Chow-source theorem claimed
- **Evidence:** Self-reviewed mathematical argument plus computationally verified finite identities; no new Lean build or axioms assumed
- **Cheapest discriminators:** Tree versus triangle; bouquet with 2 and 3 loops at N=2 gives rank-six weight-two diagonal degree-four cohomology
- **Next unresolved implication:** Obtain an independently constructed actual canonical Chow class on untouched original smooth projective X from an appropriate causal geometric operation, without assuming algebraicity of the input class

## The causal graph rank law

Normalize a connected projective nodal curve whose rational components correspond to Γ vertices. The constant-sheaf normalization sequence gives

\[
0\longrightarrow\mathbb Q\longrightarrow\mathbb Q^r
\xrightarrow{B_\Gamma}\mathbb Q^e
\longrightarrow H^1(C_\Gamma,\mathbb Q)\longrightarrow0.
\]

Connectedness implies rank B_Γ=r-1, so the new weight-zero, Hodge-(0,0) cohomology is

\[
H^1(C_\Gamma,\mathbb Q)\cong H^1(\Gamma,\mathbb Q)
\cong\mathbb Q(0)^{e-r+1}.
\]

No emergent weight-zero hole appears from a tree. One independent causal graph loop produces one, and g independent loops produce g.

With a=t²s²uv, the exact mixed-Hodge graded polynomial on C_Γ×P^N is

\[
(1+\beta t+r a)\sum_{j=0}^{N}a^j.
\]

Every j from 0 through N has β classes at cohomological degree 2j+1 of weight 2j, Hodge type (j,j), giving (χ,δ)=(0,-1).

## Double-causal-fold law: all N, even degree, diagonal charge

For connected graphs Γ₁ and Γ₂ with independent causal loop ranks β₁ and β₂, let

\[
Z_N=C_{\Gamma_1}\times C_{\Gamma_2}\times\mathbb P^N.
\]

The precise all-N formula is

\[
\operatorname{Gr}^{W}_{2j}H^{2j+2}(Z_N,\mathbb Q)
\cong
H^1(\Gamma_1,\mathbb Q)\otimes
H^1(\Gamma_2,\mathbb Q)(-j)
\cong\mathbb Q(-j)^{\beta_1\beta_2},
\quad 0\le j\le N.
\]

Hence there are β₁β₂ rational diagonal Hodge-charge-zero classes in even cohomological degree 2j+2 whose true weight is 2j. They have purity gap δ=-2. This is genuine topological/cohomological birth, not a change of Hodge-coordinate labels.

For every nonempty connected smooth projective X, H⁰(X,Q)=Q supplies the same direct summand in X×Z_N. This validates the arbitrary-input-X and all-emergent-N diagnostic on a **new singular projective realized world**, not on the original smooth X.

An algebraic Tate dimension fold (k,p,q,w)→(k+2j,p+j,q+j,w+2j) conserves both χ and δ; increasing dimension cannot remove the causal purity deficit.

## Executed Wolfram checks

- Connected tree: (vertices,edges,rank B,β)=(3,2,2,0)
- Triangle: (3,3,2,1)
- Three self-loops: (1,3,0,3)
- Four vertices and five edges: (4,5,3,2)
- Single-fold coefficient identities: 84 exact parameter pairs; all TRUE for β=1..4, N=0..5, all j≤N
- Double-fold identities: 324 exact cases; all TRUE for β₁,β₂=1..3, N=0..7, all j≤N
- Degree-four, weight-two example for two and three loops: 6uv, i.e. six rational (1,1) pieces of **wrong degree-two-below weight**

The uniform proofs follow from incidence-rank/normalization plus mixed-Hodge Künneth. The finite checks are not substituted for those proofs.

## Critical category boundary

This does **not** falsify the classical rational Hodge conjecture. C_Γ has nodes, so Z_N is singular. Genuine mixed Hodge structures exist on its cohomology, but the weight-2j classes in degree 2j+2 are not valid pure degree-2j+2 rational Hodge classes of a smooth projective complex variety. A spectral charge-zero projector without the purity index would confuse these objects. No theorem constructing a Chow representative of an arbitrary original-X rational Hodge class is claimed.

## Artifacts and source provenance

- [Full mathematical derivation](../derivations/GST_causal_graph_double_fold_weight_emergence_2026-10-22.tex)
- [Exact stateless Wolfram source](../computations/gst_causal_graph_double_fold_weight_emergence_2026_10_22.wl)
- GST modules read: GSTGeneralSpace, GSTGraphV2OmniversalCore, GSTGraphV2SelfExpandingCosmology, GSTGraphV2RecursiveStateCausality, GSTGraphV2UnboundedHigherCausality, GSTGradedWorldAlgebra, waves/GSTNCohomologyV2, waves/GSTNCohomologyV3, plus current October 21 causal-fold records.
- Exact Wolfram outputs: SingleCount=84, SingleAllTrue=True, DoubleCount=324, DoubleAllTrue=True; matrix rank outputs (2,2,0,3); double even weight-two coefficient 6uv.
- No local Lean installation, no new Lean CI run and no public internet search.
