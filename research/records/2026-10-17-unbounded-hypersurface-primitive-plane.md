# Mathbox route: explicit original-variety primitive cycle in every even dimension

- **Date:** 2026-10-17
- **Kind:** research attempt and constructive theorem (special geometric family)
- **Target:** Construct actual primitive rational algebraic representatives for every rational primitive Hodge class on every smooth projective complex X, under its canonical Betti cycle-class map. **The target is pinned and remains unproved.**
- **Hypotheses and types:** m≥1, d≥2, X a smooth degree-d hypersurface in complex projective space ℙ^(2m+1) containing ℙ^m; coefficient domain ℚ for Hodge/cohomology classes and ℤ for intersection numbers. This is a specific infinite family, not all X.
- **Active conventions:** H=h^m; P=[ℙ^m]; ∫h^(2m)=d; ∫h^m[P]=1. Cup-product and top Chern pairing orientation follow complex algebraic intersection theory.
- **Current dependency/evidence status:** Wolfram exact polynomial/Chern checks and an explicit algebraic proof; corresponding Lean polynomial identity, exact Gram calculation and Jacobian derivative certificate committed to `GSTCubicFourfoldPlanePrimitive.lean`, awaiting the latest CI outcome. Scheme-theoretic Jacobian criterion, exact normal sequence, weak Lefschetz and cycle-class identification are cited geometric steps, not verified in that Lean file.
- **Nearest prior attempt and first failure:** `research/records/2026-10-17-directed-component-primitive-birth.md` established a cubic-fourfold plane component but neither a uniform family nor universal target spanning.
- **Route:** Find an explicit smooth hypersurface in every even dimension and degree that CONTAINS a visible non-Lefschetz algebraic middle cycle on the original carrier, not a host or surrogate variety.
- **Mechanism and distinctness from prior routes:** Uniform Jacobian smoothness plus normal-bundle Chern-number computation; the determinant of actual cohomological intersection classes is proved nonzero. This does not require postulating any Hodge preimage, nor does it use the formerly rank-zero Picard trace constructor.
- **Changed input:** Replace an isolated cubic fourfold with an explicitly given degree-d hypersurface `F_{m,d} = Σ_{i=0}^{m} (y_i x_i^(d-1) + y_i^d)` in projective coordinates (x,y), all m≥1,d≥2.
- **Success criterion:** Construct a smooth X_{m,d}, construct algebraic Z_{m,d}=d[ℙ^m]-h^m, show h⋅cl(Z_{m,d})=0 and cl(Z_{m,d})≠0, with the exact geometric Betti fundamental-class correspondence. For the full target separately prove all rational primitive Hodge classes on arbitrary X lie in the span of genuine native algebraic cycles.
- **Failure/no-go criterion:** An unproved cycle-class comparison, weak Lefschetz fact or Chern formula invalidates the claimed geometric link. Existence of one nonzero primitive vector on the family is not all-X spanning.
- **Cheapest decisive check:** Compute c_m and determinant for m=1..8 symbolically and hand-check the Chern identity. Verify no nonzero projective critical points using the Jacobian partial derivatives.
- **Attempt outcome:** The explicit F is smooth by the Jacobian criterion, as checked below. The normal bundle exact sequence gives c_m(N)=coefficient of t^m in (1+t)^(m+1)/(1+dt). Let q_m=c_m. By the binomial theorem,
    `d q_m - 1 = -(1-d)^(m+1)`,
  which also yields `q_0=1, q_{m+1}=1+(1-d)q_m`.
  Hence the intersection Gram of H,P is
    `[[d,1],[1,q_m]]`,
  with determinant `d q_m-1 = (-1)^m(d-1)^(m+1) ≠0`.
  The algebraic cycle Z=dP-H satisfies `Z⋅H=0` and
    `Z²=d(d q_m-1)=(-1)^m d(d-1)^(m+1)≠0`.
  By weak Lefschetz and Poincaré duality, H^(2m+2)(X,Q) is one-dimensional, and h-cup in middle degree is zero iff pairing with h^m is zero. Thus Z is primitive. Its self-intersection being nonzero proves that the canonical geometric Betti class is nonzero.
- **Explicit smoothness check:** ∂F/∂x_i=(d-1)y_i x_i^(d-2) and ∂F/∂y_i=x_i^(d-1)+d y_i^(d-1). For a common zero of all derivatives, any x_i≠0 forces y_i=0 then x_i^(d-1)=0, contradiction. Consequently all x_i=0; the y-derivatives force all y_i=0. The only affine critical point is the homogeneous origin, absent from projective space. The embedded plane y=0 lies in X. No unproved existence/Bertini assertion is necessary.
- **Exact m=2 bridge:** q_2=d²−3d+3; determinant=(d−1)³; Z²=d(d−1)³. Specialize d=3 to the prior cubic Gram [[3,1],[1,3]], Z²=24.
- **Route disposition and scope:** Constructive special-family route succeeded in ordinary mathematics assuming standard geometric identification; full original all-X target OPEN.
- **Continuations:** Tried exact symbolic Chern and Jacobian calculations, Lean kernel route and CI repair. Untested: deriving *new independent native cycles on arbitrary X* from a geometric correspondence without assuming their Hodge representatives; no method here guarantees that.
- **Evidence label:** Proof of the explicit hypersurface family uses standard algebraic-geometric tools; algebraic Chern and Jacobian identities have bounded Wolfram checks plus uniform derivation; Lean checkpoint pending latest CI; universal spanning conjectural.
- **Review and freshness status:** Self-reviewed 2026-10-17; isolated branch `research/gpt6-native-point-primitive-span-20261017`; link CI at `https://github.com/kyo-oo/HC-PROOF/actions/workflows/gst-cubic-fourfold-plane-primitive.yml`.
- **First unresolved or failed implication:** Nothing here makes every arbitrary X a hypersurface containing a maximal plane; nor does one explicit primitive vector give the full primitive Hodge rank, even within a high-degree hypersurface.
- **Strongest surviving statement:** For every m≥1,d≥2 there is an explicit smooth 2m-dimensional degree-d projective hypersurface containing a maximal plane with a nonzero algebraic primitive middle Hodge class d[P]-h^m, and an exact Gram discriminant ±(d−1)^(m+1).
- **Artifacts and commands:** Existing Lean file `GSTCubicFourfoldPlanePrimitive.lean`; GitHub workflow `.github/workflows/gst-cubic-fourfold-plane-primitive.yml`; Wolfram exact coefficient and Gröbner tests (m=1 cases d=2..5). GitHub CI without local Lean installation.
- **Next unresolved question:** Can the directed-component selection or CM/GST operators produce, for EVERY arbitrary X, enough genuine independent non-Lefschetz classes to fill the target primitive Hodge rank and identify them canonically?
- **Uniform route or obstruction:** Every hypersurface-family member has an independent primitive source, but no functorial transfer of these source cycles to an arbitrary X has been proved. A transfer map that kills primitive classes or changes varieties cannot satisfy the user's original target.
- **What another bounded case would discriminate:** Vary independently meaningful components on a single hypersurface with primitive rational Hodge rank≥2 and test whether the resulting geometric intersection determinant is full rank. That distinguishes component-rich source production from a lone plane direction.

## Final acceptance contract

The original theorem requires the universal implication (for all smooth projective complex X, all codimensions p, and every rational primitive class α):
`∃ Z : codimensionCycles X p, canonicalCycleClass(Z)=α`,
with no unproved *surjectivity*, *rank*, *representation* or *period annihilator* premise. No weaker source-family construction may be promoted to full acceptance.
