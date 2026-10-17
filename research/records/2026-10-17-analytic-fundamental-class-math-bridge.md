# Mathbox research attempt: independent analytic construction of point Betti classes

**Date:** 2026-10-17. **Original pinned acceptance target:** For every smooth projective complex X, every codimension p, every rational primitive (p,p) class α, construct a rational algebraic cycle Z on X with its **canonical** Betti cycle class α. The target remains UNPROVED.

## Exact construction of the canonical geometric cycle-class map (ordinary mathematics)

Take a smooth projective complex n-fold X, possibly with finitely many connected components. For an irreducible closed algebraic subvariety V⊂X of pure complex dimension n−p, let i:V_an→X_an be its analytic inclusion.

1. Even if V is singular, its regular analytic locus is canonically oriented by its complex structure. The singular locus has real codimension at least two; the complex analytic space is a locally orientable real pseudomanifold. Its oriented **Borel–Moore fundamental class** [V_an] lies in H_{2(n−p)}^{BM}(V_an,ℤ), with the correct local multiplicity. For reduced irreducible V that generic multiplicity is one.
2. Since V is a **projective** subvariety, V_an is compact. Thus the Borel–Moore class can be regarded as an ordinary singular homology class. The proper inclusion induces i_*[V_an]∈H_{2(n−p)}(X_an,ℤ).
3. The compact oriented smooth real 2n-manifold X_an admits Poincaré duality componentwise. Define the **canonical point Betti class**
   cl_X([V]) := PD_X(i_*[V_an]) ∈ H^{2p}(X_an,ℤ)/torsion → H^{2p}(X_an,ℚ).
4. For a rational algebraic cycle Z=Σ_V a_V[V] (a_V∈ℚ), define cl_X(Z)=Σ_V a_V cl_X([V]). The sum is finite and therefore gives a genuine rational-linear map on the native rational cycle space. This construction never reads a Hodge target class α or asks for an algebraic representative of α.
5. By the standard cycle-class/Hodge-type theorem, cl_X([V]) has type (p,p): the integration current of V is of type (p,p), represents the image of the rational class in de Rham cohomology, and is closed. **This relies on a known analytic-geometric theorem, not on the Hodge conjecture.** Likewise intersection compatibility is the usual fundamental-class product formula for proper intersections (with normal-bundle self-intersection when not proper).

The all-codimension fundamental-class assignment to genuine coheight-p scheme points is thus canonical in ordinary mathematics: pt_p(x)=cl_X([closure{x}]_red). The existing Lean construction `cycleClassFromPointGeometry` implements only step (4), assuming pt_p is supplied. The new all-p assembly in `GSTCanonicalPointGeometryStage2G.lean` uses these assignments but does **not** formalize steps (1)–(3) and (5) in Mathlib's singular homology API.

## Independent Fermat measurement proof

Let X_{m,d}: Σ_(i=0)^m(y_i^d−x_i^d)=0⊂ℙ^(2m+1), m≥1,d≥3. The projective gradient forces x_i=y_i=0 at a singular point, so X is smooth. For each complex d-th root of unity ζ, the plane P_ζ={y_i=ζ x_i for all i} is isomorphic to ℙ^m and lies on X; different ζ produce disjoint planes.

Let H=h^m and q=q_(m,d) be the top Chern coefficient c_m(N_{P_ζ/X}), from the exact normal sequence
0→N_{P_ζ/X}→O(1)^(m+1)→O(d)→0. Then
H·H=d, H·[P_ζ]=1, and [P_ζ]·[P_η]=q if ζ=η, 0 otherwise. These equalities are **actual intersection numbers**, and their equality with cup products of the canonical Betti fundamental classes follows from the standard cycle-class compatibility (not the Hodge conjecture).

Define Z_ζ=d[P_ζ]−H. Then Z_ζ·H=d*1−d=0, so its canonical Betti class is primitive. Its intersection with Z_η is
  Z_ζ·Z_η = d² q δ_(ζη) − d.
The rational primitive Gram matrix is therefore M=d² q I_d−dJ_d, with eigenvalues d²q (multiplicity d−1), d²(q−1) (multiplicity one). Normal-top-Chern recurrence q_0=1, q_(m+1)=1+(1−d)q_m gives q≤−1 or q≥2 for every m≥1,d≥3. Hence both eigenvalues are nonzero.

**Conclusion of this ordinary-mathematics argument:** These d *specific genuine algebraic cycles on the original Fermat X* define d linearly independent rational primitive Hodge classes for every m≥1,d≥3. The argument does not construct an arbitrary X from Fermat geometry, and does not claim these d classes span all primitive rational Hodge classes even on Fermat X.

## Verification boundaries and action items

- Lean previous certificates: [run #39022986348](https://github.com/kyo-oo/HC-PROOF/actions/runs/39022986348) verifies all-m Gram injectivity for measured rational classes; [run #39022821753](https://github.com/kyo-oo/HC-PROOF/actions/runs/39022821753) verifies Fermat coordinate smoothness/disjointness.
- New native/canonical abstraction code: `GSTFermatCanonicalPointRankBridge.lean` and `GSTCanonicalPointGeometryStage2G.lean`. Their CI runs [#39024044467](https://github.com/kyo-oo/HC-PROOF/actions/runs/39024044467) and full gate [#39023714418](https://github.com/kyo-oo/HC-PROOF/actions/runs/39023714418) were still in progress when this record was created. Do not mislabel them as green without checking.
- **Formal gap A:** Mathlib's specific analytification/Borel–Moore fundamental-class construction, Poincaré duality, cycle-class multiplicities, and Hodge-type theorem must be connected to Stage2G as Lean terms rather than external semantic arguments.
- **Original open mathematical gap B:** For an arbitrary original smooth projective X, construct enough true algebraic primitive cycles to fill **every** rational primitive Hodge direction. The Fermat source result is not a uniform all-X mechanism. Replacing that gap with an abstract full-rank field or a finite-point preimage is circular.
- **Evidence label:** Standard unconditional classical geometric construction in ordinary mathematics, Lean only at previously specified finite-generator/measurement interfaces, full all-X rational Hodge conjecture UNPROVED.

**Review / route disposition:** Independent analytic point-class semantics clarified; source-family primitive rank mathematically complete; Lean analytic implementation and original all-X primitive spanning remain the active research frontier.
