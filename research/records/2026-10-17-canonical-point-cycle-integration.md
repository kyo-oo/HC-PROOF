# Mathbox route: from native irreducible point cycles to canonical geometric Betti rank

**Date:** 2026-10-17. **Authoritative original target:** for all smooth projective complex X, all codimensions p, all rational primitive (p,p) classes α, actually construct a native rational algebraic cycle on the original X whose canonical singular Betti class equals α. **Status: OPEN.**

## Actual objects and source/target

- V is a smooth projective complex scheme with analytification A; p is an arbitrary codimension. `CodimensionPoint V.X p` denotes true points of scheme coheight p, representing irreducible codimension-p subvarieties, not symbols in a formal vector space.
- `codimensionPointCycle V.X p x` is the genuinely native algebraic cycle for a point x. A supplied `Hpower : codimensionCycles V.X p` encodes the actual hyperplane-power cycle on the specific geometric carrier; no unknown Hodge target α is supplied.
- `pt : PointBettiClass p A` assigns a cohomology class to every irreducible codimension-p point. `cycleClassFromPointGeometry p A pt` is **constructed** by linear extension through the exact finite native-point presentation; on each point generator it is pt. Existing `suppliedCycleClass_eq_geometric` identifies it with Stage2G's H.cycleClass if their point classes coincide, but that pointwise identification is not yet established analytically.
- The concrete source family on a Fermat hypersurface has `Z_i = d*codimensionPointCycle(P_i) - Hpower`. Its true geometric intersection Gram formula is **specified** at the point-cycle level, not obtained by choosing an arbitrary family of rational target vectors.
- Independent measurement `M : RationalSingularCohomology A (2*p) →ₗ[ℚ] (Fin d → ℚ)` is intended to mean intersection against the d actual primitive plane classes. The concrete entry identity says `M(class(Z_i))_j = d²*q_(m,d)*delta(i,j)-d`, q_(m,d) the top normal Chern coefficient. This is classical geometry, but the formal code has not constructed the analytic cap pairing satisfying it.

## The executable route

- File `GSTFermatCanonicalPointRankBridge.lean` (created this round) imports existing canonical point-class rigidity and all-dimensional Fermat rank. The theorem `genuine_point_generated_fermat_rank` deduces that any Q-linear relation among actual point-generated Betti classes has zero coefficients from this entrywise geometric Gram.
- The reduction from entrywise comparison to a full matrix equation is proved using the linear map and finset-sum identities, not assumed.
- An integrated workflow `.github/workflows/gst-pinned-hodge-geometric-integration.yml` was created to compile this new proof **together** with `GSTClassicalHodgeGeometricCycleClassPointRigidity`, `GSTActualXHodgeResidualProjection`, `GSTUniversalCodimensionTwoPrimitiveExtraction`, and `GSTClassicalHodgeExactClayStatement`. The workflow rejects diagnostic `sorryAx`, saves an artifact, and is scoped to the research branch. Initial run `https://github.com/kyo-oo/HC-PROOF/actions/runs/39023714418`; check its exact conclusion before labeling verified.

## Attempt evaluation

**First missing implication:** There is still no *general* geometric operation producing a set of algebraic codimension-p cycles with enough independent canonical Betti classes to span all rational primitive Hodge directions of arbitrary X. Supplying arbitrary family entries satisfying a determinant inequality on each X would merely assume the target's key geometric rank question. The Fermat cycle family gives actual source existence on a very special infinite family, not on arbitrary X.

**Second missing implication:** The analytification fundamental class of every codimension-p subvariety is not instantiated as the pt assignment inside Stage2G or proven to be the supplied cycleClass. Algebraic finite-point reconstruction proves *uniqueness*, not analytic *existence* of those fundamental classes.

**Third missing implication:** The explicit intersection comparison (hEntry) must be discharged by actual projective intersection and canonical cohomology operations, independent of choosing the answer. Its generic formal statement is a mathematical bridge, not a Hodge solution.

**Strongest honest result:** Under independently geometric point-class and intersection identities, d actual native algebraic cycles generate d linearly independent rational Betti classes on each smooth Fermat 2m-dimensional hypersurface (d≥3, m≥1). This follows from the all-m uniform sign induction and a new scheme-point-native cohomology map interface; no rational Hodge target preimage or universal algebraicity is assumed.

**Evidence label:** Mathematical reduction in Lean source; integrated kernel status pending at record creation. Source rank determinant verified in [run #39022986348](https://github.com/kyo-oo/HC-PROOF/actions/runs/39022986348); canonical scheme/cohomology comparison and all-varieties target open.

**Next research route:** Derive an all-X algebraic correspondence whose actual primitive cycle classes span the complete rational Hodge primitive space *without building in a rank/surjectivity premise*, and formally instantiate canonical point fundamental classes and cup products. This cannot be replaced by a second conditional full-rank theorem.
