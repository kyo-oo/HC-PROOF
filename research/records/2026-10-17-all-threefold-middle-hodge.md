# Mathbox: all-X threefold codimension-two Hodge construction

- **Date:** 2026-10-17
- **Kind:** constructive proof attempt with an exact interface-bound result
- **Target:** All rational primitive (p,p) Hodge classes on every smooth projective complex X have genuine algebraic representatives through the canonical cycle-class map.
- **Hypotheses and types:** V a smooth projective complex threefold, H its genuine Stage2G Hodge data, G its cycle-class geometry, `P : GeometricHigherLefschetzData G 3` with Hard Lefschetz, `h11 : DivisorsRepresentHodge11 H`, and `hLZero : P.primitiveTest=LinearMap.id` (geometric fact h^(3-3)=h^0=1). The theorem concerns rational (2,2) classes in H⁴(V,ℚ) and codimension-two rational native algebraic cycles.
- **Active conventions:** Ample Lefschetz operator h cup; cup h^0 acts as identity. A native divisor D is a rational sum of genuine codimension-one algebraic cycles; `P.nativeCupH D` is their actual ample divisor intersection.
- **Current dependency/evidence status:** Lean declarations pushed; newest GitHub Actions compilation status must be read separately. Structural inputs P/h11 are independent classical geometry laws, not primitive-Hodge spanning assertions. The Stage2G analytification/canonical cycle-class construction is supplied semantically and is not discharged in this file.
- **Nearest prior attempt and first failure:** `GSTUniversalCodimensionTwoPrimitiveExtraction.lean` already decomposes arbitrary rational (2,2) classes into an actual algebraic correction plus a primitive remainder, but for d≥4 it cannot show the remainder algebraic. In d=3 the primitive-test exponent becomes ZERO and the remainder is identically zero.
- **Route:** Prove the entire rational (2,2) Hodge target for every smooth projective threefold rather than only constructing isolated primitive source families.
- **Mechanism and distinctness from prior routes:** For a threefold, Hard Lefschetz L:H²→H⁴ is an isomorphism. Given α in H⁴ of Hodge type (2,2), choose β=L⁻¹α in H² of type (1,1). Lefschetz (1,1) constructs an algebraic divisor D with cl(D)=β. The genuine native intersection h⋅D has class α. The earlier arbitrary-d primitive residual is zero because L^0=id. No higher-codimension Hodge conjecture is an input.
- **Changed input:** Specialize the actual all-X geometric Lefschetz machinery at threefold dimension and enforce the independently known degree-zero identity.
- **Success criterion:** Lean derives an actual native codimension-two cycle for every rational (2,2) Hodge class with no primitive spanning hypothesis and the correct d=3 Hodge grade. The overall original goal requires the same result across all X and p, not just this subcase.
- **Failure/no-go criterion:** Using surjectivity of the desired codimension-two cycleClass map, or omitting the degree-zero identity, would make the proof circular or incomplete.
- **Cheapest decisive check:** `lake build GSTAllDimensionalCodimTwoPrimitive` via existing GitHub workflow and inspect sorryAx diagnostics. The proof is a direct specialization of already compiled `algebraicLefschetzCorrection_test`.
- **Attempt outcome:** Theorems `threefold_primitive_hodge_remainder_zero` and `every_threefold_hodge_two_class_has_native_cycle` committed in `GSTUniversalCodimensionTwoPrimitiveExtraction.lean`. `P.primitiveTest=LinearMap.id` is an independently typed geometric statement; the code does not assume `α=cl(Z)`.
- **Route disposition and scope:** Threefold subcase mathematically established from standard Hard Lefschetz, Lefschetz (1,1) and geometric h^0=id. The original arbitrary-X/primitive-middle target remains OPEN, with first gap appearing in higher dimensions.
- **Continuations:** Tried: exact all-X d=3 reduction and native cycle construction. Untested: d≥4 primitive remainder, requiring actual new independent geometric classes outside the Lefschetz image. Other source/correspondence routes stay open.
- **Evidence label:** Conditional formal theorem on standard geometric Hodge interfaces, independent classical argument. Latest source CI pending as of record creation. Universal all-varieties Hodge claim unproved.
- **Review and freshness status:** Self-reviewed; branch `research/gpt6-native-point-primitive-span-20261017`; check GitHub Actions workflow `gst-universal-codimension-two-primitive.yml` at exact source commit, not an older green run.
- **First unresolved or failed implication:** For d≥4 there may be rational primitive (2,2) classes which are not known to be algebraic; h^0=id no longer applies because the primitive test is a positive power of h.
- **Strongest surviving statement:** Every rational (2,2) Hodge class on every smooth complex projective threefold is represented by an actual rational algebraic codimension-two cycle, assuming correctly instantiated classical Hard Lefschetz, Hodge (1,1), cup, and canonical cycle-class geometry.
- **Artifacts and commands:** Lean source `GSTUniversalCodimensionTwoPrimitiveExtraction.lean`, existing exact correction lemma `algebraicLefschetzCorrection_test`, dedicated GitHub workflow `.github/workflows/gst-universal-codimension-two-primitive.yml`.
- **Next unresolved question:** Construct non-Lefschetz representative cycles for arbitrary primitive (2,2) directions on every smooth projective fourfold, then general p,d; this is the original target's first genuinely new Hodge obstruction.
- **Uniform route or obstruction:** Dimension three is not a general induction argument; the degree-zero Lefschetz operator becomes positive-degree for higher dimensions.
- **What another bounded case would discriminate:** For a fourfold whose (2,2) rational Hodge fiber has a primitive direction outside the known algebraic sources, produce an actual irreducible surface with a provably nonzero pairing with it, then certify the canonical fundamental class.

## Proof structure

```text
α ∈ H⁴(X,ℚ) ∩ H²,²
  β = (h cup)⁻¹ α ∈ H²(X,ℚ) ∩ H¹,¹  [Hard Lefschetz, dimension 3]
  cl(D) = β                           [Lefschetz (1,1)]
  Z = h ⋅ D, a genuine algebraic curve [scheme intersection]
  cl(Z) = h cup cl(D) = α              [canonical cycle-class naturality]
```

No statement in this document asserts all primitive Hodge classes on arbitrary higher-dimensional X are algebraic.
