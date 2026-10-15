# GST Graph V2, CM–NM and primitive geometry — upgraded bridge

Date: 2026-10-15. Authorship deliberately anonymous.
Branch: mathbox/bd23-single-operator-charge-wedge.
Original target: algebraic representatives of all primitive rational Hodge classes on arbitrary smooth projective complex varieties. NOT YET PROVED.

## Existing graph identified

1. GSTGraphV2Production.lean: historical unbounded x4/base3 arithmetic production sheet.
2. GSTGraphV2ArithmeticOmniversalRealization.lean: actual arithmetic node carrier, horizontal and vertical causal events, legacy seven-axis observable.
3. GSTGraphV2OmniversalCore.lean: sector-aware graph, finite certified paths, all-index causal closure, event morphisms.
4. GSTClassicalHodgeOmniversalConstructorGraph.lean: actual codimension-point cycles, rational Betti/Hodge nodes and geometric cycle-class edges, with NO arbitrary Hodge-to-cycle reverse arrow.

These are preserved, not replaced. The new CM-NM geometric extension is GSTGraphV2CMNMPrimitiveUpgrade.lean (focused Lean CI 38713065733 SUCCESS). The coupled arithmetic plus true geometry extension is GSTGraphV2CMNMCoupledUniverse.lean (separate CI; inspect current result before using).

## The user's Equations (4) and (5) as precise typed mathematics

Equation (4) proposes A_g(s) ± GST infinite cosmology ⊕ G_a × primitive Hodge classes. The symbols mix different types; A_g, G_a, direct sum, signed operation and Hodge primitive tensor require real definitions. The upgrade interprets their useful arithmetic-to-geometry action *without pretending this is an already proved equality*.

For Gaussian rational x,y let u_m=x^(m+1)-y^(m+2). Define the fixed rational CM readouts r_m=Tr_Q(i)/Q (1/u_m) and s_m=2 Im(1/u_m). Given two actual projective scheme morphisms f,g : X→X and one native codimension-p algebraic cycle Z, build the actual rational algebraic cycle

Z_NM = r_m f_*Z + s_m g_*Z.

There is a **proved forward cycle-class identity**:

cl_p(Z_NM) = r_m cl_p(f_*Z) + s_m cl_p(g_*Z).

The new graph has a genuine native-cycle event creating Z_NM; the old graph events embed identically; cycle-to-Hodge is allowed only for an actual algebraic cycle. Nothing here selects a preimage of an arbitrary Hodge target.

Equation (5) proposes lim_{x→infinity} ℒ(n^x) tensor primitive cycles. The function ℒ, topology, normalization and target are not specified. Wolfram evaluated the unnormalized 3^x limit as +Infinity. Therefore the safe precise interpretation is the EXISTING indexed closure-union identity:

Closure(union_n Seed_n) = union_n Closure(Seed_n).

This follows for arbitrary index sets and retains all finite event stages without assuming a convergence or finite terminal dimension. It does NOT turn all Hodge classes algebraic automatically.

## Wolfram check of prior all-codimension projective primitive formula

For X dimension d=6 and p=3, existing all-dimensional product polynomial (with u and t hyperplane classes on X and P³) has coefficients {1,-4,10,-20}:

P=u³-4u²t+10ut²-20t³.

Exact Wolfram polynomial ideal reduction gives the remainder of (u+t)^4 P modulo <u^7,t^4> equal to ZERO. This independently tests the existing generic formula derived from the negative-binomial identity. It does not formalize native projective Betti cycle-class comparison for an arbitrary X.

Gaussian CM test: (1+i)^2-i^3=3i has ZERO real trace, and a nonzero imaginary channel; therefore retaining both rational CM channels is essential.

## Geometric primitivity versus Hodge algebraicity

An arbitrary projective pushforward need NOT preserve primitiveness with respect to an arbitrary polarization. Additional certified Lefschetz compatibility is required. Therefore the graph creates actual native cycles, not arbitrarily declared primitive cycles.

The upgraded graph proves all its events preserve actual algebraicity. The equality between its Hodge reachability closure and genuine existence of a native cycle is also verified. It is a structural FIREWALL, not a universal Hodge proof.

To finish the original target one must construct enough independently algebraic primitive Hodge directions for arbitrary smooth projective X, using true primitive-preserving mixed correspondences and a separately proved non-circular rank/surjectivity statement.

Status: Graph native CM-NM upgrade green. Coupled infinite arithmetic-Hodge graph remains subject to its focused Lean CI. No local Lean installation and no public internet search.