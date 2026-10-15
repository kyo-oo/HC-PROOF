# Mathbox GST — K3 diagonal primitive and original unconditional Hodge priority

**Date**: 2026-10-15
**Base**: 66e4f0bfed4f2c74cb3cd3825eae0c2911e75c88 (mathbox/bd23-single-operator-charge-wedge)
**Branch**: research/mathbox-k3-diagonal-primitive-20261015

## Original goal — unchanged

For ALL smooth projective complex X, ALL codimensions p, and ALL rational
(p,p) Hodge classes alpha, construct an actual rational algebraic cycle
Z with cycleClass(Z)=alpha. This universal target has not been proved.

## Previously developed GST power — read, NOT discarded

- HodgeConjecture.lean states the literal Stage-2G classical target.
- GSTClassicalHodgeGSTPlaneAxiomStatus.lean proves unconditional INTRINSIC
  GST plane completeness, not geometric algebraicity.
- GSTClassicalHodgeFullCorrespondenceGSTPlaneCompletion.lean ties
  geometric correspondence cyclicity to ghost-probe pairing totality.
- GSTClassicalHodgeOmniversalConstructorGraph.lean makes true native
  cycle-to-Hodge events explicit and shows its global closure is equivalent
  to the actual conjecture.
- GSTClassicalHodgeCommonClassPlaneReduction.lean supplies minimal
  GhostSeedTargetStrictClosure and precise separator trace mismatch.
- docs/GST_HODGE_PLANE_REALIZATION_LAW.tex isolates the strict
  bi-finite common-carrier condition left*(a)=right*(beta_target),
  normalized right trace, and native point-cycle naturality.
- CM–NM and Kuga–Satake/Clifford modules have already produced a
  substantial forward correspondence framework.

Therefore the priority is not ordinary hyperplane algebra or re-proving
rank-two linear independence. It is constructing NEW, independently
geometric primitive directions and testing their effect on true GST
strict correspondence/ghost-completeness arguments.

## Executed geometric breakthrough on a new non-divisor source

Let S be a smooth complex projective K3 surface with ample divisor h
and d=integral_S h^2>0. Put Y=S×S and let H=h_1+h_2.
The diagonal Delta_S, the two point-section cycles U,V, and the
external product B=h×h are actual algebraic codimension-two cycles.

Define the rational algebraic cycle

    P_h = Delta_S - U - V - (1/d) B.

Let A=[point]×h and T=h×[point] in H^6(Y,Q).
Classical diagonal projection and Kunneth/cup identities yield

    H⋅[Delta_S]=2(A+T)
    H⋅[U]=A
    H⋅[V]=T
    H⋅[B]=d(A+T).

Consequently H⋅cl(P_h)=0: an explicit primitive (2,2) class.

The K3 transcendental rational subspace T(S)=NS(S)_Q^orthogonal
has positive dimension (b2(S)=22, Picard rank <=20) and
nondegenerate rational intersection form. Choose u,v in T(S)
with q=integral_S u⋅v !=0. Then the genuine geometric intersection
functional ell(alpha)=integral_Y alpha⋅(u×v) satisfies

    ell(cl(Delta_S))=q,
    ell(cl(U))=ell(cl(V))=ell(cl(B))=0.

Hence ell(cl(P_h))=q !=0. Rational divisor-word classes on S×S
are invisible to this functional, so cl(P_h) is primitive, nonzero,
and OUTSIDE the divisor-generated Hodge subspace.

This is unconditional classical GEOMETRY for K3 self-products;
it does not establish primitive algebraicity on an arbitrary X.

## Arbitrary Picard rank correspondence projector

Take rational divisor basis D_i of NS(S) and the rational intersection
dual basis E_i (dual exists because the NS pairing is nondegenerate).

The algebraic correspondence Pi_NS = sum_i D_i×E_i acts on H^2(S,Q)
as the projector onto NS. Its complement, using the ACTUAL diagonal
identity correspondence, gives

    Pi_tr = Delta_S - ([point]×S) - (S×[point]) - Pi_NS.

On rational cohomology this is a genuine algebraic correspondence
projecting onto T(S) in degree 2 and killing the other K3 cohomology
sectors. This is a source of geometry not provided by abstract
pointwise GST matrix-unit closure.

The associated arbitrary-finite-rank projector algebra and
idempotence have been machine verified.

## Actual files and proof status

- GSTK3DiagonalPrimitive.lean, GitHub Actions 38745893192 SUCCESS:
  native cycle formula, primitive cancellation, independent non-divisor
  intersection detector; assumptions specify genuine cup identities.
- GSTK3TranscendentalProjector.lean, GitHub Actions 38746215575 SUCCESS:
  finite NS intersection-dual projector, complementary idempotence,
  orthogonal-survival theorem.
- GSTK3DiagonalActualStage2G.lean: embeds the explicit construction into
  ACTUAL Mathlib scheme codimension-two cycle submodule and Stage-2G
  rational Betti/Hodge carrier. It requires a concrete
  GenuineK3ProductDiagonalPacket giving the real K3 cup identities;
  this type is NOT constructed from arbitrary X.
- GSTK3PrimitiveOmniversalGraph.lean: one NEW actual primitive algebraic
  cycle yields a genuine reachable Hodge vertex of the USER'S EXISTING
  GST omniversal constructor graph. No invented reverse Hodge-to-cycle
  arrow; total ghost extinction is not proved.
- Focused GitHub gates for the latter two modules must be checked at
  the exact final successful commit before claiming verification.

## Exact limiting test — no renamed assumptions

An algebraic correspondence preserves the image of the genuine native
cycle-class map when applied to actual algebraic source cycles. Thus the
projector Pi_tr kills divisor seeds rather than somehow producing an
arbitrary previously unknown primitive class from them.

Likewise the diagonal Delta_X is algebraic on X×X for EVERY X, but its
identity action on an arbitrary rational primitive Hodge alpha DOES NOT
construct a rational algebraic cycle representing alpha: contracting its
Kunneth tensor against alpha uses alpha itself as the unproved algebraic
input. There is no reverse cycle-class map in the established geometry.

The strongest remaining original implication is still:
construct a ghost-target STRICT geometric correspondence carrier with
independently verified left/right pullback relation, finite trace and
native point compatibility for EVERY arbitrary smooth projective
variety and EVERY surviving ghost-detected rational Hodge sheet,
without assuming that sheet is algebraic.

This precise statement, not a new special-variety example or a fresh
conditional axiom, is the active absolute priority of GST research.

## Verification/claim firewall

Successful Lean compilation of the standalone algebraic projector verifies
the exact stated theorem, NOT the underlying K3 scheme analytic comparison.
Any eventual universal proof must also construct the actual rational
Hodge/cycleClass geometry in the pinned Stage-2G semantic package;
GSTClassicalHodgeStage2GSemanticRigidity supplies a zero-cycleClass
countermodel to claims formulated over its arbitrary cycleClass field.

No original target was weakened or claimed solved.
