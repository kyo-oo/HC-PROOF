# GST full-arsenal geometric-surgery attack: homology-preserving integral complexification on arbitrary X
**2026-10-16. Original target, unchanged.** For every smooth projective complex X, every rational (p,p) Hodge class alpha, find m>0 and fixed M so that beta=m alpha+M h^p is integral, then construct closed integer rectifiable currents T_n in ONE fixed integral homology class PD(beta) with absolute Kähler calibration defect D(T_n)->0. A proof would establish rational Hodge on arbitrary X. **Not proved in this checkpoint.**

## Exact branch checkpoint
Base was the live mathbox/residual-zero-direct-audit-20261015 head 1caa761c617e1363a1baf4fba77f92ad0a246720. New deliverables:
* GSTComplexTangentProjectionChainObstruction.lean, and dedicated GitHub Action gst-complex-tangent-chain-projection.yml;
* GSTUniversalExternalProductCurrentSurgery.lean, and dedicated GitHub Action gst-universal-external-current-surgery.yml;
* this new mathematically detailed original-target audit.

The relevant prior GREEN Lean results on the same branch were:
* N-cohomology rank/linear-mass V3 38843813429;
* integral gap 38845762815;
* native mass integration 38846681250;
* ample-shift all-N 38854324888;
* primitive relative Hodge cohomology 38857133725;
* actual P1xP1 integer surgery 38865745138;
* exact integer chain optimizer 38866728040.

Do not assume the NEW files green until their specific latest CI runs are checked.

## GST arsenal review by REAL mathematical interface

These are the operators inspected and their precise scope:
1. waves/GSTNCohomology.lean, waves/GSTNCohomologyV2.lean, waves/GSTNCohomologyV3.lean: integer tower windows and independent RATIONAL channel-coefficient readouts. Neither integral currents nor a geometric boundary differential in arbitrary X are built by these.
2. GSTNAllChannelAmpleSaturation.lean: a universal finite *coordinate model* with all-N positive integer shifted coefficients and zero abstract signed mass defect. It does not prove these basis vectors are classes of complex analytic integral cycles on an arbitrary X.
3. GSTNPrimitiveGeometricSurgery.lean: a genuinely grounded integer homology relation of actual smooth curves on P1xP1 and integer mass/period identities. This is the sole already constructed genuine chain replacement among the inspected GST operations.
4. GSTClassicalHodgeRecoordinationArsenalCrown.lean: code projectors and natural rational vector reindexings. This doesn't move rectifiable current support or tangent planes.
5. GSTClassicalHodgeStrictCorrespondenceGeometricTransferFinale.lean and GSTClassicalHodgeClosedCorrespondenceGhostExtinction.lean: genuine algebraic correspondences send already algebraic cycle classes to algebraic classes. A nonalgebraic primitive direction cannot be created from solely existing algebraic seed classes by these transfers.
6. GSTClassicalHodgeCoherentNativeGhostObstruction.lean: ghost detector rigidity under native-descending linear actions already prevents silently treating a finite-coefficient matrix unit as a realized geometric operation.
7. GSTClassicalHodgeGeometryFirstGlobalPropagation.lean: full Hodge saturation needs the actual specific native/cohomological geometric transfer steps, not just a nonzero source. In the inspected code, the global propagation packet is STRUCTURED INPUT and is not universally constructed on any arbitrary X.
8. GSTPrimitiveMiddleHyperplaneRelative.lean: every primitive middle class on a complex 2p-fold restricts to zero on a smooth ample hyperplane and has a relative/affine-complement lift. Clearing denominators produces genuine compactly supported integral cycles in U=X\Y. Their absolute defects are not automatically small.
9. GSTNCurrentCalibrationCompatibility.lean and GSTClassicalHodgeNativeMassBridgeAudit.lean: the unweighted signed native linear augmentation is NOT the nonnegative nonlinear Riemannian area/mass functional. These cannot be identified as a geometric calibration law.
10. GSTUniversalSelfProductPrimitive.lean: actual algebraic primitive cycles on XxX exist from ample hyperplanes for every X. Their span is not all arbitrary primitive rational Hodge classes on X.

Other GST systems such as cardinal-world numeral navigation, tower waves and worldtrace arithmetic are not chain-level current constructions without an explicit, verified homology-compatible geometric realization functor. Calling this "full arsenal" means checking and using mathematically relevant interfaces, not assuming all imported theorems imply Hodge.

## New route A — try an actual pointwise complexification on a genuine projective torus

On a genuine projective abelian surface E×E with global real coordinates x,y,u,v and complex structure J, consider the EXACT two-form
   omega0 = cos(x) dx∧du = d(sin(x)du).
Its de Rham class is 0, hence of Hodge type (1,1), and d omega0=0.

The pointwise J-invariant (1,1) projection is
   P11(omega0) = (cos(x)/2)(dx∧du+dy∧dv).
Direct exterior differentiation gives
   d(P11(omega0)) = -(sin(x)/2) dx∧dy∧dv ≠0.
Therefore the pointwise complex-type projector DOES NOT commute with the exterior boundary operator even on a projective X and in the zero Hodge class. A boundary-correcting current would have to be constructed globally.

A second exact obstruction concerns TANGENT PLANE INTEGRALITY. A single simple integer oriented plane bivector
   xi=dx∧du
gets projected to
   P11(xi) = (dx∧du+dy∧dv)/2.
Its exterior square is
   P11(xi)∧P11(xi) = -(1/2) dx∧dy∧du∧dv ≠0.
This bivector is NOT decomposable (its 4x4 skew matrix has determinant 1/16), so it is not the tangent plane of any rectifiable surface, and its coefficients are fractional. Wolfram Language exact arithmetic independently verified determinant 1/16, Pfaffian -1/4, exterior-square coefficient -1/2.

GSTComplexTangentProjectionChainObstruction.lean encodes the exact rational Fourier block from these forms and proves that closedness fails and a nonzero boundary correction is necessary. A later addition proves the projected simple integer bivector is nonsimple. Lean verifies these finite rational identities, not the entire analytic torus theorem.

**Outcome:** this simplest would-be GST "complex tangency" operator FAILS both boundary conservation and geometric integer rectifiability. A proof requires a nonlocal integral boundary repair, not a pointwise J projector.

## New route B — functorially lift the ACTUAL GST integer surgery to EVERY base X

Let X be ANY smooth projective complex variety of complex dimension d, and let S be ANY closed oriented integer rectifiable 2q-current on X, with finite mass mu and calibration period pi (so original defect D(S)=mu-pi>=0). Let E=P1xP1 with normalized Fubini-Study product metric.

The actual integral P1xP1 cycles are:
   Γ = antipodal anti-holomorphic graph, mass 2, period 0;
   Δ = holomorphic diagonal, mass 2, period 2;
   F = a holomorphic ruling fiber, mass 1, period 1.

There is an INTEGRAL homology relation
   [Γ]+[Δ]-2[F]=0 in H_2(P1xP1,Z).
Thus there exists an integer 3-chain B with
   ∂B=[Γ]+[Δ]-2[F].

Form EXTERNAL PRODUCT integer currents on XxE:
   T_bad = S×(Γ+Δ),
   T_good = 2 S×F.
Since S is closed of EVEN real dimension, ∂(S×B)=S×∂B.
Hence
   T_bad-T_good=∂(S×B),
so T_bad and T_good have the EXACT SAME INTEGRAL HOMOLOGY CLASS, for EVERY X and EVERY S. This is a real all-X functorial integer boundary surgery, not an invented GST channel identity.

The product Riemannian mass and Wirtinger periods satisfy exactly
   Mass(T_bad)=4 mu,
   Period(T_bad)=2 pi,
   D(T_bad)=4 mu-2 pi;
   Mass(T_good)=2 mu,
   Period(T_good)=2 pi,
   D(T_good)=2 mu-2 pi=2 D(S).

Thus the surgery reduces absolute defect by 2mu, but leaves
   D(T_good)=2 D(S).
If S is already holomorphic/calibrated, the output is genuinely calibrated on XxE. If S is a NONCALIBRATED primitive carrier on X, the output is NOT calibrated. Tensoring the genuine GST local surgery cannot turn a missing primitive algebraic class into a holomorphic cycle.

This exact identity is kernel-formalized for the genuine P1xP1 packet and abstract source mu,pi in GSTUniversalExternalProductCurrentSurgery.lean. The geometric external-product step is justified here using standard integer current product, Künneth naturality and product Kähler metric; it is not itself a Lean theorem in the pinned repository.

**Outcome:** successfully constructed a homology-preserving, mass-decreasing integer surgery functorially for every X (on XxP1xP1). However, the all-X ORIGINAL primitive defect persists; this operation alone does not solve Hodge. This is a tested, algebraic quantitative blocker, not a claim that a different surgery is impossible.

## Route C — revisit true all-X GST integral boundary minimization

The existing research/records/20261016-gst-integral-boundary-surgery-all-varieties.md established the genuinely all-X integral class-preserving replacement T_lambda = S+∂B_lambda by minimizing
    Mass(S+∂B)+lambda Mass(B)
over integer fillings B.
Its defect approaches exactly
    gamma_X(beta)
      = inf_{[T]=beta, T integral} Mass(T) - ∫_beta omega^q/q!
as lambda↓0.

A smooth positive diffuse (p,p) representative exists after ample shift, so the relaxed REAL minimum equals its calibrated period. But no GST operator inspected gives the strict integer/real comparison
    gamma_X(beta)=0
for arbitrary higher-codimension Hodge beta. This is exactly the sought Hodge conjecture in current language, not a consequence of a generic minimization theorem.

Previous tests rule out three shortcuts:
 - Stationary/minimal current implies holomorphic: false for an explicit ample class on E×E;
 - stable calibration in n beta implies fixed-beta zero defect: false in exact integer N-lattice;
 - pointwise J-projection of closed integer current gives an integral closed complex current: false by Route A.
The functorial product surgery is quantitatively tested here: Route B.

## What would ACTUALLY be a proof on arbitrary X

Find a nonlocal operator or explicit integer fillings B_n on the ORIGINAL X (not just XxE) that, for every rational primitive (p,p) alpha and SOME FIXED m,M, satisfy ALL:
  1. ∂(S+∂B_n)=0 and integral multiplicities of all S+∂B_n;
  2. [S+∂B_n]=PD(m alpha+M h^p) in one fixed integer class;
  3. Mass(S+∂B_n) - ∫_beta omega^q/q! → 0 ABSOLUTELY;
  4. no use of prior Hodge algebraicity, an unproved geometric reachability field, or arbitrary target-cycle witness.

Current exact verdict: **NO universal class-preserving zero-defect sequence has been constructed.** The new direct routes A and B are executed and produce checkable geometry and clear constraints; route C is the existing strongest all-X operator but still requires independent proof of gamma_X(beta)=0.
