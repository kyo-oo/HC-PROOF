# Mathbox 2026-10-16: GST integer boundary surgery aimed at the universal Hodge geometric replacement
Checkpoint base 9f0c4943f612990eb48bfb77095e4222044b2e63.
Original exact goal: for EVERY smooth projective complex X, EVERY rational (p,p) Hodge class alpha, produce FIXED m>0,M>=0 and closed integral rectifiable currents T_n with [T_n]=PD(m alpha+M h^p) and absolute Wirtinger defect D(T_n)->0. This is equivalent to rational Hodge algebraicity; this route does NOT claim to prove it.

## Existing GST mechanisms genuinely inspected

1. waves/GSTNCohomology.lean, V2, V3: finite tower-hole/window readouts, independent rational coordinates. **These objects are not topological singular chains** and have no integral boundary operator with ∂²=0.
2. GSTNAllChannelAmpleSaturation.lean (CI success 38854324888): all-N ample shifts yield zero "calibration" in an INTEGER-WEIGHTED CHANNEL model. The channel mass is not the current mass on arbitrary X. Its vector coordinates do not carry a cycle-class map with target every Hodge direction.
3. GSTClassicalHodgeProjectivePointTransport.lean: actual scheme pushforward on already algebraic codimension-p point cycles. No action on a nonalgebraic primitive rectifiable current.
4. GSTClassicalHodgeProjectiveDefectTransport.lean: transports a *fibered cycle-class defect* (not Kähler mass minus ω-period), preserves the zero-defect property for suitable projective self-transports, and does NOT construct a method shrinking a positive Kähler calibration defect.
5. GSTClassicalHodgeNativeOperatorCohomologyRealization.lean: the ambient operator is descended from the existing algebraic image, using a rational projection from ambient Betti space onto that image. Under kernel stability it maps existing cycle classes into existing cycle classes. No inverse for an arbitrary Hodge class appears from this extension.
6. GSTClassicalHodgeGeometryFirstGlobalPropagation.lean: the full-Hodge conclusion is conditional on GeometryFirstGlobalPropagation, including native Lefschetz transport and a GeometryFirstTwoGenerator for every Hodge basis pair. These are not constructed on arbitrary X by the inspected file.
7. GSTK3GeometricSourceToArbitraryX.lean: actual K3 source cycles transport to arbitrary X if a Hodge/Chow retract is supplied. The universal existence of such a retract is not derived.

Conclusion: GST is genuinely being used here, but its existing operators do NOT already implement the requested homology-preserving, mass-defect-decreasing geometric current surgery. Creating a meaningful chain-level transport is the active work, not pretending that the earlier fibered defect is Wirtinger calibration.

## GST new geometry: integer N-current boundary surgery

File GSTNPrimitiveGeometricSurgery.lean: an explicit rationally honest, integer-multiplicity model linked to ACTUAL geometric curves on X=P1×P1.

Let A denote the antiholomorphic antipodal graph Γ, D the holomorphic diagonal Δ, F the holomorphic ruling fiber (P1×{pt}). Their integral homology classes, areas, and Kähler periods are:

     current        PD in (A_h,B_h)   mass     ω-period
     Γ               B_h-A_h            2           0
     Δ               A_h+B_h            2           2
     F               B_h                1           1

A geometric cycle with integer multiplicities (a,b,c) in these three directions has integral H_2 coordinates
   homology(a,b,c)=(-a+b, a+b+c),
period
   P(a,b,c)=2b+c,
and for generic distinct sheets (no 2-dimensional overlap)
   Mass(a,b,c)=2|a|+2|b|+|c|.

The fundamental integral geometric relation is

   [Γ]+[Δ]=2[F]  in H_2(X,Z).

Hence, for any integer k, the *actual homology-preserving surgery* is

    R_k(a,b,c)=(a-k,b-k,c+2k).

Exact integer identities:
   homology(R_k T)=homology(T),
   P(R_k T)=P(T).

For nonnegative sheets a,b,c and 0≤k≤min(a,b):
   Mass(R_k T)=Mass(T)-2k,
   D(R_k T)=D(T)-2k.

In particular, if 0≤a≤b and c≥0, choosing k=a eliminates ALL anti-graph contributions:
   D(R_a T)=0
   homology(R_a T)=homology(T).

The concrete replacement is
    T_bad=(1,1,0),   Mass=4, P=2, D=2;
    T_good=(0,0,2),  Mass=2, P=2, D=0.

Both represent PD(2B_h). The output is the sum of two actual positively oriented holomorphic ruling curves, not a symbolic mass coincidence. Since the homology difference is ZERO IN INTEGRAL H_2, it is the boundary of an integral singular 3-chain B. That filling is not explicitly constructed as a current in Lean; only the homology and numerical effect are formalized.

### What the result DOES and DOES NOT do

This is a FAMILY of homology-preserving zero-defect surgeries (not just one triple). It supplies an actual geometric realization for every nonnegative configuration with enough diagonal sheets to cancel anti-graphs on P1×P1. It does NOT supply an analogous null-homologous surgery relation on arbitrary smooth projective X, and no arbitrary nonalgebraic alpha is realized by an algebraic source in the module.

## New all-X positive replacement: global integral mass minimization

Given a compact Riemannian smooth projective X with fixed integral 2q-homology class beta, the set of closed integral rectifiable currents representing beta is nonempty by triangulation. The standard integral-current compactness and homological persistence argument supplies an AREA MINIMIZER T_beta within this single integer homology class.

For every starting primitive-plus-ample current S in beta,
   [T_beta]=[S]=beta,
   Mass(T_beta)≤Mass(S).
Because c=ω^q/q! is closed, the calibration period T(c) depends only on beta, so
   D(T_beta)≤D(S).

This is a genuine all-X, integral-class-preserving, globally mass-nonincreasing GEOMETRIC REPLACEMENT. Unlike a local mean-curvature flow, it may jump through nonlocal fillings and cannot be blocked solely by a stationary initial varifold.

Define the fundamental all-X geometric "integrality gap":
   gamma_X(beta)=Mass(T_beta)-<beta,c>≥0.

Every minimizing current has D=gamma_X(beta). It is calibrated (and algebraic, by calibrated-holomorphic regularity and Chow) IFF gamma_X(beta)=0.

Rational Hodge type supplies a smooth diffuse POSITIVE current with the SAME *real* class whose mass equals <beta,c>; it does NOT imply the integer integral minimizer reaches that real relaxed value. The strict inequality gamma_X(beta)>0 remains logically possible from the present arguments. No theorem in the inspected GST modules excludes it for every Hodge beta.

This yields a direct absolute-defect research target: prove gamma_X(m alpha+M h^p)=0 for some fixed m,M by a new Hodge-specific geometric estimate. Proving precisely that would establish the rational Hodge conjecture.

### Universal monotonicity across ample shifts (new exact property)

Let Z_h be a positive holomorphic complete intersection of p hyperplanes in X, giving a closed integral calibrated current with [Z_h]=PD(h^p). For a fixed m and beta_M=m alpha+M h^p, define gamma_M=gamma_X(beta_M).

For every integer N≥0 and T in beta_M,
   T+N Z_h lies in beta_{M+N}, and by mass subadditivity
   D(T+N Z_h) ≤ D(T)+D(N Z_h)=D(T).

Taking infima:
   0 ≤ gamma_{M+N} ≤ gamma_M.

So the genuine integral absolute-defect optimum is MONOTONE NONINCREASING as the ample-shift coefficient grows. For the P1×P1 example alpha=B_h-A_h, gamma_0>0 (pure primitive has zero ample degree but is nonzero), while gamma_1=0 because beta_1=2B_h is represented by 2F.

**Important quantifier warning:** monotone nonincrease does NOT imply that gamma_M=0 for any finite M. Even gamma_M→0 as M→∞ would be insufficient for a sequence in ONE FIXED homology class. This is a *stronger constraint to exploit*, not the missing universal Hodge theorem itself.

## Three actual routes tested against decisive failures

A. Native GST projective transport, correspondences, matrix units:
   maps existing algebraic cycles to existing algebraic cycles;
   cannot create a primitive class missing from the native image.
   Inspect GSTClassicalHodgeNativeOperatorCohomologyRealization.

B. Local geometric mean curvature descent:
   earlier exact E×E example contains a stationary noncalibrated
   integral varifold IN AN AMPLE HODGE CLASS. Pure MCF can stop at
   the wrong stationary point. Needs NONLOCAL topology-changing surgery.

C. Global integral-current minimization + GST integer boundary surgery:
   fully valid for arbitrary X as homology-preserving replacement,
   with explicit strict zero-defect geometry for a FAMILY on P1×P1.
   Remaining precise gap is independent Hodge-specific proof
   that integral minimizer has gamma_X(beta)=0 for some shift.
   This is NOT yet settled.

## Active next geometric mechanism (not a claim of proof)

Find, for arbitrary primitive middle rational Hodge alpha, a certificate
of a NULL-HOMOLOGOUS INTEGRAL (2q+1)-dimensional surgery B with
    [T+∂B]=[T]=beta,
    Mass(T+∂B) ≤ Mass(T) - eta(T),
where eta(T)>0 for any noncalibrated globally minimizing current
in the target Hodge class, WITHOUT importing algebraicity of alpha.
The existence of this nonlocal move is the first genuinely unproved
geometric implication. A naive uniform descent lemma is inconsistent
with the non-Hodge Kähler-angle lower-bound examples, so the proof
must explicitly use the Hodge condition on alpha.

Before promotion to theorem, reconstruct the actual B, its integer
multiplicities, homology and lower mass against each tangent-plane
angle. DO NOT add a "surgery packet" whose fields already assert
the all-X statement and then claim victory when Lean compiles.

### Verification

N independent rank, integer ample saturation and earlier relative
cohomology modules have green CI at their pinned runs. New
GSTNPrimitiveGeometricSurgery.lean and dedicated CI run
38865178608 were submitted in this turn; their final verification
status must be rechecked before labeling the new Lean theorem GREEN.

**Original all-X rational Hodge fixed-class calibrated-current theorem is not yet proved.**
