# Mathbox + Wolfram: N-cohomology, fixed-homology integral currents, and Hodge zero residual
2026-10-16

## THE ORIGINAL TARGET (unchanged)

For every smooth projective complex X, all p, every rational primitive
(p,p) Hodge class alpha, construct a SINGLE positive shift
    beta = m alpha + M h^p (integral modulo torsion)
and integral rectifiable closed currents T_n representing PD(beta)
with absolute Kähler calibration defects D(T_n) -> 0.

If this succeeds, integer compactness and calibrated-current analyticity
produce an effective algebraic representative of beta. Subtract M h^p
and divide by m to represent alpha; the GST residual r_alpha vanishes
and Q(r_alpha,r_alpha)=0.

**Research verdict for the universal quantifier: unproved.** This file
records the concrete N-cohomology upgrades and explicit geometric
discrimination, not a substituted theorem.

## What was actually upgraded in N-cohomology (Lean-checked)

Original source files:
* waves/GSTNCohomology.lean
* waves/GSTNCohomologyV2.lean

Upgrade, on the independent Mathbox work branch:
* waves/GSTNCohomologyV3.lean
* GitHub Actions run 38843813429 — SUCCESS
* GSTNCurrentCalibrationCompatibility.lean — integrates the upgrade
  with the repository's actual native algebraic-cycle mass; its
  dedicated CI outcome must be checked separately (run 38844187690).

The old V2 canonicalNCohoBasis takes the same value for every index.
This never established linear independence of holes. The new
independentHoleBasis i j = delta_ij on Q^(Fin s.holes) gives:
    sum_i c_i delta_ij = c_j,
and a zero linear combination implies all coefficients zero.

The genuine original tower amplitude,
    waveIIAmplitude R (s.channel i),
is now an actual coordinate vector in that basis, not a declaration of
topological Betti rank in an unrelated complex projective variety.

The second upgrade proves that for any rational-linear
    M: signed native cycles -> Q,
    (forall Z, M Z >= 0) => (forall Z, M Z=0).
For M nonzero there is Z with M Z < 0.
Thus nativeCycleMass from GST classical Hodge cannot equal nonnegative
rectifiable-current mass on all signed cycles. The contradiction is
mathematically structural and verified, not a CI tool issue.

## Wolfram computation: exact middle-dimensional projective geometry

On X = P^2 x P^2, h=A+B, choose primitive r=A^2-AB+B^2.
In the Chow ring Q[A,B]/(A^3,B^3):
    h*r=0; integral_X r*h^2=0; integral_X r^2=3.
Shift r by h^2:
    beta=h^2+r=2A^2+AB+2B^2,
which is effective on this *cellular* X.
Wolfram Language coefficient calculation verifies the above.
It is NOT a universal construction for non-cellular X.

## GENUINE integral-current geometric test: projective abelian surface

Let E=C/(Z+i Z) be the standard square elliptic curve, a projective
complex curve; X=E x E with coordinates (x,y;u,v) mod Z^4,
flat product Kähler form
    omega = dx ^ dy + du ^ dv.
Take C=E x {0}. For a real epsilon, graph the smooth map
    f_epsilon(x,y)=(epsilon sin(2 pi x),0) mod Z^2
to obtain the closed, oriented, integer rectifiable current T_epsilon.

Every graph T_epsilon is HOMOLOGOUS to C: f_epsilon is homotopic
to the constant map by scaling epsilon.
A graph is holomorphic only at epsilon=0 (for these functions).

Its induced Riemannian area element is:
    sqrt(1+4 pi^2 epsilon^2 cos^2(2 pi x)) dx dy.
And its Kähler period is fixed:
    integral_(T_epsilon) omega = 1.

Consequently, for epsilon!=0,
    D(T_epsilon)
      = integral_0^1 (sqrt(1+4 pi^2 epsilon^2 cos^2(2 pi x))-1) dx
      > 0,
but
    0 < D(T_epsilon) <= pi^2 epsilon^2 -> 0.

The upper bound follows from sqrt(1+t)<=1+t/2 and
integral_0^1 cos^2(2 pi x) dx=1/2.
Wolfram Language EXACT Taylor-integral computation returned
    pi^2 epsilon^2 - 3/4 pi^4 epsilon^4
through order epsilon^4.

**Crucial new test result:** Fixed-integral-class current defect is
NOT quantized with any uniform positive lattice spacing even
on a smooth projective complex variety. Therefore the GST N-wave
interference law (integer source multiple of 56) cannot be
substituted directly for calibrated-current defect via a fixed
nonzero rescaling: the graph sequence disproves that identity.
An actual geometry-aware analytic comparison would have to map
the window signal to current tangent geometry and correctly
reproduce its continuous defect behavior.

This is not a counterexample to the Hodge conjecture:
C is an algebraic curve and its class is calibrated by T_0.

## A general geometric criterion, not an automatic existence proof

For a fixed integral homology class beta define
    delta(beta) = inf_{T closed integral, [T]=PD(beta)}
                   (Mass(T) - int_T omega^q/q!).

The calibration inequality gives delta(beta)>=0.
On compact X integral currents in the fixed homology class have a
mass-minimizer by Federer-Fleming compactness (provided the class
has at least one integral current representative).
The calibration integral is fixed, so the infimum of defect is
attained. Thus:
    delta(beta)=0
       if and only if
    beta has an effective holomorphic/analytic cycle representative.
On projective X these are algebraic by Chow's theorem.

So the requested existence of an approximate sequence T_n in one
integral class is already equivalent to effectiveness of THAT shift.
This analytic characterization does NOT prove that every rational
Hodge class admits an effective shift.

For primitive r itself, degree integral_X r*h^(d-p)=0.
In the P^2 x P^2 case, since integral_X r^2=3, choose a smooth closed
4-form psi representing r with finite positive comass C>0. Any
integral 4-cycle T representing PD(r) obeys
    Mass(T) >= |int_T psi| / C = 3/C,
whereas int_T omega^2/2 = 0. Hence its calibration defect has
a strictly positive lower bound: delta(r)>=3/C.
The ample SHIFT is mathematically indispensable.

## Exactly what the N-to-geometric construction would require

N-cohomology now supplies genuinely independent rational coordinate
coefficients and integral tower amplitudes. To construct T_n for an
arbitrary X, however, it must provide actual homological realization
of those coefficients in X with ALL of:
  (i) integral rectifiability and closedness of each current,
  (ii) equal INTEGRAL homology class beta for every n,
  (iii) a nonlinear area/mass estimate causing D(T_n)->0,
  (iv) no assumption that beta already has an algebraic representative.

None of these properties is a consequence of the existing finite
digit-window interference decomposition by itself. No unverified
geometric realization or universal current selector has been inserted
as a Lean axiom. Building it unconditionally would complete the
original goal, but has not been accomplished by this execution.

## Evidence summary

GREEN: independent N-coordinate basis and its linear signed mass theorem
(GitHub Actions 38843813429).
WOLFRAM: exact projective intersection calculation and exact
elliptic-graph area-defect Taylor coefficient.
ACTUAL GEOMETRY: explicit integral cycles at fixed class with continuous,
positive, vanishing calibration defects.
UNRESOLVED: the universal fixed-integral-homology current construction
for EVERY rational (p,p) Hodge class on an arbitrary X.
