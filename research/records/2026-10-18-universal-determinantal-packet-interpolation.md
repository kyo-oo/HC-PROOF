# Mathbox — every-original-X target-born K-theory/determinantal finite packet

**Date:** 2026-10-18.
**Authoritative base:** branch research/gpt6-native-point-primitive-span-20261017, revision 4bfd8934456f6a27bf4da9fcb8ec61bd382c7dc6, preceding this research checkpoint.
**Fixed exact goal:** on each original smooth projective complex X of dimension n, each p and each rational (p,p) Hodge alpha, construct an algebraic rational codimension-p cycle with canonical Betti class alpha, without assuming a preimage or full rank.
**Verdict:** proved an ALL-X, ALL-p, target-born **smooth topological geometric cycle packet** with the exact prescribed rational homology class. Algebraicity of the individual sheets or a replacement packet remains OPEN. Not a proof of the Hodge conjecture, not a new Lean compile.

## 1. Correct the earlier unstable BU(p) obstacle: construct in stable topological K-theory

Let 1<=p<=n and alpha in H^(2p)(X,Q), not necessarily Hodge. Compact smooth projective X has finite CW type. The rational topological Chern character is an isomorphism:

  ch: K_top^0(X) tensor Q  -> direct-sum_{i>=0} H^(2i)(X,Q).

Choose a rational virtual class eta with ch_0(eta)=p-1, ch_p(eta)=alpha, all other positive-degree ch_i=0. Choose positive N clearing its K-theory denominators. Then correct the rank of N eta by adding (p-1)(1-N) copies of the trivial line as a VIRTUAL K class. This yields an INTEGRAL topological K class xi with

  rank(xi)=p-1, ch_j(xi)=0 for 1<=j<p,
  ch_p(xi)=N alpha.

Represent xi=[F]-[E] by actual smooth complex bundles F,E, and if necessary stabilize both by identical trivial summands to ensure rank(E)=e>=1 and rank(F)=f=e+p-1.

Crucially we did NOT ask for a rank-p bundle with special top Chern class, did NOT presume a holomorphic or algebraic bundle, and did NOT presume an algebraic cycle representing alpha.

Newton/Chern-character identities give the EXACT cohomological identity
\[
 c_p(F-E)=(-1)^{p-1}(p-1)!\,\mathrm{ch}_p(F-E)
          =(-1)^{p-1}(p-1)!\,N\alpha.
\]
The vanishing of all lower Chern characters forces all c_j(F-E)=0 for 1<=j<p. Neither this identity nor the K-theory construction requires alpha to be Hodge: the Hodge condition must enter the later algebraization operation.

## 2. Genuinely geometric original-X rank-drop carriers

Fix a genuine ample holomorphic line L on original X, h=c1(L). For each positive integer k, choose a generic SMOOTH complex bundle map
\[
  \phi_k: E \longrightarrow F\otimes L^{\otimes k}.
\]
Its rank-drop locus D_k={rank(phi_k)<=e-1} has expected REAL codimension 2(f-e+1)=2p. Transversality to rank stratification gives an oriented top stratum; deeper rank-drop strata have higher codimension, so D_k defines a true integral homology/pseudocycle class on original X. Topological maximal-minor Thom–Porteous yields
\[
 \mathrm{PD}[D_k]=c_p(F\otimes L^k-E)\in H^{2p}(X,\mathbb Z).
\]
These smooth determinant-matrix rank-drop loci are genuine source-born GEOMETRIC carriers; they are NOT automatically complex-analytic or algebraic.

For arbitrary fixed F,E, the Chern class
\[
 P(k):=c_p(F\otimes L^k-E)
\]
is a polynomial in k of degree AT MOST p in the rational vector space H^(2p)(X,Q). To see this directly, use Chern roots x_1,...,x_f of F and total formal characteristic polynomial
\[
 c_t(F\otimes L^k-E)
  =\frac{\prod_{i=1}^f(1+(x_i+kh)t)}
         {c_t(E)}.
\]
The coefficient of t^p is polynomial of k degree <=p even without ANY lower-Chern vanishing. Its constant value is P(0)=c_p(F-E).

## 3. Universal finite-difference constructor, ALL dimensions and codimensions

Every polynomial P(k) of degree <=p over a rational vector space satisfies
\[
 P(0)=\sum_{k=1}^{p+1}(-1)^{k-1}\binom{p+1}{k}\,P(k),
\]
because the (p+1)-st forward difference vanishes. Apply this universal integer-coefficient law to the ACTUAL determinantal geometric cycles:
\[
 \boxed{
 \sum_{k=1}^{p+1}(-1)^{k-1}\binom{p+1}{k}\,
       \mathrm{PD}[D_k]
 =(-1)^{p-1}(p-1)!\,N\alpha .
 }
\]
Equivalently the signed oriented geometric packet
\[
 \boxed{
 T_{\alpha}:=\frac{(-1)^{p-1}}{(p-1)!\,N}
     \sum_{k=1}^{p+1}(-1)^{k-1}\binom{p+1}{k}[D_k]
 }
\]
has **exact** rational fundamental class PD(T_alpha)=alpha on the ORIGINAL X, for EVERY alpha (not just Hodge), EVERY 1<=p<=n. No selected Chow witness, irreducibility of geometric correspondences, determinant full-rank assumption, unstable BU(p) lift, or abstract pure Hodge matrix-unit naturality enters the construction.

This is a real finite geometric source construction rather than an equivalence disguised as one. However an arbitrary smooth rank-drop sheet is NOT a subvariety of the complex-algebraic category. Calling T_alpha a Chow cycle would be an error.

**Fresh primitive detection:** if alpha is a nonzero rational primitive Hodge class, its signed packet cannot have all component fundamental classes within an ambient algebraic subspace that excludes alpha, since that subspace is rational-linear and the exact signed sum equals alpha. This means the new SMOOTH carriers really reach the previously missing cohomological primitive direction. It does not make those carriers algebraic.

## 4. Exact independent polynomial checks

At p=2, take f=3,e=2, formal c1(F)=u, c2(F)=v,c1(E)=z. Let h denote the numerical hyperplane variable (set h=1 in the formal coefficient test). The exact Thom-Porteous polynomial is
\[
 P(k)=3k^2+(2u-3z)k+(v-uz+z^2).
\]
Wolfram returned:
  {P(k), 3P(1)-3P(2)+P(3), Boolean equality to P(0), coefficient k^2}
with output
  {3 k^2+2 k u+v-3 k z-u z+z^2, v-u z+z^2, True, 3}.
Here u,v,z are arbitrary symbols: the cancellation removes every unwanted term, not only ambient powers or vanishing lower Chern components.

At p=3, take f=5,e=3 with formal Chern parameters u,v,w for F and z,a,b for E. The exact third Chern polynomial has degree three with all mixed terms. Wolfram returned identically
  4P(1)-6P(2)+4P(3)-P(4)=P(0)
with symbolic difference exactly 0, and computed coefficient-weight moments {1,0,0,0}. The proof for all p is the general finite-difference identity above, not extrapolation from these checks.

## 4b. Arbitrarily POSITIVE twists with INTEGER source-packet coefficients

The initial 1,...,p+1 twist levels are convenient algebraically but may be too small for any approximately holomorphic/positive-curvature transversality theorem. We can solve this coefficient issue EXACTLY.

Fix ANY integer K>=1. At the consecutive twist levels K,K+1,...,K+p define
\[
\boxed{
\lambda_{K,p,j}=(-1)^j
  \binom{K+j-1}{j}\binom{K+p}{p-j},\qquad 0\le j\le p.
}
\]
These are INTEGERS (not merely rational coefficients). Lagrange interpolation at 0 for the p+1 nodes k=K+j gives
\[
\lambda_{K,p,j}
 =\prod_{m\ne j}\frac{-K-m}{j-m}
 =(-1)^j\frac{K(K+1)\cdots(K+p)}
            {(K+j)j!(p-j)!}.
\]
Consequently \(\sum_{j=0}^p\lambda_{K,p,j}(K+j)^m=\delta_{m,0}\) for EVERY 0<=m<=p. Therefore the following exact topological/geometric identity holds on EVERY original X:
\[
\boxed{
\sum_{j=0}^{p}
 \lambda_{K,p,j}\,\mathrm{PD}[D_{K+j}]
 =c_p(F-E)
 =(-1)^{p-1}(p-1)!\,N\alpha .
}
\]
This is the all-p GST finite-channel 'twist annihilation' law: any sufficiently positive twist regime is allowed, while ALL unwanted coefficients (including every mixed Chern term) cancel and the prescribed primitive vector survives exactly. No limit or approximate equality is taken.

At K=2,p=2 the exact integer packet is \(6D_2-8D_3+3D_4\). At K=5,p=3 it is \(56D_5-140D_6+120D_7-35D_8\). Wolfram evaluated exact moment vectors \(\{1,0,\ldots,0\}\) for K in {1,2,5} and p in {2,3,4}, while the displayed Lagrange identity proves ALL integers K>=1 and ALL p.

**Mass warning:** \(|\lambda_{K,p,j}|\) grows polynomially with K, so a compactness argument for the SIGNED geometric packet does NOT follow from separate approximately holomorphic estimates for each D. Precisely because these coefficients are signed, the homological cancellation is legitimate but positivity/mass cannot be assumed to cancel as well. The extra analytic challenge is to construct algebraic *holomorphic* degeneracy sheets at at least one K-regime (or independently algebraize their whole signed packet).

## 5. Deep category obstruction: slope-polystable holomorphic bundles are TOO RESTRICTIVE

A tempting repair is to run Hermitian–Yang–Mills/Donaldson–Uhlenbeck–Yau heat flow on the topological K source until all F^(0,2) vanishes, then claim algebraicity. This DOES NOT GENERALLY WORK for a primitive nonzero source with the prescribed Chern-vector normalization.

**Theorem (standard Hermitian–Einstein/Chern–Weil consequence).** Suppose X is smooth projective Kähler and V is a slope-polystable holomorphic bundle with c1(V)=0 rationally. Its Hermitian–Einstein connection is trace-free and primitive. A positive Chern–Weil identity gives
\[
 \int_X c_2(V)\,h^{n-2}
    = C_{n,h}\int_X\lVert F_V\rVert^2\,\mathrm{vol}_h
    \quad(C_{n,h}>0).
\]
Thus if c2(V) h^(n-2) integrates to zero, the curvature is zero, V is unitary flat, and ALL its rational Chern classes vanish.

For a hypothetical topological rank-p bundle with ch_j=0 (j<p) and ch_p=N alpha≠0:
- For p>=3, c1=c2=0 automatically, hence NO such holomorphic bundle can be slope-polystable.
- For p=2 with n>=4 and alpha primitive of degree 4, c1=0 and c2=-N alpha. Primitive implies alpha h^(n-3)=0, so its c2 degree c2 h^(n-2) is zero, likewise ruling out any polystable holomorphic realization.

**Sharp actual original-X test:** on a cubic fourfold containing a plane, alpha=3[P]-h² is primitive and algebraic. Its true intersection data are alpha h²=0 but alpha²=24>0. Thus even for this KNOWN ALGEBRAIC nonzero primitive class, a polystable rank-two holomorphic bundle V with c1=0 and c2=±N alpha would violate the zero-energy Chern–Weil identity: such a V cannot exist. Wolfram independently confirmed the exact pairings {0,24}. The obstacle is not some alleged nonalgebraic class; it rules out a tempting overly rigid analytic carrier despite algebraicity.

**Therefore the correct all-X source birth cannot demand ONE slope-polystable normalized holomorphic bundle.** The original conjecture permits SIGNED Chow cycles. The finite bundle-difference/determinantal packet likewise needs signed, potentially slope-UNSTABLE, or perfect-complex/singular-sheaf geometry. This is a substantive limitation on how GST calibration energy may be used: ordinary HYM positivity kills primitive Chern channels when falsely imposed on a single normalized stable bundle.

The above uses the standard differential-geometric Hermitian–Einstein existence theorem for polystable bundles; the exact analytic external theorem and positivity normalization were NOT checked against a pinned primary-source document in this no-web checkpoint. The Chern-polynomial calculations were verified symbolically; the global differential-geometric claim is given with its mathematical hypotheses, not claimed as a Lean theorem.

## 6. Honest remaining nonlinear construction challenge

To **solve** the user-requested all-varieties Hodge theorem using the new finite packet, one must construct for each X,p,Hodge-alpha enough HONEST complex-analytic/algebraic determinants A_k on the SAME original X whose canonical classes are the P(k), or build an independent holomorphic/coherent perfect-complex avatar realizing the target-born virtual K-class. The Hodge condition is absent from Steps 1–3 and MUST enter this new map from smooth determinant geometry into complex analyticity. Ordinary smooth transversality cannot provide it, HYM polystability is impossible for nonzero normalized primitive packages, and simply applying the existing algebraic GST orbit to existing algebraic seeds cannot manufacture the missing direction.

The next viable attack is TARGET-DEPENDENT **signed, unstable/coherent determinantal geometry**, not more old-cycle transformations and not a fictitious "zero-calibration" law. The rational class equality has been constructively solved **in homology**, not in Chow. The universal Hodge conjecture remains OPEN.

**Checks:** exact symbolic Wolfram p=2 and p=3 formulas, full all-p finite difference derivation; no local Lean installation and no GitHub Actions workflow was launched. The external analytic and topological transversality theorems should be source-authenticated before any claim of independently kernel-verified implementation.
