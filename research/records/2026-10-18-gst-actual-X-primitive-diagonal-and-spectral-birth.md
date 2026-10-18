# Mathbox — universal original-X primitive algebraic correspondence and all-rank spectral native-birth attack

**2026-10-18. Base:** c593e5a4c9828072cf3a9cf3c7c1c8d87d65f985. **Target unchanged:** for arbitrary smooth projective complex original X, every p and rational (p,p) alpha, independently construct an actual Z in CH^p(X)_Q with the genuine canonical singular-Betti cycle class alpha. The new object constructed here is an ORIGINAL-X **algebraic correspondence in CH^n(X×X)_Q**, not a codimension-p original-X representative; do not conflate them.

## Route A — all-X actual algebraic primitive diagonal, with no target cycle as input

Let X be smooth projective of complex dimension n>0. Embed X by a sufficiently ample L, then take a basepoint-free general linear projection f:X→P^n, finite surjective of degree d>0. Because X is smooth Cohen–Macaulay and P^n is regular, a finite equidimensional f is flat. Its graph Γ_f⊂X×P^n is genuine algebraic; transposition and proper algebraic correspondence composition give the true codimension-n fiber-product correspondence

\[
 W_f={}^t\Gamma_f\circ\Gamma_f=[X\times_{\mathbb P^n}X]\in CH^n(X\times X)_{\mathbb Q}.
\]

Define the actual *algebraic* projector correspondence, with NO Hodge witness as input,

\[
\boxed{\Pi_f:=[\Delta_X]-\tfrac1d W_f\in CH^n(X\times X)_{\mathbb Q}.}
\]

Its action on rational Betti cohomology (after genuine graph fundamental-class/Gysin comparison) is exactly \((\Pi_f)_*=I-\frac1d f^*f_*\). Since \(f_*f^*=dI\), this operator is idempotent, kills all classes \(f^*H^{2p}(\mathbb P^n,\mathbb Q)=\mathbb Q h^p\), and fixes \(\ker f_*:H^{2p}(X,\mathbb Q)\to H^{2p}(\mathbb P^n,\mathbb Q)\). In particular any middle primitive rational Hodge class alpha with 2p<=n and p>=1 satisfies \(f_*\alpha=0\) by the primitive relation \(\alpha h^{n-2p+1}=0\), hence \(\Pi_{f*}\alpha=\alpha\). The entire algebraic correspondence is already present on the ORIGINAL X×X for **every X**, independent of whether alpha is algebraic.

Let \(\alpha\ne0\) be rational primitive of type (p,p), 2p<=n, and let Q be the true signed Hodge–Riemann pairing \(Q(\alpha,\alpha)=(-1)^p\int_X\alpha^2 h^{n-2p}>0\). Using the diagonal integration identity and f_*alpha=0 gives the exact **target-sensitive algebraic correspondence readout**

\[
\boxed{(-1)^p \int_{X\times X} [\Pi_f]\,
   \mathrm{pr}_1^*(\alpha h^{n-2p})\,\mathrm{pr}_2^*(\alpha)
   =Q(\alpha,\alpha)>0.}
\]

Thus a genuine algebraic primitive projective-incidence/diagonal object has *nonzero geometric detection of any nonzero primitive alpha on every original X*, without a preexisting codimension-p Chow cycle representing alpha. This is a structural cross-connection of GST diagonal identity, finite-projection native trace-zero surgery, polarized residual energy and Poincare geometry. The cohomological alpha factors in the readout are NOT algebraic inputs. **No single-sided original-X cycle is derived by this identity.**

**Exact original-X cubic-fourfold test:** For smooth cubic fourfold X containing plane P, d=3, f_*h²=3H², f_*[P]=H², so \(\Pi_{f*}h²=0\) and \(\Pi_{f*}[P]=[P]-h²/3\). In the actual intersection Gram [[3,1],[1,3]], \(([P]-h²/3)^2=8/3\), agreeing with the prior GST primitive residual. The projector is an actual rational combination of algebraic correspondences on the original X and has a nonzero primitive response.

**Critical source-extraction demand:** an algebraic class on X×X does NOT yield an algebraic codimension-p class on X by contracting one factor with an arbitrary rational Hodge alpha; that contraction is merely a rational cohomology operation. A genuine all-X source theorem must construct an *algebraic* factorization/slicing of Pi_f with nonzero alpha-coupling. Replacing the cohomological alpha in the above pairing by a presupposed Chow class would insert the target into the hypothesis. This is the precise native-source operation left for geometric work, not a newly introduced axiom.

## Route B — upgraded GST arbitrary-rank spectral correspondence determinant

Let T be a genuine algebraic correspondence inducing a rational Hodge operator, Q-self-adjoint on a chosen positive primitive sector. If T has distinct rational eigenvalues \(\lambda_1,\ldots,\lambda_s\) and an actual native source v has nonzero Q-orthogonal eigenprojections \(v_k\), put \(w_k=Q(v_k,v_k)>0\). All Hodge moments are

\[
m_j=Q(v,T^j v)=\sum_{k=1}^s w_k\lambda_k^j.
\]

Consequently the s×s GST Krylov moment matrix H_{ij}=m_{i+j} factorizes as \(H=A^{\mathsf T}\operatorname{diag}(w)A\) with A_{kj}=\lambda_k^j. Thus

\[
\boxed{\det H=(\prod_{k=1}^s w_k)
              \prod_{1\le i<j\le s}(\lambda_j-\lambda_i)^2>0.}
\]

This **removes a bare determinant nonzero hypothesis** from the old GST geometric-Krylov criterion, reducing it to separated actual correspondence eigenvalues and positive geometrically calculated seed weights. Wolfram verified the polynomial identity EXACTLY at s=1,2,3,4. The existing Lean file GSTClassicalHodgeGeometricKrylovMomentDeterminant.lean was edited in place with gstSpectralPowerMatrix, gstSpectralMomentMatrix, gstSpectralMoment_det_factor and gstSpectralMoment_det_nonzero; a dedicated GitHub workflow checks the file; its final CI receipt must be explicitly confirmed before promotion to kernel-verified.

**Operator obstruction test on the actual all-X projector from Route A.** Since \(\Pi_f^2=\Pi_f\), its only rational eigenvalues are 0 and 1. A single-generator Krylov Hankel matrix of rank s>=3 has duplicate rows and determinant identically zero. Wolfram EXACT calculations: for eigenvalue lists {0,1,1} and {0,1,1,1} the determinants are 0 for arbitrary weights; for {0,1,2} the determinant is 4abc. This proves that the universal algebraic primitive projector, although a genuine all-X *detector*, CANNOT ALONE supply a high-dimensional cyclic algebraic generating action. New genuinely richer algebraic correspondences or several distinct geometric sources are mathematically essential for this specific spectral mechanism.

Wolfram caveat: evaluating 0^0 natively can produce Indeterminate. Tests explicitly used exponent-zero value 1, the algebraically correct polynomial convention, and then found exact symbolic determinants; no floating tolerance or data fitting.

## Program status and research move

What is independently constructed on EVERY original X here: the rational primitive diagonal correspondence Pi_f and its nonzero target-sensitive pairing for every nonzero primitive rational (p,p) alpha (analytic comparison subject to standard fundamental-class naturality). What is algebraically proved for an arbitrary-rank correspondence moment: exact spectral/Vandermonde factorization and determinant positivity under actual separated spectrum and positive source components. These are substantive new *cross-law* sources and numerical invariants, not universal Hodge-cycle representatives.

**The next decisive geometric construction** is a real algebraic factorization of Pi_f on the appropriate primitive Hodge sector, or an independently built native seed with positive weight in each sector of a non-idempotent genuinely algebraic correspondence on X. Neither can be assumed merely from the existence of Pi_f or from its target-sensitive Betti pairing. Canonical cycle-class comparison remains a separate proof obligation in the current Lean structures.

No local Lean setup or web search; actual source and workflow updates were performed through the GitHub connector, with exact Wolfram computations.
