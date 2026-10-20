# GST middle Euler construction: Lean implementation and remote verification

Date: 2026-10-21 (Asia/Calcutta).
Base: d34b0a248ae9f54500bf7c3e78f1cf612d4c5e18 on research/gpt6-native-point-primitive-span-20261017.

## Exact target and implementation

Continue the 691-line middle-world arithmetic derivation into the existing GST Lean modules, with remote GitHub Actions compilation. The original universal target remains actual rational algebraic cycle representatives of every rational Hodge class on every original smooth projective complex X.

- GSTGraphV2SelfExpandingCosmology.lean: constructive denominator-separated Newton source for the finite normal correction; nilpotent error factorization; exact square-root/Segre cancellation; preservation of the native subalgebra in both directions; signed Euler trace normalization; primitive-coordinate positive polarization; discriminant arithmetic.
- GSTActualXHodgeResidualProjection.lean: measured matrix of ACTUAL original-X source cycle classes, explicit inverse-weighted native cycle, and exact cycleClass correctness from a verified matrix inverse or nonzero determinant.
- GSTK3PrimitiveGram.lean: exact M=5 duality/exceptional sign calculation, native diagonal Euler index 21 and native Euler Gram determinant 63*d^2.

No new Lean files or global axioms; no sorry/admit placeholders. These are proof submissions, with compiler status pending until observed below.

## Constructive mathematical upgrade

Let s be the actual Segre class, with (1-s)^c=0. Define rational denominators d_0=1, d_(n+1)=2*d_n^3 and numerator polynomials r_0=1, r_(n+1)=r_n*(3*d_n^2-s*r_n^2), interpreting rational d_n in the cohomology/Chow algebra. The integral polynomial identity is
  d_(n+1)^2-s*r_(n+1)^2=(d_n^2-s*r_n^2)^2*(3*d_n^2+(d_n^2-s*r_n^2)).
Thus the defect is divisible by (1-s)^(2^n). Since 2^c>=c, R=d_c^(-1)*r_c satisfies s*R^2=1. This CONSTRUCTS the normalizer from nilpotence; it does not hypothesize its existence. When s*c(N)=1, R^2=c(N). Every intermediate numerator and R stay in the native rational characteristic-class algebra. R*a is native iff a is native.

## Audited geometric boundary

Self-review of the implication 'positive middle integer Euler index implies algebraic realization': incomplete, with the exact missing implication being algebraization of the explicit topological K packet. Positive topological pairing has a partner in topological K; that partner is not automatically an algebraic perfect complex. The native inverse-matrix theorem consumes ACTUAL algebraic source columns. It does not supply them universally.

Formalization scope is explicit: the new Graph section proves rational algebra and finite coordinate polarization. The geometric topological KU/Gysin/GRR comparison and full Hodge--Riemann statement are not newly formalized by defining a trace polynomial. The discriminant lemma consumes det(S)=1; its geometric unipotent-grading proof is in the manuscript. The ActualX compiler uses the repository's exact Mathlib cycle type and supplied Stage-2G cycleClass; independent canonical semantic realization remains the existing Gate 1 obligation. A successful build must not be reported as the full Hodge conjecture.

## Computation

Wolfram independently expanded both rational and denominator-separated Newton error identities to zero. Eighteen exact truncated projective-normal models, dimensions 0..8 with M=d+1 and M=2d+3, verified both s*R^2=1 and equality with the finite binomial normalizer. Source/output files are alongside this record under research/computations.

## Compilation

Initial submission: 4715410811cb32e2fd83a0d90611d3adf1fb8214.

- Graph arithmetic GREEN: https://github.com/kyo-oo/HC-PROOF/actions/runs/39482156972 .
- K3 Gram/Euler benchmark GREEN: https://github.com/kyo-oo/HC-PROOF/actions/runs/39482156988 .
- Pinned integration run 39482156974 exposed exactly one type error at GSTActualXHodgeResidualProjection.lean:2496: Matrix.mul_nonsing_inv requires IsUnit(det), not merely det!=0. The underlying right-inverse reconstruction theorem compiled; the determinant wrapper did not.
- Minimal repair: supply isUnit_iff_ne_zero.mpr hDet over Q. The compiler output identifies this exact conversion; no theorem statement or mathematical premise changes.
- Remote compilation of the repaired ActualX file and full pinned gate is pending until observed below. The separate initial ActualX job may still be rebuilding dependencies; its status is not evidence for the repaired revision.

The manuscript now includes the denominator-separated constructive Newton proof. Its general KU/GRR and Hodge geometry remain mathematical manuscript results, with the formal algebraic scope specified above.

## Continuation

Arithmetic normalization route: implementation submitted; compiler outcome pending.
Native arithmetic-to-cycle route: explicit constructive certificate submitted; universal actual-source rank remains open.
Universal algebraization route: open; no counterexample or universal source constructor has been proved by these index identities.

## Completed formal input chain

The original nilpotent positive Chern class u=c(N)-1 now directly constructs the finite Segre word s=sum_(k<c)(-u)^k using the existing GST birth-feedback inverse. The proof derives (1-s)^c=0 from u^c=0, constructs the Newton normalizer, proves its square is 1+u, and gives the complete Chern -> Segre -> Newton -> Euler cancellation theorem. No extra Segre-nilpotence premise is needed. This final composition is submitted for revision-matched Graph and pinned verification.

## Self-review of the proposed final inference

Claim audited: do the nondegenerate normalized Euler form and positive integer detector alone imply that every prescribed original rational Hodge class has a native algebraic representative?

Verdict: incomplete; algebraic realization of the detector partner/source is not supplied. This is not a failed Newton or Euler theorem.

A precise algebraic discriminator is H=Q^2 with ordinary positive dot product and topological source space H itself. Take the unital native subalgebra to be the diagonal {(q,q)} in the coordinatewise Q-algebra Q^2, and take s=1. The normalized arithmetic pairing is already the positive dot product. The vector (1,0) has integer self-index 1 but has no diagonal native preimage. This is a countermodel to an inference from the abstract index/native-algebra interfaces; it is NOT a geometric variety and NOT a counterexample to the Hodge conjecture.

Thus the denominator-separated normalizer gives a new explicit finite native characteristic-class word, while its proved native_iff identity preserves the original algebraization question. The actual native index matrix theorem closes the cycle construction exactly when its actual source columns have full rank. A topological Gram matrix supplies no proof of that native-column condition.

Audit provenance: self-review, manuscript and Lean submissions pinned at d34b0a2, 4715410 and b4c7d11. No independent-agent review or geometric KU/GRR formalization is claimed.
