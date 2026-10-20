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

Pending remote compilation after this code commit. Expected existing workflows: GST Graph V2 CM NM Geometry Upgrade; GST Pinned Universal Hodge Geometric Integration; Mathbox K3 Rank Two Primitive Intersection Gram. Read revision-matched job logs and repair all errors before recording a green outcome.

## Continuation

Arithmetic normalization route: implementation submitted; compiler outcome pending.
Native arithmetic-to-cycle route: explicit constructive certificate submitted; universal actual-source rank remains open.
Universal algebraization route: open; no counterexample or universal source constructor has been proved by these index identities.
