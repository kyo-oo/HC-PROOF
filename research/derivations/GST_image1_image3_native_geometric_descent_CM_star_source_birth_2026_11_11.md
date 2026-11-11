# General Space Theory — original Image-1 \(Z_0+NZ_0\) + Image-3 Navigation/CM/Hodge-Star: exact proof audit and geometric descent

**Owner's requested target:** prove the ORIGINAL universal GST geometric antecedent \(X_{\rm GST}\) of the already formalized Lean implication \(X_{\rm GST}\Rightarrow\) rational Hodge conjecture. Integrate the user's three cardinal/topology images and first original handwritten hypothesis sketch, not an unrelated Hilbert/product substitute.

**Research date:** 2026-11-11 (Asia/Kolkata).
**Base:** \`research/gpt6-native-image3-navigation-cm-star-ncoho-20261111\` at SHA \`c37c3cf47d2d3a39575cf4e8dd3364db5f88368e\`.
**New independent branch:** \`research/gpt6-gst-image3-geometric-descent-20261111\`.
**User originals consulted:** \`HYPOTHESIS PROOF, PART 1.pdf\`, \`GST_Hypothesis_Part_I_Completed.tex\`, \`GST_Hypothesis_Part_I_Cardinal_Topology_Upgrade.tex\`, the three uploaded images, the original existing GST Lean modules. The last .tex also proves cardinal naturality, actual product-family Chow correspondences, correct Hodge-star on that restricted family and a no-escape retraction theorem. We deliberately do NOT repeat those restricted geometric examples.

## I. Objective and accurate four-step scorecard

The OWNER'S exact conditional target is in \`GSTHodgeSingleHypothesisConditional.lean\`:
\[
\mathrm{NativeGSTSingleFoldOrbitLaw}(X,H)\implies
\mathrm{EveryHodgeClassIsRationalAlgebraic}(H),
\]
and similarly the determinant version. The implication is formalized; no new speculative Hodge implication needs to be invented.

Original requirements:
1. for EVERY original smooth projective complex X,p construct an ACTUAL rational algebraic correspondence \(\Gamma\in CH^{\dim X}(X\times X)_\mathbb Q\) (or appropriate fixed-degree correspondences), with native Chow N, canonical rational Betti T and \(\mathrm{cl}\circ N=T\circ\mathrm{cl}\);
2. prove a single native-algebraic seed has a T-orbit spanning the COMPLETE actual \(W_p(X)=H^{2p}(X,\mathbb Q)\cap H^{p,p}(X)\), including all primitive directions;
3. prove true original-X rational detector Hankel determinant !=0 on actual W_p(X), not just an information-space metric;
4. establish all of the above for every X and p, with the canonical Hodge/Betti realization.

**Status NOW: 2/4 native information-space parts (cyclic rank and moment determinant) solved, 0/4 fully universal original-X requirements solved.** Step 1 has a formally proved conditional actual-geometry compiler from SUPPLIED real closed correspondences. Step 4 remains universal, not a separate issue that can be inferred from arbitrary-cardinal indexing. Previous good GitHub workflows:
- native Image-3 \`42932667715\`: SUCCESS;
- genuine original-X operator pair \`42905175760\`: SUCCESS;
- all-N original-X companion class square \`42918087672\`: SUCCESS;
- companion source transport \`42917671380\`: SUCCESS.

## II. Faithful original handwritten Image-1 operator/iteration correction

The user's original handwritten Part-I source writes \(Z=Z_0+N(Z_0)\) and then uses \(N Z_0+N^2 Z_0\) inside the cycle class, with unlimited \(n\)-iteration and cardinal world indexing. **We must NOT replace that idea by \(Z=Z_0\), nor silently identify cardinal \(\aleph\) with integer iteration n.**

Use three distinct types:
- N : CH^p(X)_Q -> CH^p(X)_Q is a TRUE rational native cycle OPERATOR, not a natural number.
- n∈Nat labels iterations N^n (n=0 is identity).
- κ is cardinal size of indexed source-world family; α is an ordinal birth stage; \(\tau_\alpha\) is a geometry/topology tag. \(\aleph_\omega\) is a limit cardinal, not an ordinary operator power.

For the original true-native \`CycleClassOperatorPair\` F, define
\[
Z=Z_0+N Z_0,\qquad
\mathcal P_N(Z_0)=N Z_0+N^2 Z_0.
\]
The EXACT canonical original-X identity is
\[
\boxed{
\mathrm{cl}_X\bigl(\mathcal P_N(Z_0)\bigr)
=T\,\mathrm{cl}_X(Z_0)+T^2\,\mathrm{cl}_X(Z_0).
}
\]
This is new Lean file \`GSTImageThreeOwnerPolynomialFold.lean\`, theorem \`originalX_owner_N_plus_N_squared\`. It assumes an actual original-X natural operator pair and does not magically produce the pair. The case n=0 must be N^0=id on the original seed; the original handwritten assertion that it is necessarily zero is not implied by the usual iteration law unless the seed itself is zero.

**STRONG NEW UNIVERSAL NO-RANK-GAIN THEOREM.** Let \(V\) be ANY rational GST module and T ANY rational linear fold. Write \(C_T(v)=\operatorname{span}_{\mathbb Q}\{T^n v:n\ge0\}\). Then for every n:
\[
T^n(v+Tv)=T^n v+T^{n+1}v.
\]
Hence
\[
\boxed{C_T(v+Tv)\subseteq C_T(v)\quad\text{for all }V,T,v.}
\]
Adding \(Nv\) changes the seed but cannot by itself CREATE an independent orbit direction. Geometrically new directions must come from actual new source inputs and/or operators. This is formalized in the same new Lean module as \`ownerExpandedSeed_orbitSpan_le\`. This is NOT a rejection of the owner's original idea; it is an exact upgrade of its algebra and tells when extra source operators or cross-world CM curvature are truly needed.

### Original GST 12-state complete cyclicity classification for the TRANSFORMED seed

Let \(F_\lambda=U+J+\lambda M\) be exactly the owner's original 4x3 fold, \(v=e_{(0,0)}+e_{(0,1)}\) its ORIGINAL seed. Let \(K_\lambda(v)=[v,F_\lambda v,\ldots,F_\lambda^{11}v]\). Then the exact matrix identity is
\[
K_\lambda(v+F_\lambda v)=(I+F_\lambda)K_\lambda(v).
\]
Wolfram **symbolically proved**, directly on original 12-cell U/J/M,
\[
\boxed{\det(I+F_\lambda)
=(5+4\lambda)\left[6(\lambda+2)^2+1\right].}
\]
The bracketed factor is strictly positive for all real lambda. The base determinant previously proved is
\[
-4\lambda^2(1+\lambda)P_8(\lambda)P_9(\lambda),
\]
where P8 has no roots modulo 3 and P9 none modulo 13, with invertible leading coefficients; hence P8,P9 have NO rational zeros. Consequently the exact full original-GST theorem is
\[
\boxed{
\lambda\in\mathbb Q,\ 
\det K_\lambda(v+F_\lambda v)\ne0
\iff \lambda\notin\{0,-1,-5/4\}.
}
\]
At lambda=-5/4, base rank12 and transformed rank11; at lambda=0 rank10/10, lambda=-1 rank11/11. At the active owner's lambda=1, both rank12 and the transformed exact Krylov determinant is \(-569080009080000\) (base determinant \(-1149656584000\), multiplier \(\det(I+F_1)=495\)). This is a valuable special case: one exact EXCEPTIONAL source strength where original cyclicity is lost by the owner's own transformed seed.

**Source audit:** \`research/computations/GST_image1_original_polynomial_seed_image3_full_wave_20261111.wl\` was committed, re-fetched and executed verbatim: allPassed=True, exact symbolically verified matrix identity, determinant factorization, modular proof, five exceptional/regular rational cases.

## III. IMAGE-3 genuine internal GST Hodge-star/CM/curvature fusion

Original source facts:
- \`GSTGraphV2CMWaveFusion.J\`, \`cmSign\`, \`mirrorCell\`, \`M\`;
- \`GSTWorldPoincareDuality.worldDual\`, \`complementFin\`, \`worldDual_involutive\`;
- \`GSTWorldCosmology\` limitless dimensionless coordinates, finite observation;
- \`GSTSquarePureHodgeDuality\` native square-world pure Hodge reversal.

On the ACTUAL original 4x3 carry/trit physical information carrier, the old mirror is LITERALLY the old complementary-cell worldDual. Define D u(s)=u(worldDual(s)) and S u(s)=cmSign(s)u(s). The original CM phase satisfies cmSign(worldDual s)=-cmSign(s), and J=SD exactly. Consequently:
\[
\boxed{D^2=S^2=I,\ J^2=-I,\ DJ=-JD.}
\]
M is the ORIGINAL diagonal SURVIVE source, so SM=MS. Therefore
\[
\boxed{[J,M]=S[D,M].}
\]
The exact ORIGINAL wave-source noncommutative CM curvature is a *signed Hodge-worldDual source curvature*. Since S is invertible, ranks of both curvatures coincide: \(\rank_\mathbb Q [J,M]=\rank_\mathbb Q[D,M]=6\) for the original 12-state carrier, a computationally verified exact fact. This is the requested SYNTHESIS of the owner's native Hodge-star, CM, curvature and waves, not a substituted classical Hodge-star model.

Native Lean:
- \`GSTImageThreeAllRectangularCMStar.lean\` proves ORIGINAL mirror=worldDual, J signed-worldDual, and universal rational J²=-I on every finite rectangular GST world with at least one even axis.
- \`GSTImageThreeStarCMCurvatureFusion.lean\` proves original J=SD, the anti-commutation and true curvature identity.

ALL-RECTANGULAR generalization: on any A×B original dimensionless GST world with A EVEN, define \(\sigma_A(C,d)=+1\) if C<A/2, else -1. Then \(\sigma_A(Ds)=-\sigma_A(s)\). Therefore
\(J_Au(s)=\sigma_A(s)u(Ds)\) satisfies \(J_A^2=-I\) for ALL B; similarly if B is even. This removes the artificial 12-state ceiling while preserving the exact original worldDual rather than inventing geometry. Odd-by-odd worlds have a D-fixed center and cannot admit an ALL-coordinate rational signed-complement complex structure without augmenting the source world (one easy option is a doubled world). This is a SOURCE-world parity constraint, not an assertion about actual original-X Hodge ranks.

Wolfram exact receipts:
- \`research/computations/GST_image3_all_rectangular_signed_Hodge_CM_star_20261111.wl\` was fetched and executed: 10/10 true rectangular parity cases and exact original CM signed complement, allPassed=True.
- \`research/computations/GST_image3_original_star_CM_curvature_signed_identity_20261111.wl\` was initially faulty because Wolfram protects symbol D. This was FIXED in commit with nonreserved names; fetched NEW source and executed verbatim again, with EVERY identity and rank6 checked, allPassed=True. Keep the fixed source as reproducible authoritative receipt.

**Type firewall:** The native Hodge-like worldDual on information cells is NOT AUTOMATICALLY the actual metric analytic Hodge star on X nor a Chow correspondence on X. Even when a geometric Hodge-star action on primitive cohomology is rational, its realization by a true original-X algebraic correspondence must be proved separately. The cohomological star can change Hodge grade p to d-p; don't demand a same-p endomorphism when p != d/2.

## IV. IMAGE-3 original CM rank-adaptive F-quotient: what truly descends

The original native full F-fold has proved cyclic quotients of arbitrary positive rational ranks r (prior rank-adaptive companion). This removes the artificial multiple-of-twelve dimension restriction.

BUT one must not demand that the original \(J^2=-I\) descend as an endomorphism to EVERY W_p(X): the rational rank-one target Q does not support any linear J with J²=-I. This is provable directly from q²=-1 having no rational solution.

**Exact original GST witness from TRUE original 12x12 U,J,M:** take λ=5/3, so F=U+J+5/3M has full 12-dimensional cyclic rank. The two original U-fixed CM-mirrored cells are null (0,0) and max (3,2), with F restriction
\[
\begin{pmatrix}1&1\\-1&13/3\end{pmatrix}
\]
and rational eigenvalue 4. The original rational left detector \(\ell(u)=u_{(0,0)}-3u_{(3,2)}\) is a true FULL-12D left eigenfunctional: \(\ell F=4\ell\). Hence \(\ell\) is a surjective F-intertwining rank-one quotient.

However choose original signal \(w=e_{(0,0)}+\frac13e_{(3,2)}\). Then
\[
\ell(w)=0,\quad
\ell(Jw)=10/3\ne0,\quad
\ell([J,F]w)=-80/9\ne0.
\]
Therefore the SAME F-compatible quotient does not carry a well-defined quotient J or original CM commutator operator. **This is a precise instruction for the user's geometric descent compiler:** intertwine the whole original F with the target Hodge operator; retain the original CM curvature on the SOURCE side and prove a separate map for its BORN cycles; do not demand all suboperators automatically descend to arbitrary-rank targets.

Exact Wolfram file \`research/computations/GST_image3_rank_adaptive_original_CM_quotient_descent_firewall_20261111.wl\`, re-fetched and executed: allPassed=True, rank12, rational quotient, 10/3 and -80/9. New Lean file \`GSTImageThreeCMDescentFirewall.lean\` formalizes the general rank-one no-go directly using the original J²=-I.

## V. Step-01 strengthening: actual original-X REAL CLOSED CORRESPONDENCES, not mere linear-pair syntax

The prior Image-3 \`GSTImageThreeOriginalXNativeLanding.lean\` constructs the exact pair \(F=U+J+\kappa M\) from any three \`CycleClassOperatorPair\` inputs, and proves its class-square. But a bare operator pair is NOT necessarily the action of an algebraic correspondence \(\Gamma\subset X\times X\). This is a real semantic distinction in the original step01.

The preexisting true geometry \`GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra.RealizedFiniteClosedCorrespondence\` has an actual finite closed correspondence plus pointwise geometry certification. A finite rational word of these forms true rational algebraic correspondence action. The NEW \`GSTImageThreeRealizedWordGeometry.lean\` takes THREE actual such \(U,J,M\) GEOMETRIC correspondences as inputs, constructs
\[
\boxed{\Gamma_{\rm Image3}(R)=(1,U)+(1,J)+(\kappa(R),M),}
\]
as an actual finite rational realized-correspondence word, proves equality of BOTH native cycle operator and Betti action to the previous \(F\), and proves exact original-X canonical class-square:
\[
\mathrm{cl}_X(N_{\Gamma(R)} Z)=T_{\Gamma(R)}\mathrm{cl}_X(Z).
\]
It also proves the original physical navigation canonical-tail invariance of the geometric word and preserves the cycle-class range. This is a genuine strengthening of Step01, but the actual desired U,J,M correspondences on arbitrary X are STILL inputs, not constructed from original wave signal matrices for all X.

## VI. Step02 original-X two-mode geometric detector criterion and the range obstruction

The original wave result has exact source-free rank10 and active rank12, with two independent original annihilator detectors seeing the native fold-depth-2 and fold-depth-3 classes as columns (-2,0) and (-8,2), determinant -4.

New \`GSTImageThreeTwoModeGeometricBirth.lean\` defines two actual ORIGINAL-X Chow cycles:
\(Z_2=N_F^2Z_0\), \(Z_3=N_F^3Z_0\). It proves their true canonical Betti identities from cycle-class naturality. For a proper subspace S of **PREVIOUSLY KNOWN** classes and genuine rational cohomological detectors d1,d2 vanishing on S, if
\[
\begin{pmatrix}d_1(cl Z_2)&d_1(cl Z_3)\\d_2(cl Z_2)&d_2(cl Z_3)\end{pmatrix}
=\begin{pmatrix}-2&-8\\0&2\end{pmatrix},
\]
then exact rational linear algebra proves
\[
a\,cl Z_2+b\,cl Z_3\in S\ \Longrightarrow\ a=b=0.
\]
This gives TWO genuinely new independent class directions modulo S without assuming preimages for unknown Hodge classes in the output. But existence of the actual original-X F, Z0 and the geometric detector measurements are STILL specific geometric hypotheses; the previous native info d1,d2 are not themselves detectors on X.

A crucial honest FIREWALL also formally proved: if the detector is required to annihilate the ENTIRE algebraic class image \(A_p(X)=im(cl_X)\), then it MUST annihilate any real \(cl(N_F^3Z_0)\), since the latter is the class of an actual Chow cycle. Thus \(-4\)-type source birth detectors can vanish on the **old known subspace**, not on ALL geometrically algebraic classes. The geometric proof must show the old generated subspace was proper and the constructed true new cycles expand it, until its final dimension equals full W_p(X). This is why simply declaring symbolic wave curvature to be a new algebraic Hodge direction would be a circular argument.

## VII. What remains, precisely — directly within the FOUR ORIGINAL steps

**We have not inserted a fifth unrelated requirement.** The new work sharpens dependencies INSIDE original Steps01–04.

1. **Step01 universal geometric compiler:** For every original X,p, construct actual algebraic correspondences representing enough of the owner's source F-wave/CM/navigation operators on the original rational Chow carrier, rather than choose abstract matrices or assume such correspondence inputs. The universal construction cannot require J²=-I on odd-dimensional target Hodge spaces; J can remain original native source-side.
2. **Step02 genuine primitive source birth:** Establish a source-to-target map from the original cardinal/N-wave cycles that actually hits EVERY missing rational Hodge primitive direction. Need either actual original-X geometric detector minor(s) produced from geometry without presupposing the target's Chow preimage, or a genuine non-circular alternative that forces full rank.
3. **Step03 true Hankel once 01/02 achieved:** The already proved native cyclic/Hankel linear algebra constructs a nonzero detector. For the author's transformed seed use the exact \(\lambda\notin\{0,-1,-5/4\}\) safeguard rather than claiming arbitrary polynomial seed changes create rank.
4. **Step04 universal quantifiers/canonical realization:** Take actual X,p and rational canonical Betti class, including higher primitive and special CM. The cardinal source labels \(\aleph_\alpha\), topological parameter \(\tau_\alpha\), limitless observation and self-expanding world-birth are fully compatible as indexing/transport formalism. They do not independently yield an algebraic cycle for a missing original-X class.

**First unresolved implication:** A fully geometric original-X correspondence/seed/detector mechanism that preserves the owner's native F nondegeneracy *after* canonical Betti realization and grows the actual original-X known algebraic span up to all of W_p(X), with no unknown cycle-class preimage selected as an input.

The original conditional Lean theorem then DOES complete Hodge if that universally quantified original-X GST hypothesis is genuinely proved.

## VIII. Evidence / CI

All new Wolfram scripts are EXACT rational symbolic algebra. Four were committed and fetched back from GitHub for actual execution (with one corrected source-version), all final checks \`allPassed=True\`:
- \`research/computations/GST_image1_original_polynomial_seed_image3_full_wave_20261111.wl\`
- \`research/computations/GST_image3_all_rectangular_signed_Hodge_CM_star_20261111.wl\`
- \`research/computations/GST_image3_original_star_CM_curvature_signed_identity_20261111.wl\`
- \`research/computations/GST_image3_rank_adaptive_original_CM_quotient_descent_firewall_20261111.wl\`

NEW Lean targets, on independent branch:
- \`GSTImageThreeCMDescentFirewall.lean\`
- \`GSTImageThreeRealizedWordGeometry.lean\`
- \`GSTImageThreeTwoModeGeometricBirth.lean\`
- \`GSTImageThreeAllRectangularCMStar.lean\`
- \`GSTImageThreeOwnerPolynomialFold.lean\`
- \`GSTImageThreeStarCMCurvatureFusion.lean\`

CI \`.github/workflows/gst-image3-geometric-descent-proof.yml\` checks all six local modules plus imports. Do not mark new Lean green unless the exact SHA workflow SUCCESS is observed. All code changes are confined to new files on the independent branch, preserving the owner's original Lean proof and source.


## IX. NEW THEOREM — the OWNER'S transformed Image-1 seed is cyclic for EVERY original zero-local-SURVIVE companion GST N-world fold

This is a new, NONTRIVIAL connection of the ORIGINAL handwritten \(Z_0+NZ_0\) formula to the owner's all-finite-N Image-3 *single-root* wave/CM/source construction. It does NOT replace the source with independently supplied Hodge basis cycles.

Recall from the already derived original companion source transport theorem that for every h>=2:
- the source companion \(C_h\) has distinct nonzero rationals \(\lambda_i\) with sum zero and all diagonal entries zero (therefore no local original SURVIVE M term);
- the navigation-address operator \(B_h=f_h(C_h)\) has source eigenmode addresses \(10(i-1)\);
- the true original U,J,M global fold is
\[
\mathcal F_h=I_h\otimes(U+J)+C_h\otimes M+B_h\otimes I_{12};
\]
- the ONE initial original GST source \(w_h=e_1\otimes v\), \(v=e_{(0,0)}+e_{(0,1)}\), has full cyclic orbit rank \(12h\);
- choose the small rational source strengths \(\lambda_i=i/(100h^2)\) for i<h and \(\lambda_h=-(h-1)/(200h)\), which are all nonzero, distinct, sum zero, and have absolute value below 1/200.

Now apply the author's ACTUAL Part-I transform:
\[
\boxed{w'_h=w_h+\mathcal F_h w_h.}
\]

**THEOREM (all finite h>=2).**
\[
\boxed{
\rank_\mathbb Q[w'_h,\mathcal F_h w'_h,\ldots,\mathcal F_h^{12h-1}w'_h]=12h.
}
\]
The transformed source has an exactly anti-diagonal rational moment detector, with
\[
\boxed{\det H_h=+1.}
\]

**Proof.** Since \(\mathcal F_h\) is rationally similar to the block sum
\[
\bigoplus_{i=1}^{h}
 \left(U+J+\lambda_i M+10(i-1)I_{12}\right),
\]
we can test invertibility of \(I_{12h}+\mathcal F_h\) block by block.

Block 1 has address zero. Its determinant is EXACTLY
\[
\det(I_{12}+U+J+\lambda_1M)
=(5+4\lambda_1)\left[6(\lambda_1+2)^2+1\right]\ne0
\]
because \(0<\lambda_1<1/200\), and the bracket is positive for every real value.

Each other block has address \(10(i-1)\) with i>=2. The exact original matrix maximum absolute row-sum bound is
\(\|U+J+\lambda_i M\|_\infty\le 2+2|\lambda_i|<2.01\). Every complex eigenvalue of that original block thus has modulus <2.01, whereas \(-1-10(i-1)\) has modulus >=11; hence no other block of \(I+\mathcal F_h\) is singular. Consequently \(I_{12h}+\mathcal F_h\) is invertible over Q (rational nonzero determinant).

The Krylov identity holds at ALL native-world dimensions:
\[
K(\mathcal F_h,w'_h)
=(I_{12h}+\mathcal F_h)K(\mathcal F_h,w_h).
\]
Both factors are invertible for EVERY h>=2, proving the full 12h rank. Define \(\ell_h\) to read 1 on the LAST of the transformed orbit basis vectors and 0 on its first 12h-1. The associated Hankel matrix is zero below its anti-diagonal and one along the anti-diagonal, so
\(\det H_h=(-1)^{12h(12h-1)/2}=+1\). QED.

This is a genuine ALL finite N native source theorem; the proof works uniformly because of the original source strengths and source navigation addresses, not by extrapolation from a few finite cases.

### Independently executed exact computation

The additional committed \`research/computations/GST_image1_image3_allN_transformed_single_root_companion_20261111.wl\` was fetched back and executed with Wolfram after correcting its local variable names. It tested the full original 24x24 and 36x36 native operators, in both cases:
- diagonal of C exactly zero (ZERO local original SURVIVE term);
- original root cyclic rank = required 12h;
- transformed root cyclic rank = required 12h;
- exact equality of all entries of the transformed Krylov matrix with \((I+\mathcal F_h)K(\mathcal F_h,w_h)\);
- exact nonzero determinant of \(I+\mathcal F_h\), and equality to product of all individual shifted original 12x12 determinants;
- a rational dual readout with first 12h-1 moments 0, last moment 1.

The exact tests passed for h2 strengths (1/2,-1/2) and h3 strengths (1/2,1/3,-5/6), allPassed=True. These examples use larger source strengths than the chosen universal proof family but satisfy the same nonzero/spectral separation criteria. The all-h claim comes from the uniform proof above, not the finite checks.

**Hodge hypothesis boundary:** This now proves EXACTLY the original transformed seed part of Steps02/03 on all finite GST native N-cohomology wave worlds. A proof that it yields a truly full-rank *canonical original-X* Chow/Hodge fold on every X,p still requires the actual universal geometric source/birth compiler and the target cohomological landing; do not silently treat native rank as canonical Hodge rank.


## X. Cardinal \(\aleph\)-worlds × true dimensionless GST N-cohomology × native CM star

The owner's second and third images call for all-cardinality indexing, independently variable world dimensions/topologies and an original native Hodge Star, rather than conflating \(\aleph_\omega\) with a natural-number polynomial power.

New Lean file \`GSTImageThreeCardinalRectangularCM.lean\` establishes a genuinely dependent-index geometry. Let I be ANY Lean type, of any cardinality. Give each i∈I its own finite information world \(W_i=\mathrm{WorldCell}(A_i,B_i)\), amplitudes \(u_i:W_i\to\mathbb Q\), and the ORIGINAL \`GSTWorldPoincareDuality.worldDual\` on each rectangle. The entire indexed native Hodge-like star is
\[
(D_Iu)_i(c)=u_i(D_i c),
\qquad D_I^2=I.
\]
If every A_i is even (with B_i unconstrained), use the actual ORIGINAL \`evenCarryWorldJ\` sign-twist from the previous section on EACH independently indexed geometry:
\[
(\mathcal J_Iu)_i(c)=
\sigma_i(c)\,u_i(D_i c),
\qquad
\boxed{\mathcal J_I^2=-I}
\]
for ALL I. No finite upper bound on |I|, no artificial 12-cell terminal universe, no invalid infinite Chow sum and no unproved transfinite power are involved.

This exactly marries the three owner ideas:
- cardinal \(\aleph\) indexes SOURCE WORLDS, preserving the topology \(\tau_i\) and finite coordinates of each;
- original GST Hodge/dual is the owner's genuine worldDual, extended pointwise across the cardinal family;
- rational CM structure and curvature are defined natively on even-axis source worlds, including the actual original 4x3 chart.

This DOES NOT automatically give a compatible rational J action on the complete original-X Hodge space W_p(X) when its dimension is odd (see the explicit rank-one obstruction above), nor does it assert \(\mathcal J_I\) is algebraically realizable as an original-X Chow correspondence. The universal original-X F-algebraic source-birth hypothesis remains to be constructed.

**Kernel-check status:** The new Lean module is included in the same GitHub workflow as the six previous modules. Treat the new theorem as submitted for Lean verification until its exact successful run is observed.
