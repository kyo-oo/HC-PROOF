import GSTUniversalHodgeResidualProjection
import GSTGeometricRealizationStage2G

/-!
# GST genuine arbitrary-X native Hodge-cycle projection

This file connects the exact cycle-plus-residual formula to the true
Stage-2G rational (p,p) Hodge subspace of ANY smooth projective
complex scheme X, and to ACTUAL Mathlib rational codimension-p
native algebraic cycles on X.

No target source restriction is imposed: X,p, and rational Hodge
alpha are arbitrary. The only additional geometric input is a
finite already known family of actual native cycles on X,
with independently verified rational intersection-dual probes.
There is NO target witness and NO arbitrary surjectivity axiom.

For ALL alpha, build an ACTUAL native codimension-p cycle
Z(alpha)=sum_i probe_i(alpha) Z_i; its class is the known
algebraic projection of alpha. The class
alpha - cycleClass(Z(alpha)) remains in the true (p,p)
Hodge subspace, and every chosen geometric probe kills it.

Original Hodge requires the residual to vanish for every
alpha. This module does not assume or assert that it does.
-/

set_option maxHeartbeats 5000000
noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTUniversalHodgeResidualProjection

namespace GSTActualXHodgeResidualProjection

variable {X : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData X}
variable {p : Nat}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- ACTUAL rational (p,p) Hodge fiber of X from Stage-2G. -/
abbrev HodgeSpace (X : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData X) (p : Nat) :=
  rationalHodgeSubspace (H.hodgeBigrading p)

/-- Only source algebraic cycles, with actual Betti cycleClass
and independently geometric rational intersection duality.
The fields do NOT assert surjectivity onto the target Hodge space. -/
structure ActualXCycleProjectionData
    (X : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData X)
    (p : Nat) (ι : Type*)
    [Fintype ι] [DecidableEq ι] where
  sourceNativeCycles : ι → codimensionCycles X.X p
  cycle_is_hodge :
    ∀ Z : codimensionCycles X.X p,
      H.cycleClass p Z ∈ HodgeSpace X H p
  geometricDetectors : ι → HodgeSpace X H p →ₗ[ℚ] ℚ
  independently_geometric_duality :
    ∀ i j, geometricDetectors i
      (⟨H.cycleClass p (sourceNativeCycles j),
        cycle_is_hodge (sourceNativeCycles j)⟩ : HodgeSpace X H p) =
          if i = j then 1 else 0

/-- Actual native-to-Hodge cycle-class map, never an abstract
unconstrained second semantic cycleClass field. -/
noncomputable def ActualXCycleProjectionData.trueHodgeClass
    (P : ActualXCycleProjectionData X H p ι) :
    codimensionCycles X.X p →ₗ[ℚ] HodgeSpace X H p :=
  (H.cycleClass p).codRestrict (HodgeSpace X H p) P.cycle_is_hodge

/-- The generic geometric projection packet instantiated with
the exact scheme native-cycle type and Stage-2G Hodge space. -/
noncomputable def ActualXCycleProjectionData.toProjectionPacket
    (P : ActualXCycleProjectionData X H p ι) :
    GeometricDualCyclePacket ι
      (codimensionCycles X.X p) (HodgeSpace X H p) where
  cycleClass := P.trueHodgeClass
  cycles := P.sourceNativeCycles
  detectors := P.geometricDetectors
  dual := by
    intro i j
    exact P.independently_geometric_duality i j

/-- Fully concrete rational Chow-cycle construction on arbitrary X
for every rational Hodge alpha. The output is not a Betti vector
or a possibly nonalgebraic K3 tensor. -/
noncomputable def ActualXCycleProjectionData.projectNative
    (P : ActualXCycleProjectionData X H p ι)
    (alpha : HodgeSpace X H p) :
    codimensionCycles X.X p :=
  projectedNativeCycle P.toProjectionPacket alpha

/-- Exact leftover (p,p) Hodge class on the SAME original variety X. -/
noncomputable def ActualXCycleProjectionData.primitiveResidual
    (P : ActualXCycleProjectionData X H p ι)
    (alpha : HodgeSpace X H p) :
    HodgeSpace X H p :=
  residualClass P.toProjectionPacket alpha

theorem ActualXCycleProjectionData.algebraic_part_plus_residual
    (P : ActualXCycleProjectionData X H p ι)
    (alpha : HodgeSpace X H p) :
    P.trueHodgeClass (P.projectNative alpha) +
      P.primitiveResidual alpha = alpha := by
  exact actual_cycle_plus_residual_equals_target P.toProjectionPacket alpha

theorem ActualXCycleProjectionData.residual_killed_by_all_probes
    (P : ActualXCycleProjectionData X H p ι)
    (alpha : HodgeSpace X H p) (i : ι) :
    P.geometricDetectors i (P.primitiveResidual alpha) = 0 := by
  exact residual_orthogonal_to_all_geometric_cycles
    P.toProjectionPacket alpha i

/-- This is the EXACT genuine cycle witness on X as soon as the
mathematically nontrivial residual vanishing is independently proved.
No arbitrary target-native preimage is passed to this theorem. -/
theorem ActualXCycleProjectionData.cycle_represents_target_of_residual_zero
    (P : ActualXCycleProjectionData X H p ι)
    (alpha : HodgeSpace X H p)
    (hresidual : P.primitiveResidual alpha = 0) :
    H.cycleClass p (P.projectNative alpha) = alpha.1 := by
  have h := P.algebraic_part_plus_residual alpha
  rw [hresidual, add_zero] at h
  exact congrArg Subtype.val h

/-- In the actual Stage-2G target, residual ZERO is equivalent to
exact equality of the concrete constructed native cycleClass to alpha.
This is the precise mathematical criterion that a universal GST
geometric-generator theorem must establish independently. -/
theorem ActualXCycleProjectionData.residual_zero_iff_constructed_cycle_exact
    (P : ActualXCycleProjectionData X H p ι)
    (alpha : HodgeSpace X H p) :
    P.primitiveResidual alpha = 0 ↔
      H.cycleClass p (P.projectNative alpha) = alpha.1 := by
  constructor
  · exact P.cycle_represents_target_of_residual_zero alpha
  · intro h
    have hh : P.trueHodgeClass (P.projectNative alpha) = alpha :=
      Subtype.ext h
    change alpha - P.trueHodgeClass (P.projectNative alpha) = 0
    rw [hh]
    exact sub_self _

/-- This theorem exposes rather than hides the original Hodge gap:
a hypothetical missing class must give a NONZERO target Hodge
residual orthogonal to the full known algebraic detector family. -/
theorem ActualXCycleProjectionData.missing_class_has_nonzero_residual
    (P : ActualXCycleProjectionData X H p ι)
    (alpha : HodgeSpace X H p)
    (hmissing :
      alpha.1 ∉ LinearMap.range (H.cycleClass p)) :
    P.primitiveResidual alpha ≠ 0 := by
  intro hzero
  apply hmissing
  exact ⟨P.projectNative alpha,
    P.cycle_represents_target_of_residual_zero alpha hzero⟩


/-! ## ANY X: direct geometric finite-projection trace construction

EVERY smooth projective complex X of dimension d admits a finite
surjective morphism to P^d after a generic linear projection.
The classical projective-space Hodge classes are generated by
rational hyperplane intersections. Unlike a finite rational
parametrization FROM P^d, this direction exists even for general
type and non-unirational X.

For arbitrary rational Hodge alpha on X, the actual geometric
finite projection g:X->P^d produces an algebraic AMBIENT
component
  Z_X := (1/deg g) g^*(Z_P)
where cl(Z_P)=g_*(alpha). The residual rational Hodge class
  r(alpha) = alpha - cl(Z_X)
is EXACTLY annihilated by the geometric Betti trace g_*.
This provides a native algebraic cycle on EVERY X without
presupposing target Hodge surjectivity.

The trace-zero residual is the remaining primitive/new geometry
part of the ORIGINAL conjecture, and may be nonzero. No false
inference from finite projection or GST positivity to r=0 is made.
The actual finite projection, geometric cycle-class maps and
Chow/Betti naturality are separately instantiated certificates.
-/

/-- Finite dominant morphism FROM arbitrary X TO projective space P,
with genuine Chow pullback and rational Betti push/pull. All map
compatibility is geometric input, not a chosen Hodge target cycle. -/
structure ActualXFiniteProjectiveTrace
    (P X : SmoothProjectiveComplexScheme)
    (HP : HodgeBigradedBettiData P)
    (HX : HodgeBigradedBettiData X)
    (p : ℕ) where
  degree : ℚ
  degree_ne_zero : degree ≠ 0
  nativePull :
    codimensionCycles P.X p →ₗ[ℚ] codimensionCycles X.X p
  bettiPull :
    RationalSingularCohomology HP.analytification (2*p) →ₗ[ℚ]
      RationalSingularCohomology HX.analytification (2*p)
  bettiPush :
    RationalSingularCohomology HX.analytification (2*p) →ₗ[ℚ]
      RationalSingularCohomology HP.analytification (2*p)
  push_preserves_hodge :
    ∀ alpha : RationalSingularCohomology HX.analytification (2*p),
      alpha ∈ rationalHodgeSubspace (HX.hodgeBigrading p) →
      bettiPush alpha ∈
        rationalHodgeSubspace (HP.hodgeBigrading p)
  pull_preserves_hodge :
    ∀ beta : RationalSingularCohomology HP.analytification (2*p),
      beta ∈ rationalHodgeSubspace (HP.hodgeBigrading p) →
      bettiPull beta ∈
        rationalHodgeSubspace (HX.hodgeBigrading p)
  projective_hodge_has_cycles :
    rationalHodgeSubspace (HP.hodgeBigrading p) ≤
      LinearMap.range (HP.cycleClass p)
  cycleClass_natural :
    ∀ Z : codimensionCycles P.X p,
      HX.cycleClass p (nativePull Z) =
        bettiPull (HP.cycleClass p Z)
  trace_degree :
    ∀ beta : RationalSingularCohomology HP.analytification (2*p),
      bettiPush (bettiPull beta) = degree • beta

/-- An ACTUAL rational native codimension-p algebraic cycle on
the ORIGINAL arbitrary X from its finite geometric projection to
projective space. The input is an arbitrary rational Hodge alpha
on X, not an assumed target algebraic representative. -/
noncomputable def ActualXFiniteProjectiveTrace.ambientNativeCycle
    {P X : SmoothProjectiveComplexScheme}
    {HP : HodgeBigradedBettiData P}
    {HX : HodgeBigradedBettiData X}
    {p : ℕ}
    (F : ActualXFiniteProjectiveTrace P X HP HX p)
    (alpha : HodgeSpace X HX p) :
    codimensionCycles X.X p :=
  F.degree⁻¹ • F.nativePull
    (Classical.choose
      (F.projective_hodge_has_cycles
        (F.push_preserves_hodge alpha.1 alpha.2)))

/-- The precise direct-X rational Hodge residual AFTER
constructing the algebraic ambient trace part. -/
noncomputable def ActualXFiniteProjectiveTrace.traceZeroResidual
    {P X : SmoothProjectiveComplexScheme}
    {HP : HodgeBigradedBettiData P}
    {HX : HodgeBigradedBettiData X}
    {p : ℕ}
    (F : ActualXFiniteProjectiveTrace P X HP HX p)
    (alpha : HodgeSpace X HX p) :
    RationalSingularCohomology HX.analytification (2*p) :=
  alpha.1 - HX.cycleClass p (F.ambientNativeCycle alpha)

/-- The remaining arbitrary-X Hodge class is invisible to the
finite projective trace, proved EXACTLY using the geometric
degree identity and the TRUE native Chow cycleClass naturality.
No geometric existence hypothesis is made for this residual. -/
theorem ActualXFiniteProjectiveTrace.traceZeroResidual_push_zero
    {P X : SmoothProjectiveComplexScheme}
    {HP : HodgeBigradedBettiData P}
    {HX : HodgeBigradedBettiData X}
    {p : ℕ}
    (F : ActualXFiniteProjectiveTrace P X HP HX p)
    (alpha : HodgeSpace X HX p) :
    F.bettiPush (F.traceZeroResidual alpha) = 0 := by
  let ZP : codimensionCycles P.X p :=
    Classical.choose
      (F.projective_hodge_has_cycles
        (F.push_preserves_hodge alpha.1 alpha.2))
  have hZP : HP.cycleClass p ZP = F.bettiPush alpha.1 :=
    Classical.choose_spec
      (F.projective_hodge_has_cycles
        (F.push_preserves_hodge alpha.1 alpha.2))
  have hAmbient :
      HX.cycleClass p (F.ambientNativeCycle alpha) =
        F.degree⁻¹ • F.bettiPull (F.bettiPush alpha.1) := by
    change HX.cycleClass p (F.degree⁻¹ • F.nativePull ZP) = _
    rw [map_smul, F.cycleClass_natural, hZP]
  calc
    F.bettiPush (F.traceZeroResidual alpha) =
        F.bettiPush alpha.1 -
          F.degree⁻¹ • F.bettiPush
            (F.bettiPull (F.bettiPush alpha.1)) := by
              simp only [ActualXFiniteProjectiveTrace.traceZeroResidual,
                map_sub, hAmbient, map_smul]
    _ = F.bettiPush alpha.1 -
          F.degree⁻¹ • (F.degree • F.bettiPush alpha.1) := by
            rw [F.trace_degree]
    _ = 0 := by simp [smul_smul, F.degree_ne_zero]

/-- The trace-zero obstruction is a TRUE rational Hodge (p,p)
class on the ORIGINAL X, not merely a formal quotient token.
The algebraic ambient correction is guaranteed (p,p)
by the geometric finite-projection Hodge pullback law. -/
theorem ActualXFiniteProjectiveTrace.traceZeroResidual_is_hodge
    {P X : SmoothProjectiveComplexScheme}
    {HP : HodgeBigradedBettiData P}
    {HX : HodgeBigradedBettiData X}
    {p : ℕ}
    (F : ActualXFiniteProjectiveTrace P X HP HX p)
    (alpha : HodgeSpace X HX p) :
    F.traceZeroResidual alpha ∈ HodgeSpace X HX p := by
  let ZP : codimensionCycles P.X p :=
    Classical.choose
      (F.projective_hodge_has_cycles
        (F.push_preserves_hodge alpha.1 alpha.2))
  have hZP : HP.cycleClass p ZP = F.bettiPush alpha.1 :=
    Classical.choose_spec
      (F.projective_hodge_has_cycles
        (F.push_preserves_hodge alpha.1 alpha.2))
  have hAmbient :
      HX.cycleClass p (F.ambientNativeCycle alpha) =
        F.degree⁻¹ • F.bettiPull (F.bettiPush alpha.1) := by
    change HX.cycleClass p (F.degree⁻¹ • F.nativePull ZP) = _
    rw [map_smul, F.cycleClass_natural, hZP]
  have hPull :=
    F.pull_preserves_hodge (F.bettiPush alpha.1)
      (F.push_preserves_hodge alpha.1 alpha.2)
  change alpha.1 - HX.cycleClass p (F.ambientNativeCycle alpha) ∈ _
  rw [hAmbient]
  exact Submodule.sub_mem _ alpha.2 (Submodule.smul_mem _ _ hPull)


/-! ## Pinned all-varieties final existence gate: trace-zero cycles

This is the exact all-X rational Hodge target, not a new weakened
conjecture: finite projective projection constructs the algebraic
ambient part ON EVERY X, so algebraic representation of ALL remaining
trace-zero Hodge classes is EQUIVALENT to the unrestricted statement
for that X and p.

The new actual native Chow output is
  Z(alpha) = ambientNativeCycle(alpha) + Z_traceZero,
where Z_traceZero is an independent geometric representative
of the trace-zero Hodge residual. An arbitrary 'section from
cohomology to Chow' is NOT an input; Z_traceZero must come from
a genuine geometric construction. Establishing such cycles
universally is the next target, not a theorem currently asserted.
-/

/-- Fully explicit source-to-target assembly on the ORIGINAL
arbitrary smooth projective scheme from a geometric native
trace-zero residual cycle and the already constructed projective
ambient cycle. -/
noncomputable def ActualXFiniteProjectiveTrace.constructFromTraceZero
    {P X : SmoothProjectiveComplexScheme}
    {HP : HodgeBigradedBettiData P}
    {HX : HodgeBigradedBettiData X}
    {p : ℕ}
    (F : ActualXFiniteProjectiveTrace P X HP HX p)
    (alpha : HodgeSpace X HX p)
    (Ztrace : codimensionCycles X.X p) :
    codimensionCycles X.X p :=
  F.ambientNativeCycle alpha + Ztrace

/-- Its cycle class equals the arbitrary original Hodge target
whenever the independently constructed native trace-zero class
is exact. No source Hodge surjectivity on X is assumed. -/
theorem ActualXFiniteProjectiveTrace.constructFromTraceZero_correct
    {P X : SmoothProjectiveComplexScheme}
    {HP : HodgeBigradedBettiData P}
    {HX : HodgeBigradedBettiData X}
    {p : ℕ}
    (F : ActualXFiniteProjectiveTrace P X HP HX p)
    (alpha : HodgeSpace X HX p)
    (Ztrace : codimensionCycles X.X p)
    (hTrace :
      HX.cycleClass p Ztrace = F.traceZeroResidual alpha) :
    HX.cycleClass p (F.constructFromTraceZero alpha Ztrace) =
      alpha.1 := by
  unfold ActualXFiniteProjectiveTrace.constructFromTraceZero
  rw [map_add, hTrace]
  dsimp only [ActualXFiniteProjectiveTrace.traceZeroResidual]
  abel

/-- EXACT target equivalence at ALL weights on ANY X:
every rational Hodge class of X is algebraic IFF every rational
Hodge class killed by its genuine finite-projective trace
has an actual algebraic representative. This theorem makes
the trace-zero primitive existence the SINGLE remaining
unproved geometric input, without inferring it from Kähler
positivity, rational coordinate tricks, or GST formal operators.
-/
theorem ActualXFiniteProjectiveTrace.full_hodge_iff_trace_zero_hodge
    {P X : SmoothProjectiveComplexScheme}
    {HP : HodgeBigradedBettiData P}
    {HX : HodgeBigradedBettiData X}
    {p : ℕ}
    (F : ActualXFiniteProjectiveTrace P X HP HX p) :
    (rationalHodgeSubspace (HX.hodgeBigrading p) ≤
       LinearMap.range (HX.cycleClass p)) ↔
    (∀ alpha : HodgeSpace X HX p,
      F.bettiPush alpha.1 = 0 →
      alpha.1 ∈ LinearMap.range (HX.cycleClass p)) := by
  constructor
  · intro hAll alpha _
    exact hAll alpha.2
  · intro hTrace alpha hAlpha
    let a : HodgeSpace X HX p := ⟨alpha, hAlpha⟩
    let residual : HodgeSpace X HX p :=
      ⟨F.traceZeroResidual a, F.traceZeroResidual_is_hodge a⟩
    have hZero : F.bettiPush residual.1 = 0 :=
      F.traceZeroResidual_push_zero a
    obtain ⟨Ztrace, hZtrace⟩ := hTrace residual hZero
    refine ⟨F.constructFromTraceZero a Ztrace, ?_⟩
    exact F.constructFromTraceZero_correct a Ztrace hZtrace


/-! ## ALL X: actual Chow trace-zero generators from finite projection

This constructs algebraic CYCLES killed already at the Chow
pushforward level, not merely their cohomology classes.
For an ACTUAL finite flat projective projection g:X->P^d
of nonzero degree e, every known native rational codimension-p
cycle Z on X gives a new explicit native cycle

  Z^0 = Z - e^(-1) g^*(g_* Z),

which lies in ker(g_*:CH^p(X)_Q -> CH^p(P^d)_Q).

The Betti cycle-class of Z^0 lies in ker(g_*:H^{2p}(X,Q)
-> H^{2p}(P^d,Q)), and is nonzero whenever cl(Z) does
NOT belong to the ambient projective pullback subspace.

This is genuine all-varieties trace-zero CYCLE CONSTRUCTION.
It does NOT assert that the generated classes fill the
entire trace-zero Hodge subspace. That is precisely the
remaining universal existence theorem being attacked.
-/

/-- The Chow-level geometric pushforward and degree-trace law
of an actual finite flat projective projection, in addition
to the Betti-level comparison certified above. -/
structure ActualXFiniteProjectiveNativeTrace
    {P X : SmoothProjectiveComplexScheme}
    {HP : HodgeBigradedBettiData P}
    {HX : HodgeBigradedBettiData X}
    {p : ℕ}
    (F : ActualXFiniteProjectiveTrace P X HP HX p) where
  nativePush :
    codimensionCycles X.X p →ₗ[ℚ] codimensionCycles P.X p
  push_cycleClass_natural :
    ∀ Z : codimensionCycles X.X p,
      HP.cycleClass p (nativePush Z) =
        F.bettiPush (HX.cycleClass p Z)
  native_push_pull_degree :
    ∀ Z : codimensionCycles P.X p,
      nativePush (F.nativePull Z) = F.degree • Z

/-- AN ACTUAL native codimension-p cycle in the projective-trace
kernel on arbitrary X. No Hodge target or cycle-preimage
selector is an input. -/
noncomputable def ActualXFiniteProjectiveNativeTrace.traceZeroNative
    {P X : SmoothProjectiveComplexScheme}
    {HP : HodgeBigradedBettiData P}
    {HX : HodgeBigradedBettiData X}
    {p : ℕ}
    {F : ActualXFiniteProjectiveTrace P X HP HX p}
    (T : ActualXFiniteProjectiveNativeTrace F)
    (Z : codimensionCycles X.X p) :
    codimensionCycles X.X p :=
  Z - F.degree⁻¹ • F.nativePull (T.nativePush Z)

/-- Exact Chow trace-zero property: the ACTUAL proper
pushforward of the constructed algebraic cycle is zero
before applying any cohomological realization. -/
theorem ActualXFiniteProjectiveNativeTrace.traceZeroNative_push_zero
    {P X : SmoothProjectiveComplexScheme}
    {HP : HodgeBigradedBettiData P}
    {HX : HodgeBigradedBettiData X}
    {p : ℕ}
    {F : ActualXFiniteProjectiveTrace P X HP HX p}
    (T : ActualXFiniteProjectiveNativeTrace F)
    (Z : codimensionCycles X.X p) :
    T.nativePush (T.traceZeroNative Z) = 0 := by
  dsimp only [ActualXFiniteProjectiveNativeTrace.traceZeroNative]
  rw [map_sub, map_smul, T.native_push_pull_degree]
  simp [smul_smul, F.degree_ne_zero]

/-- Exact Betti class of the newly CONSTRUCTED native trace-zero
cycle: the original algebraic class minus its projective
trace component, at every codimension and on EVERY X. -/
theorem ActualXFiniteProjectiveNativeTrace.traceZeroNative_cycleClass
    {P X : SmoothProjectiveComplexScheme}
    {HP : HodgeBigradedBettiData P}
    {HX : HodgeBigradedBettiData X}
    {p : ℕ}
    {F : ActualXFiniteProjectiveTrace P X HP HX p}
    (T : ActualXFiniteProjectiveNativeTrace F)
    (Z : codimensionCycles X.X p) :
    HX.cycleClass p (T.traceZeroNative Z) =
      HX.cycleClass p Z -
        F.degree⁻¹ • F.bettiPull
          (F.bettiPush (HX.cycleClass p Z)) := by
  dsimp only [ActualXFiniteProjectiveNativeTrace.traceZeroNative]
  rw [map_sub, map_smul, F.cycleClass_natural,
    T.push_cycleClass_natural]

/-- Exact geometric NONVANISHING criterion for a new algebraic
trace-zero Hodge direction: if the known source algebraic
cycle has a Betti class outside the projective pullback image,
its corrected native Chow cycle represents a NONZERO class
in the actual trace-zero geometric cohomology of X. -/
theorem ActualXFiniteProjectiveNativeTrace.traceZeroNative_nonzero_of_new_class
    {P X : SmoothProjectiveComplexScheme}
    {HP : HodgeBigradedBettiData P}
    {HX : HodgeBigradedBettiData X}
    {p : ℕ}
    {F : ActualXFiniteProjectiveTrace P X HP HX p}
    (T : ActualXFiniteProjectiveNativeTrace F)
    (Z : codimensionCycles X.X p)
    (houtside : HX.cycleClass p Z ∉
      LinearMap.range F.bettiPull) :
    HX.cycleClass p (T.traceZeroNative Z) ≠ 0 := by
  intro hzero
  have hClass :
      HX.cycleClass p Z =
        F.degree⁻¹ • F.bettiPull
          (F.bettiPush (HX.cycleClass p Z)) := by
    have h := T.traceZeroNative_cycleClass Z
    rw [hzero] at h
    exact sub_eq_zero.mp h.symm
  apply houtside
  refine ⟨F.degree⁻¹ • F.bettiPush (HX.cycleClass p Z), ?_⟩
  rw [map_smul]
  exact hClass.symm


/-! ## Exact GST native trace-zero projector and Chow/Hodge kernel landing

For every finite flat projective projection X -> P^d, the actual
rational algebraic-cycle module on X splits into an ambient
projective pullback summand and an entirely native trace-kernel
summand. This is an exact algebraic-cycle splitting, not a
cohomology-level coordinate choice.

The trace-zero projector fixes EVERY known algebraic cycle whose
actual Chow pushforward vanishes. This is stronger than constructing
one nonzero trace-zero example. Its exact image is the ENTIRE
kernel of the genuine native pushforward.

Finally, a trace-zero rational Hodge class with ANY algebraic
representative automatically has one with ZERO native pushforward,
and the explicit projector constructs it. Thus the remaining
geometric existence question lives genuinely inside the
trace-zero Chow module, not just the cohomological trace kernel.

These are exact identities conditional only on the independently
specified finite-morphism Chow/Betti maps. They do not assert
that the trace-zero cohomological Hodge space is algebraic.
-/

/-- All-codimension rational-linear projector to the ACTUAL
kernel of native geometric Chow pushforward on arbitrary X. -/
noncomputable def ActualXFiniteProjectiveNativeTrace.nativeTraceZeroProjector
    {P X : SmoothProjectiveComplexScheme}
    {HP : HodgeBigradedBettiData P}
    {HX : HodgeBigradedBettiData X}
    {p : ℕ}
    {F : ActualXFiniteProjectiveTrace P X HP HX p}
    (T : ActualXFiniteProjectiveNativeTrace F) :
    codimensionCycles X.X p →ₗ[ℚ] codimensionCycles X.X p :=
  LinearMap.id - F.degree⁻¹ • (F.nativePull.comp T.nativePush)

/-- Projector evaluation is definitionally the already
constructed Chow trace-zero correction. -/
theorem ActualXFiniteProjectiveNativeTrace.nativeTraceZeroProjector_apply
    {P X : SmoothProjectiveComplexScheme}
    {HP : HodgeBigradedBettiData P}
    {HX : HodgeBigradedBettiData X}
    {p : ℕ}
    {F : ActualXFiniteProjectiveTrace P X HP HX p}
    (T : ActualXFiniteProjectiveNativeTrace F)
    (Z : codimensionCycles X.X p) :
    T.nativeTraceZeroProjector Z = T.traceZeroNative Z := by
  simp [ActualXFiniteProjectiveNativeTrace.nativeTraceZeroProjector,
    ActualXFiniteProjectiveNativeTrace.traceZeroNative]

/-- Existing native trace-zero cycles are FIXED by the
constructed geometric projective projector. -/
theorem ActualXFiniteProjectiveNativeTrace.traceZeroNative_fixed
    {P X : SmoothProjectiveComplexScheme}
    {HP : HodgeBigradedBettiData P}
    {HX : HodgeBigradedBettiData X}
    {p : ℕ}
    {F : ActualXFiniteProjectiveTrace P X HP HX p}
    (T : ActualXFiniteProjectiveNativeTrace F)
    (Z : codimensionCycles X.X p)
    (hZ : T.nativePush Z = 0) :
    T.traceZeroNative Z = Z := by
  change Z - F.degree⁻¹ • F.nativePull (T.nativePush Z) = Z
  rw [hZ]
  simp

/-- All-codimension native trace-zero projection is IDEMPOTENT:
performing the geometric correction twice cannot create a
new artifact or erase an existing trace-zero native cycle. -/
theorem ActualXFiniteProjectiveNativeTrace.traceZeroNative_idempotent
    {P X : SmoothProjectiveComplexScheme}
    {HP : HodgeBigradedBettiData P}
    {HX : HodgeBigradedBettiData X}
    {p : ℕ}
    {F : ActualXFiniteProjectiveTrace P X HP HX p}
    (T : ActualXFiniteProjectiveNativeTrace F)
    (Z : codimensionCycles X.X p) :
    T.traceZeroNative (T.traceZeroNative Z) =
      T.traceZeroNative Z := by
  exact T.traceZeroNative_fixed (T.traceZeroNative Z)
    (T.traceZeroNative_push_zero Z)

/-- EXACT full-range theorem: the image of the native geometric
projector is EQUAL to the kernel of actual Chow pushforward.
This is a global module equality on the actual source X. -/
theorem ActualXFiniteProjectiveNativeTrace.range_projector_eq_kernel_push
    {P X : SmoothProjectiveComplexScheme}
    {HP : HodgeBigradedBettiData P}
    {HX : HodgeBigradedBettiData X}
    {p : ℕ}
    {F : ActualXFiniteProjectiveTrace P X HP HX p}
    (T : ActualXFiniteProjectiveNativeTrace F) :
    LinearMap.range T.nativeTraceZeroProjector =
      LinearMap.ker T.nativePush := by
  apply le_antisymm
  · intro Z hZ
    obtain ⟨W, hW⟩ := hZ
    change T.nativePush Z = 0
    calc
      T.nativePush Z = T.nativePush (T.nativeTraceZeroProjector W) := by
        rw [hW]
      _ = T.nativePush (T.traceZeroNative W) := by
        rw [T.nativeTraceZeroProjector_apply W]
      _ = 0 := T.traceZeroNative_push_zero W
  · intro Z hZ
    change T.nativePush Z = 0 at hZ
    refine ⟨Z, ?_⟩
    calc
      T.nativeTraceZeroProjector Z = T.traceZeroNative Z :=
        T.nativeTraceZeroProjector_apply Z
      _ = Z := T.traceZeroNative_fixed Z hZ

/-- Any cohomological trace-zero rational Hodge class that is
algebraic already has a representative inside the TRUE native
Chow pushforward kernel: it is obtained constructively by
projecting its actual source cycle, and has exactly the
original specified Betti class, not a scalar multiple. -/
theorem ActualXFiniteProjectiveNativeTrace.exact_native_trace_zero_witness
    {P X : SmoothProjectiveComplexScheme}
    {HP : HodgeBigradedBettiData P}
    {HX : HodgeBigradedBettiData X}
    {p : ℕ}
    {F : ActualXFiniteProjectiveTrace P X HP HX p}
    (T : ActualXFiniteProjectiveNativeTrace F)
    (alpha : RationalSingularCohomology HX.analytification (2*p))
    (hTrace : F.bettiPush alpha = 0)
    (hAlg : alpha ∈ LinearMap.range (HX.cycleClass p)) :
    ∃ W : codimensionCycles X.X p,
      T.nativePush W = 0 ∧ HX.cycleClass p W = alpha := by
  obtain ⟨Z, hZ⟩ := hAlg
  refine ⟨T.traceZeroNative Z, T.traceZeroNative_push_zero Z, ?_⟩
  calc
    HX.cycleClass p (T.traceZeroNative Z) =
      HX.cycleClass p Z -
        F.degree⁻¹ • F.bettiPull
          (F.bettiPush (HX.cycleClass p Z)) :=
        T.traceZeroNative_cycleClass Z
    _ = alpha := by
      rw [hZ, hTrace]
      simp

/-- The original trace-zero Hodge existence target is EQUIVALENT
to actual Chow-cycle surjectivity FROM THE NATIVE TRACE KERNEL.
This is an exact geometric range statement, not an assumption
or proof that every trace-zero Hodge class is representable. -/
theorem ActualXFiniteProjectiveNativeTrace.hodge_trace_zero_iff_native_kernel
    {P X : SmoothProjectiveComplexScheme}
    {HP : HodgeBigradedBettiData P}
    {HX : HodgeBigradedBettiData X}
    {p : ℕ}
    {F : ActualXFiniteProjectiveTrace P X HP HX p}
    (T : ActualXFiniteProjectiveNativeTrace F) :
    (∀ alpha : HodgeSpace X HX p,
      F.bettiPush alpha.1 = 0 →
      alpha.1 ∈ LinearMap.range (HX.cycleClass p)) ↔
    (∀ alpha : HodgeSpace X HX p,
      F.bettiPush alpha.1 = 0 →
      ∃ Z : codimensionCycles X.X p,
        T.nativePush Z = 0 ∧ HX.cycleClass p Z = alpha.1) := by
  constructor
  · intro h alpha hZero
    exact T.exact_native_trace_zero_witness alpha.1 hZero
      (h alpha hZero)
  · intro h alpha hZero
    obtain ⟨Z, _, hZ⟩ := h alpha hZero
    exact ⟨Z, hZ⟩

#check ActualXFiniteProjectiveNativeTrace.nativeTraceZeroProjector
#check ActualXFiniteProjectiveNativeTrace.range_projector_eq_kernel_push
#check ActualXFiniteProjectiveNativeTrace.traceZeroNative_idempotent
#check ActualXFiniteProjectiveNativeTrace.exact_native_trace_zero_witness
#check ActualXFiniteProjectiveNativeTrace.hodge_trace_zero_iff_native_kernel
#print axioms ActualXFiniteProjectiveNativeTrace.hodge_trace_zero_iff_native_kernel

#check ActualXFiniteProjectiveNativeTrace.traceZeroNative
#check ActualXFiniteProjectiveNativeTrace.traceZeroNative_push_zero
#check ActualXFiniteProjectiveNativeTrace.traceZeroNative_cycleClass
#check ActualXFiniteProjectiveNativeTrace.traceZeroNative_nonzero_of_new_class
#print axioms ActualXFiniteProjectiveNativeTrace.traceZeroNative_nonzero_of_new_class

#check ActualXFiniteProjectiveTrace.constructFromTraceZero_correct
#check ActualXFiniteProjectiveTrace.full_hodge_iff_trace_zero_hodge
#print axioms ActualXFiniteProjectiveTrace.full_hodge_iff_trace_zero_hodge

#check ActualXFiniteProjectiveTrace.ambientNativeCycle
#check ActualXFiniteProjectiveTrace.traceZeroResidual_push_zero
#check ActualXFiniteProjectiveTrace.traceZeroResidual_is_hodge
#print axioms ActualXFiniteProjectiveTrace.traceZeroResidual_push_zero

#check ActualXCycleProjectionData.projectNative
#check ActualXCycleProjectionData.primitiveResidual
#check ActualXCycleProjectionData.algebraic_part_plus_residual
#check ActualXCycleProjectionData.residual_killed_by_all_probes
#check ActualXCycleProjectionData.missing_class_has_nonzero_residual
#print axioms ActualXCycleProjectionData.algebraic_part_plus_residual

end GSTActualXHodgeResidualProjection
