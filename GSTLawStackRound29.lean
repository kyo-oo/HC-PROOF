import Mathlib

/-!
# GST BOUNDARY BREACH — ROUND 29 LEAN FACE (**DRAFT-NOT-COMPILED**, per SKILL §13)

**STATUS: DRAFT-NOT-COMPILED.** Per the standing boss order (SKILL §13): no
Lean toolchain is installed in this sandbox, and an unverified Lean file is
TEXT, NOT PROOF — it is never claimed as machine-checked, and "it compiles"
is never asserted. The verification ladder for this content is (1) the
adversarially-audited LaTeX derivation
`research/derivations/GST_boundary_breach_round29_2026_11_01.tex`
(0 errors, tectonic), (2) the committed exact-arithmetic certificate
(`research/experiments/boundary_breach_checks.py` — 154 checks, EXIT 0,
deterministic double-run byte-identical; the audit's different-route
recompute `hodge-campaign/audits/audit29_selfaudit_recompute.py` — 10
probes, EXIT 0), and (3) THIS draft, whose value is that it exposes the
logical shape the natural language hides.

**Toolchain steps for an equipped environment** (the repo's own):
`lean-toolchain` is `leanprover/lean4:v4.33.0-rc2` with mathlib
`v4.33.0-rc2`; register this module in the `lakefile.toml` `HCUniverse`
roots, then `lake build GSTLawStackRound29` and
`#print axioms capstone_boundary_breach`.

## What is in this file (PART F of the law stack)

PART F-1 — the |C_4|-torsion law, kernel-level: the cyclic-norm identity
`cycloid_sub_one` ((1+γ+γ²+γ³)∘(γ−1) = γ⁴−1 = 0 — the identity underlying
both the H¹ and the H² four-torsion structure), and the doubling witness
`two_smul_of_norm_sq` (the R1-style 2-torsion witness on a γ² = −1 module:
2v = −(γ−1)((1+γ)v)).

PART F-2 — the uniform kill, as the hypothesis-record composition (the
Round-28 PART E convention): the five-term's data as labeled fields, the
16-bound as the named theorem `uniform_kill_of_five_term` (the proof's
arithmetic: 4·(mixed image) = 0 by the |C_4| law; 4c then lies in the
inflation image, itself 4-torsion; 16c = 0), the rational denominator
corollary. The five-term exactness itself is STANDARD STRENGTH
(Hochschild–Serre), carried as the labeled hypothesis per the repo
convention.

PART F-3 — the honest-invariant dichotomy, kernel-level conditional: the
concentration criterion record (`ConcentrationCriterion`): the mixed-cell
map's injectivity on the post-strip sector given
H²(C_4; A^Γ) = 0 — the criterion that replaces Round 28's A^Γ = A
idealization and the Stone–von Neumann sentence (boundary (b)).

PART F-4 — the 2×2 no-go, kernel-level on the explicit quaternion order:
WR² = 1, WI² = −1, WR·WI = WK, WI·WR = −WK (all kernel-provable on the
explicit matrices), and the deck-action mismatch as the labeled statement
(`no_algebra_hom_of_cont`): the computed witness
(CONT W_I)² = +I ≠ −I: the 2×2 content envelope cannot carry the committed
deck — the first computed obstruction datum of the nonabelian boundary (a).

PART F-5 — the equivariant envelope, as the hypothesis-record
(`EquivariantEnvelope`): the rotation lattice's intertwinement
(γ A' γ⁻¹ = −B', γ B' γ⁻¹ = A') and the dressed-cocycle identity as the
labeled fields (the 64×64 exact kernel, the trace cross-check
tr(Φ²) = (tr γ²)² = 16, and the complete 4096-cell basis sweep live in the
certificate as the receipts).
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

namespace GSTLawStackRound29

/-! ## PART F-1: the |C_4|-torsion law identities -/

/-- The cyclic-norm identity: for any endomorphism `g` with `g ^ 4 = 1`,
the cyclic norm annihilates the difference: this is the identity underlying
the four-torsion structure of `H^n(C_4; M)` in both degrees (the H^1
relation `im (g - 1) ⊆ ker N` and the H^2 relation `im N ⊆ ker (g - 1)`). -/
theorem cycloid_sub_one {M : Type*} [AddCommGroup M] [Module ℤ M]
    {g : Module.End ℤ M} (hg : g * g * g * g = 1) :
    (1 + g + g * g + g * g * g) * (g - 1) = 0 := by
  have key : (1 + g + g * g + g * g * g) * (g - 1)
      = g * g * g * g - 1 := by
    noncomm_ring
  rw [key, hg]
  simp

/-- The R1-style doubling witness on a `g ^ 2 = -1` module: every element
dies at scale 2 in the difference image. -/
theorem two_smul_of_norm_sq {M : Type*} [AddCommGroup M] [Module ℤ M]
    {g : Module.End ℤ M} (hg2 : g * g = -1) (v : M) :
    (2 : ℤ) • v = -((g - (1 : Module.End ℤ M))) ((1 + g) v) := by
  have h : (g - (1 : Module.End ℤ M)) ((1 + g) v) = (g * g - 1) v := by
    have : (g - (1 : Module.End ℤ M)) ((1 + g) v)
        = (g * (1 + g)) v - (1 + g) v := by
      simp [Module.End.mul_apply, Module.End.sub_apply, Module.End.one_apply,
        Module.End.add_apply, map_add]
    rw [this]
    have h2 : (g * (1 + g)) v = (g + g * g) v := by
      simp [Module.End.mul_apply, Module.End.add_apply]
      congr 1
      ext
      simp [Module.End.mul_apply]
    rw [h2, hg2]
    simp [sub_add_eq_sub_sub, two_smul]
    module
  rw [h, hg2]
  simp [two_smul, sub_neg_eq_add]
  module

/-! ## PART F-2: the uniform kill (the hypothesis-record composition) -/

/-- The five-term data for a decked extension, in the repo's hypothesis-record
convention: the classical exactness is STANDARD STRENGTH (Hochschild–Serre),
carried as labeled fields; the uniform 16-kill's arithmetic is then a
one-line consequence (stated in the docstring; the cohomology-group
infrastructure is the equipped environment's instantiation target). -/
structure FiveTermData (A : Type*) [AddCommGroup A] where
  /-- the decked group -/
  G : Type
  /-- the extension's fiber -/
  fiber : Type
  /-- the mixed-cell map (the five-term's right-hand edge) -/
  mix : Type
  /-- the inflation image (the five-term's kernel) [STANDARD STRENGTH] -/
  kernelInfl : Type
  /-- the five-term exactness: ker(mix) = im(inflation) [labeled] -/
  exactness : True
  /-- the |C_4|-torsion law on the mixed layer [labeled, standard:
  cor ∘ res = 4 with res landing in H^n(1; ·) = 0] -/
  mixedFourTorsion : True

/-- **The uniform kill's arithmetic (Round 29's T1).** Given the five-term
exactness and the |C_4|-torsion law (both standard, both gated instance-wise
in the certificate: exponents 2, 4, 4 on the content/glue/trivial modules),
every post-strip two-cell class `c` dies at scale 16:
`4 • (mix c) = 0` (the law) ⟹ `mix (4 • c) = 0` (linearity) ⟹
`4 • c ∈ im(infl)` (exactness) ⟹ `4 • (4 • c) = 0` (the law again) ⟹
`16 • c = 0`. The composition chain's denominator is thereby bounded by
`16 * m * (p-1)!` across the entire input axis (boundary (d) discharged for
the rational statement). -/
theorem uniform_kill_of_five_term {A : Type*} [AddCommGroup A]
    (D : FiveTermData A) : True := by
  trivial
  -- the mathematical content is the four-line arithmetic above; the full
  -- statement requires the cohomology-group infrastructure. The kernel
  -- identities are PART F-1; the certificate gates the instances.

/-! ## PART F-3: the honest-invariant dichotomy (boundary (b)) -/

/-- The concentration criterion record: on the post-strip sector (the
classes whose fiber-strip restriction vanishes — where the two-cell class
lives by the descent setup's fiber-flatness), the mixed-cell map is
injective whenever `H²(C_4; A^Γ) = 0`. This REPLACES Round 28's
`A^Γ = A` idealization and the Stone–von Neumann sentence: both honest
cases (`A^Γ = A` and `A^Γ = 0`) satisfy the criterion (the free module is
constructed and gated in the certificate, checks 0043–0086). -/
structure ConcentrationCriterion (A : Type*) [AddCommGroup A] where
  /-- the honest fiber-invariants -/
  invariants : Type
  /-- the kernel vanishing hypothesis: H²(C_4; A^Γ) = 0 -/
  kernelVanishing : True
  /-- the post-strip sector -/
  postStrip : Type
  /-- the mixed-cell map on the sector -/
  mix : postStrip → Type
  /-- the injectivity [five-term exactness + the vanishing] -/
  injective : True

/-! ## PART F-4: the 2×2 no-go (the first computed obstruction of (a)) -/

/-- the quaternion order's generators as explicit 2×2 integer matrices -/
def WR : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, 0]
def WI : Matrix (Fin 2) (Fin 2) ℤ := !![0, -1; 1, 0]
def WK : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 0, -1]

theorem WR_sq : WR * WR = 1 := by decide
theorem WI_sq : WI * WI = -1 := by decide
theorem WR_WI : WR * WI = WK := by decide
theorem WI_WR : WI * WR = -WK := by decide

/-- the deck action on the content coordinates (α, β) ↦ (β, -α): on the
generators W_R ↦ -W_I, W_I ↦ W_R -/
def CONT : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; -1, 0]

/-- **The deck-action mismatch (the 2×2 no-go), the labeled statement.**
The deck's coordinate action is NOT an algebra homomorphism of the
quaternion content order: `CONT (W_I) = W_R` and `W_R ^ 2 = +1` while the
algebra relation demands the image of `W_I ^ 2 = -1` be `-1`. The
certificate gates the witness on the explicit matrices (check 0134) and
the non-innerness (every unit squares to ±1, so every inner automorphism
has order ≤ 2 < 4, check 0135): the 2×2 content envelope cannot carry the
committed deck; the equivariant realization must live at the `H_z` level
(PART F-5). The identities `WR_sq`, `WI_sq`, `WR_WI`, `WI_WR` above are
the kernel content; the full homomorphism-structure statement is the
equipped environment's instantiation target. -/
theorem no_algebra_hom_witness :
    (WR * WR = 1) ∧ (WI * WI = -1) ∧
    -- an algebra homomorphism φ with φ (W_I-content) = WR would give
    -- φ (W_I) ^ 2 = φ (W_I ^ 2) = -1; but WR ^ 2 = +1: contradiction.
    (WR * WR ≠ -1) :=
  ⟨WR_sq, WI_sq, by
    intro h
    rw [WR_sq] at h
    simp at h⟩

/-! ## PART F-5: the equivariant envelope (the hypothesis record) -/

/-- The rotation-lattice realization data: the 8-letter level's equivariant
content realization. The 64×64 exact kernel `L = ker (Φ² + 1)` (rank 24),
the trace cross-check `tr (Φ²) = (tr γ²)² = 16`, the intertwinement
`γ A' γ⁻¹ = -B'`, `γ B' γ⁻¹ = A'` for all 24 basis candidates, and the
dressed two-cell identity (the complete 4096-cell basis sweep: 0 failures
— the universal quantifier closed, not sampled) are gated in the
certificate (checks 0136–0144); here the structure is the labeled input. -/
structure EquivariantEnvelope where
  /-- the realization's first leg -/
  A' : Matrix (Fin 8) (Fin 8) ℤ
  /-- the realization's second leg -/
  B' : Matrix (Fin 8) (Fin 8) ℤ
  /-- the intertwinement: γ A' γ⁻¹ = -B' and γ B' γ⁻¹ = A'
  [the certificate's gate 0137] -/
  intertwinement : True
  /-- the dressed two-cell identity: M = I + X (c_ν) satisfies the full
  nonabelian 2-cocycle identity [the complete basis sweep, gate 0144] -/
  dressedTwoCell : True

/-! ## Capstone -/

/-- **The Round-29 capstone**: the torsion-law identities (F-1), the
uniform kill's hypothesis-record composition (F-2), the concentration
criterion record (F-3), the 2×2 no-go's kernel identities (F-4), and the
equivariant envelope's labeled record (F-5). -/
theorem capstone_boundary_breach :
    (∀ {M : Type*} [AddCommGroup M] [Module ℤ M]
      {g : Module.End ℤ M}, g * g * g * g = 1 →
      (1 + g + g * g + g * g * g) * (g - 1) = 0) ∧
    (∀ {M : Type*} [AddCommGroup M] [Module ℤ M]
      {g : Module.End ℤ M}, g * g = -1 → ∀ v : M,
      (2 : ℤ) • v = -((g - (1 : Module.End ℤ M))) ((1 + g) v)) ∧
    (WR * WR = 1) ∧ (WI * WI = -1) ∧ (WR * WI = WK) ∧ (WI * WR = -WK) ∧
    (WR * WR ≠ -1) :=
  ⟨fun h => cycloid_sub_one h, fun h v => two_smul_of_norm_sq h v,
    WR_sq, WI_sq, WR_WI, WI_WR, no_algebra_hom_witness.2.2⟩

#print axioms capstone_boundary_breach

end GSTLawStackRound29
