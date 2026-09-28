import GSTClassicalHodgeCohomologicalPairingFrontier
import GSTClassicalHodgeOmniversalSeparatorGhostCrown
import GSTClassicalHodgeAtomicSpan

/-!
# GST CLASSICAL HODGE — POLARIZED HODGE-FIBER GHOST

The ambient pairing transformation still permits the representing dual class
to carry components outside the rational `(p,p)` Hodge fiber.  For a genuine
Hodge-polarization attack the sharper object is the restriction of the ghost
separator to the Hodge fiber itself.

This file packages only a perfect rational pairing on that genuine Hodge fiber.
It does not assert that algebraic classes span the fiber.  Perfectness converts
the restricted separator into a unique Hodge class.  A hypothetical Hodge
failure therefore produces a concrete nonzero rational `(p,p)` class which is
orthogonal to every algebraic Hodge class and which pairs nontrivially with the
Hodge class detected by the ghost.

This is the exact polarization-level residual obstruction.  Nondegeneracy or
positivity of a polarization alone does not imply that this orthogonal class
vanishes: a proper subspace may have a nonzero orthogonal complement.  Thus a
future extinction theorem must provide an independently geometric reason that
the algebraic Hodge subspace has zero orthogonal complement; merely storing
that conclusion would be Hodge-strength.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgePolarizedHodgeGhost

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeAtomicAnnihilator
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeOmniversalSeparatorGhostCrown

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

abbrev HFiber (p : Nat) := ClassicalHodgeFiber V H p

/-- Rank-free perfect pairing directly on the genuine rational `(p,p)` Hodge
fiber. -/
structure PerfectHodgeFiberPairing (p : Nat) where
  pair : HFiber (V := V) (H := H) p →ₗ[ℚ]
    HFiber (V := V) (H := H) p →ₗ[ℚ] ℚ
  toDual : HFiber (V := V) (H := H) p →ₗ[ℚ]
      (HFiber (V := V) (H := H) p →ₗ[ℚ] ℚ) := pair
  toDual_bijective : Function.Bijective toDual

namespace PerfectHodgeFiberPairing

variable {p : Nat}

noncomputable def dualClass
    (P : PerfectHodgeFiberPairing (V := V) (H := H) p)
    (ell : HFiber (V := V) (H := H) p →ₗ[ℚ] ℚ) :
    HFiber (V := V) (H := H) p :=
  Classical.choose (P.toDual_bijective.2 ell)

theorem dualClass_spec
    (P : PerfectHodgeFiberPairing (V := V) (H := H) p)
    (ell : HFiber (V := V) (H := H) p →ₗ[ℚ] ℚ) :
    P.toDual (P.dualClass ell) = ell :=
  Classical.choose_spec (P.toDual_bijective.2 ell)

theorem pair_dualClass
    (P : PerfectHodgeFiberPairing (V := V) (H := H) p)
    (ell : HFiber (V := V) (H := H) p →ₗ[ℚ] ℚ)
    (alpha : HFiber (V := V) (H := H) p) :
    P.pair (P.dualClass ell) alpha = ell alpha := by
  exact LinearMap.congr_fun (P.dualClass_spec ell) alpha

theorem dualClass_ne_zero
    (P : PerfectHodgeFiberPairing (V := V) (H := H) p)
    (ell : HFiber (V := V) (H := H) p →ₗ[ℚ] ℚ)
    (hell : ell ≠ 0) :
    P.dualClass ell ≠ 0 := by
  intro hz
  apply hell
  rw [← P.dualClass_spec ell, hz]
  exact map_zero P.toDual

end PerfectHodgeFiberPairing

/-- Restriction of an ambient separator detector to the genuine Hodge fiber. -/
noncomputable def separatorOnHodge
    {p : Nat}
    (ell : RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ] ℚ) :
    HFiber (V := V) (H := H) p →ₗ[ℚ] ℚ :=
  ell.comp (rationalHodgeSubspace (H.hodgeBigrading p)).subtype

/-- A Hodge vector is algebraic when its ambient class lies in the genuine
point-cycle-class span. -/
def IsAlgebraicHodge
    {p : Nat}
    (alpha : HFiber (V := V) (H := H) p) : Prop :=
  alpha.1 ∈ pointCycleClassSpan p (H.cycleClass p)

/-- The ghost detector remains nonzero after restriction to the Hodge fiber. -/
theorem separatorOnHodge_ne_zero
    {G : GeometricCycleClassSpine V H}
    (E : OmniversalSeparatorGhost G) :
    separatorOnHodge E.separator.detector ≠ 0 := by
  intro hz
  have hv := LinearMap.congr_fun hz E.hodge
  exact E.separator.detects hv

/-- Pairing-orthogonality to every actual algebraic Hodge vector. -/
def OrthogonalToAlgebraicHodge
    {p : Nat}
    (P : PerfectHodgeFiberPairing (V := V) (H := H) p)
    (u : HFiber (V := V) (H := H) p) : Prop :=
  ∀ alpha : HFiber (V := V) (H := H) p,
    IsAlgebraicHodge alpha → P.pair u alpha = 0

/-- **GHOST -> NONZERO HODGE DUAL.** -/
theorem ghostHodgeDual_ne_zero
    {G : GeometricCycleClassSpine V H}
    (E : OmniversalSeparatorGhost G)
    (P : PerfectHodgeFiberPairing (V := V) (H := H) E.weight) :
    P.dualClass (separatorOnHodge E.separator.detector) ≠ 0 := by
  exact P.dualClass_ne_zero _ (separatorOnHodge_ne_zero E)

/-- **GHOST -> ALGEBRAIC-HODGE ORTHOGONALITY.** -/
theorem ghostHodgeDual_orthogonal
    {G : GeometricCycleClassSpine V H}
    (E : OmniversalSeparatorGhost G)
    (P : PerfectHodgeFiberPairing (V := V) (H := H) E.weight) :
    OrthogonalToAlgebraicHodge P
      (P.dualClass (separatorOnHodge E.separator.detector)) := by
  intro alpha halpha
  rw [P.pair_dualClass]
  have hker :
      pointCycleClassSpan E.weight (H.cycleClass E.weight) ≤
        LinearMap.ker E.separator.detector :=
    (annihilatesPointCycles_iff_atomicSpan_le_ker
      E.weight (H.cycleClass E.weight) E.separator.detector).mp
      E.separator.annihilates_atoms
  exact hker halpha

/-- The polarized ghost dual still pairs nontrivially with the Hodge direction
selected by the original separator. -/
theorem ghostHodgeDual_detects
    {G : GeometricCycleClassSpine V H}
    (E : OmniversalSeparatorGhost G)
    (P : PerfectHodgeFiberPairing (V := V) (H := H) E.weight) :
    P.pair
        (P.dualClass (separatorOnHodge E.separator.detector))
        E.hodge ≠ 0 := by
  rw [P.pair_dualClass]
  exact E.separator.detects

/-- Concrete Hodge-fiber residual obstruction after polarization. -/
structure PolarizedHodgeGhost
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (P : PerfectHodgeFiberPairing (V := V) (H := H) p) where
  dual : HFiber (V := V) (H := H) p
  dual_ne_zero : dual ≠ 0
  orthogonal_algebraic : OrthogonalToAlgebraicHodge P dual
  witness : HFiber (V := V) (H := H) p
  detects_witness : P.pair dual witness ≠ 0

noncomputable def OmniversalSeparatorGhost.toPolarizedHodgeGhost
    {G : GeometricCycleClassSpine V H}
    (E : OmniversalSeparatorGhost G)
    (P : PerfectHodgeFiberPairing (V := V) (H := H) E.weight) :
    PolarizedHodgeGhost G E.weight P where
  dual := P.dualClass (separatorOnHodge E.separator.detector)
  dual_ne_zero := ghostHodgeDual_ne_zero E P
  orthogonal_algebraic := ghostHodgeDual_orthogonal E P
  witness := E.hodge
  detects_witness := ghostHodgeDual_detects E P

/-- **HODGE FAILURE -> NONZERO POLARIZED ORTHOGONAL HODGE CLASS.** -/
theorem failure_yields_polarizedHodgeGhost
    (G : GeometricCycleClassSpine V H)
    (P : ∀ p : Nat, PerfectHodgeFiberPairing (V := V) (H := H) p)
    (hnot : ¬ BigradedBettiHodgeStatement V H) :
    ∃ p : Nat, Nonempty (PolarizedHodgeGhost G p (P p)) := by
  rcases (not_hodge_iff_nonempty_omniversalSeparatorGhost G).mp hnot with ⟨E⟩
  exact ⟨E.weight, ⟨E.toPolarizedHodgeGhost (P E.weight)⟩⟩

#check PerfectHodgeFiberPairing
#check PerfectHodgeFiberPairing.dualClass
#check separatorOnHodge
#check IsAlgebraicHodge
#check separatorOnHodge_ne_zero
#check OrthogonalToAlgebraicHodge
#check ghostHodgeDual_ne_zero
#check ghostHodgeDual_orthogonal
#check ghostHodgeDual_detects
#check PolarizedHodgeGhost
#check OmniversalSeparatorGhost.toPolarizedHodgeGhost
#check failure_yields_polarizedHodgeGhost

#print axioms PerfectHodgeFiberPairing.pair_dualClass
#print axioms separatorOnHodge_ne_zero
#print axioms ghostHodgeDual_orthogonal
#print axioms ghostHodgeDual_detects
#print axioms failure_yields_polarizedHodgeGhost

end GSTClassicalHodgePolarizedHodgeGhost
