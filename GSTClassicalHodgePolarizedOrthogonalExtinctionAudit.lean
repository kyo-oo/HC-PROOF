import GSTClassicalHodgePolarizedHodgeGhost
import GSTClassicalHodgeAtomicDefectDuality

/-!
# GST CLASSICAL HODGE — POLARIZED ORTHOGONAL EXTINCTION AUDIT

After restricting an omniversal separator to the genuine rational `(p,p)`
Hodge fiber, a perfect pairing turns failure into a nonzero Hodge vector
orthogonal to every algebraic Hodge vector.

This file audits the tempting next shortcut.

The statement

  every nonzero Hodge vector has nonzero pairing with some algebraic Hodge
  vector

looks weaker than Hodge because it asks only for detection, not an explicit
cycle representative.  Under a perfect pairing it is nevertheless exactly the
statement that the algebraic Hodge subspace has trivial orthogonal complement;
for the ghost argument it already eliminates every separator and therefore
implies the full Stage-2G Hodge target.

Conversely, if Hodge holds, the perfect pairing itself supplies such an
algebraic detector for every nonzero vector.  Thus universal algebraic pairing
separation is Hodge-equivalent in the present semantics and must not be
introduced as a free geometric axiom.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgePolarizedOrthogonalExtinctionAudit

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgePolarizedHodgeGhost

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Universal pairing separation by genuine algebraic Hodge vectors. -/
def AlgebraicPairingSeparates
    (P : ∀ p : Nat,
      PerfectHodgeFiberPairing (V := V) (H := H) p) : Prop :=
  ∀ p : Nat,
  ∀ u : ClassicalHodgeFiber V H p,
    u ≠ 0 →
      ∃ a : ClassicalHodgeFiber V H p,
        IsAlgebraicHodge a ∧ (P p).pair u a ≠ 0

/-- Hodge saturation gives algebraic pairing separation immediately: choose a
pairing witness supplied by nondegeneracy and use Hodge to recognize that
witness as algebraic. -/
theorem algebraicPairingSeparates_of_hodge
    (P : ∀ p : Nat,
      PerfectHodgeFiberPairing (V := V) (H := H) p)
    (hHodge : BigradedBettiHodgeStatement V H) :
    AlgebraicPairingSeparates P := by
  intro p u hu
  have hdual0 : (P p).toDual u ≠ 0 := by
    intro hz
    have hinj := (P p).toDual_bijective.1
    have : u = 0 := hinj (by simpa using hz)
    exact hu this
  have hex : ∃ a : ClassicalHodgeFiber V H p,
      (P p).pair u a ≠ 0 := by
    by_contra h
    push_neg at h
    apply hdual0
    apply LinearMap.ext
    intro a
    simpa [PerfectHodgeFiberPairing.toDual] using h a
  rcases hex with ⟨a, ha⟩
  refine ⟨a, ?_, ha⟩
  exact (bigradedBettiHodgeStatement_iff_atomic_span V H).mp hHodge p a.2

/-- Pairing separation eliminates every polarized Hodge ghost. -/
theorem no_polarizedHodgeGhost_of_separation
    (G : GeometricCycleClassSpine V H)
    (P : ∀ p : Nat,
      PerfectHodgeFiberPairing (V := V) (H := H) p)
    (hsep : AlgebraicPairingSeparates P)
    (p : Nat) :
    IsEmpty (PolarizedHodgeGhost G p (P p)) := by
  refine ⟨?_⟩
  intro E
  rcases hsep p E.dual E.dual_ne_zero with ⟨a, haAlg, hpair⟩
  exact hpair (E.orthogonal_algebraic a haAlg)

/-- **UNIVERSAL ALGEBRAIC PAIRING SEPARATION IMPLIES HODGE.** -/
theorem hodge_of_algebraicPairingSeparates
    (G : GeometricCycleClassSpine V H)
    (P : ∀ p : Nat,
      PerfectHodgeFiberPairing (V := V) (H := H) p)
    (hsep : AlgebraicPairingSeparates P) :
    BigradedBettiHodgeStatement V H := by
  by_contra hnot
  rcases failure_yields_polarizedHodgeGhost G P hnot with ⟨p, ⟨E⟩⟩
  exact (no_polarizedHodgeGhost_of_separation G P hsep p).false E

/-- **PAIRING-SEPARATION AUDIT.**  Under a perfect Hodge-fiber pairing,
universal separation by algebraic Hodge vectors is equivalent to the complete
Stage-2G Hodge statement. -/
theorem algebraicPairingSeparates_iff_hodge
    (G : GeometricCycleClassSpine V H)
    (P : ∀ p : Nat,
      PerfectHodgeFiberPairing (V := V) (H := H) p) :
    AlgebraicPairingSeparates P ↔ BigradedBettiHodgeStatement V H := by
  constructor
  · exact hodge_of_algebraicPairingSeparates G P
  · exact algebraicPairingSeparates_of_hodge P

#check AlgebraicPairingSeparates
#check algebraicPairingSeparates_of_hodge
#check no_polarizedHodgeGhost_of_separation
#check hodge_of_algebraicPairingSeparates
#check algebraicPairingSeparates_iff_hodge

#print axioms algebraicPairingSeparates_of_hodge
#print axioms no_polarizedHodgeGhost_of_separation
#print axioms hodge_of_algebraicPairingSeparates
#print axioms algebraicPairingSeparates_iff_hodge

end GSTClassicalHodgePolarizedOrthogonalExtinctionAudit
