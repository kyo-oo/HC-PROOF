import GSTClassicalHodgeGradedGeometricOrbitAlgebra
import GSTClassicalHodgeSeparatorProbe

/-!
# GST CLASSICAL HODGE — GRADED ORBIT ANNIHILATOR / OMNIVERSAL TOMOGRAPHY

The upgraded graded geometric program already has the decisive forward law:
every program state reached from the canonical geometric origin is the genuine
cycle class of the native program executed on the codimension-zero fundamental
cycle.  Hence the geometric program orbit is an intrinsically algebraic
submodule of ambient rational cohomology.

This file dualizes the *remaining* reachability problem rather than adding a
new realization assumption.

A `GradedOrbitSeparator` is a rational detector which:

* kills the complete verified graded geometric orbit at one weight;
* nevertheless detects one genuine rational `(p,p)` Hodge state.

The key results are exact:

* Hodge failure always yields such an orbit separator, because every verified
  program state is already an actual cycle class;
* absence of orbit separators is **equivalent** to cyclicity of the graded
  geometric orbit in the whole Hodge sector;
* because the program language is already closed under rational addition and
  scaling, annihilating the orbit is exactly the concrete statement that the
  detector vanishes on the output of **every** finite mixed geometric program
  from the canonical origin;
* consequently Hodge reduces to an omniversal tomography law: every rational
  detector which sees a genuine Hodge state must see at least one actual
  projective/cut program state generated from the geometric origin.

No matrix-unit naturality, basis-cycle family, finite-sheet externalization,
or cycle-class surjectivity is assumed in this reduction.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeGradedOrbitAnnihilator

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeAtomicAnnihilator
open GSTClassicalHodgeSeparatorProbe
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeGradedGeometricProgramOrbit
open GSTClassicalHodgeGradedGeometricOrbitAlgebra

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

abbrev AmbientCoh (p : Nat) :=
  RationalSingularCohomology H.analytification (2 * p)

/-- A nonzero Hodge state invisible to the entire verified graded geometric
program orbit.  This is the exact dual obstruction to orbit cyclicity. -/
structure GradedOrbitSeparator
    (G : GeometricCycleClassSpine V H)
    (p : Nat) where
  alpha : ClassicalHodgeFiber V H p
  detector : AmbientCoh (H := H) p →ₗ[ℚ] ℚ
  annihilates_orbit :
    ∀ beta : AmbientCoh (H := H) p,
      beta ∈ geometricProgramOrbitModule G p → detector beta = 0
  detects_alpha : detector alpha.1 ≠ 0

namespace GradedOrbitSeparator

variable {G : GeometricCycleClassSpine V H}
variable {p : Nat}

/-- The detector's completed Hodge-coordinate probe sees the separator state
nontrivially. -/
theorem probePairing_ne_zero
    (S : GradedOrbitSeparator G p) :
    hodgeFiberPairing
        ((classicalHodgeBasis V H p).repr S.alpha)
        (functionalHodgeProbe V H p S.detector) ≠ 0 := by
  exact (functional_detects_hodge_iff_probe_pairing_ne_zero
    V H p S.detector S.alpha).mp S.detects_alpha

/-- Orbit annihilation is not a span-level abstraction: because the upgraded
program language itself contains addition and rational scaling, it says exactly
that the detector vanishes on every finite mixed geometric program from the
canonical origin. -/
theorem annihilates_every_program
    (S : GradedOrbitSeparator G p)
    (P : GradedGeometricProgram V 0 p) :
    S.detector
      (P.cohomologyEval G (geometricOriginClass V H)) = 0 := by
  apply S.annihilates_orbit
  exact ⟨P, rfl⟩

/-- Every atomic Hodge-failure probe automatically annihilates the stronger
verified geometric-program orbit, since that orbit lies in the genuine
cycle-class range. -/
noncomputable def ofAtomicSeparatorProbe
    (G : GeometricCycleClassSpine V H)
    (S : AtomicSeparatorProbe V H p) :
    GradedOrbitSeparator G p where
  alpha := S.alpha
  detector := S.detector
  annihilates_orbit := by
    intro beta hbeta
    have hrange : beta ∈ LinearMap.range (H.cycleClass p) :=
      geometricProgramOrbitModule_le_cycleClass_range G p hbeta
    have hatomic : beta ∈ pointCycleClassSpan p (H.cycleClass p) := by
      rwa [smoothProjective_cycleClass_range_eq_atomic_span V H p] at hrange
    have hker :
        pointCycleClassSpan p (H.cycleClass p) ≤ LinearMap.ker S.detector :=
      (annihilatesPointCycles_iff_atomicSpan_le_ker
        p (H.cycleClass p) S.detector).mp S.annihilates_atoms
    exact hker hatomic
  detects_alpha :=
    (functional_detects_hodge_iff_probe_pairing_ne_zero
      V H p S.detector S.alpha).mpr S.pairing_nonzero

end GradedOrbitSeparator

/-- For an arbitrary detector, killing the intrinsic orbit module is exactly
killing every concrete program readout from the canonical geometric origin. -/
theorem annihilates_geometricProgramOrbit_iff_all_program_readouts_zero
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (ell : AmbientCoh (H := H) p →ₗ[ℚ] ℚ) :
    (∀ beta : AmbientCoh (H := H) p,
        beta ∈ geometricProgramOrbitModule G p → ell beta = 0) ↔
      ∀ P : GradedGeometricProgram V 0 p,
        ell (P.cohomologyEval G (geometricOriginClass V H)) = 0 := by
  constructor
  · intro h P
    exact h _ ⟨P, rfl⟩
  · intro h beta hbeta
    rcases hbeta with ⟨P, rfl⟩
    exact h P

/-- **FAILURE-TO-ORBIT-SEPARATOR THEOREM.**
Every failure of the classical Stage-2G target produces a detector which is
nonzero on a genuine Hodge class while vanishing on every state generated by
the full verified mixed projective/cut program algebra. -/
theorem not_hodge_yields_gradedOrbitSeparator
    (G : GeometricCycleClassSpine V H)
    (hnot : ¬ BigradedBettiHodgeStatement V H) :
    ∃ p : Nat, Nonempty (GradedOrbitSeparator G p) := by
  obtain ⟨p, hS⟩ :=
    (not_bigradedBettiHodgeStatement_iff_exists_separatorProbe V H).mp hnot
  rcases hS with ⟨S⟩
  exact ⟨p, ⟨GradedOrbitSeparator.ofAtomicSeparatorProbe G S⟩⟩

/-- Cyclicity of the verified graded orbit excludes every orbit separator. -/
theorem no_gradedOrbitSeparator_of_cyclic
    (G : GeometricCycleClassSpine V H)
    (hcyclic : GradedGeometricOrbitModuleCyclic G) :
    ∀ p : Nat, IsEmpty (GradedOrbitSeparator G p) := by
  intro p
  refine ⟨?_⟩
  intro S
  apply S.detects_alpha
  exact S.annihilates_orbit S.alpha.1 (hcyclic p S.alpha.2)

/-- Conversely, if one Hodge class lies outside the verified orbit module,
pure rational linear separation manufactures an orbit separator. -/
theorem gradedOrbitSeparator_of_not_mem
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (alpha : ClassicalHodgeFiber V H p)
    (hnot : alpha.1 ∉ geometricProgramOrbitModule G p) :
    Nonempty (GradedOrbitSeparator G p) := by
  obtain ⟨ell, hell, hdetect⟩ :=
    exists_linearFunctional_separating_submodule
      (geometricProgramOrbitModule G p) alpha.1 hnot
  exact ⟨{
    alpha := alpha
    detector := ell
    annihilates_orbit := hell
    detects_alpha := hdetect
  }⟩

/-- **EXACT DUALITY: ORBIT CYCLICITY IFF NO ORBIT SEPARATOR.**
This is stronger than a one-way Hodge criterion: it identifies the precise
functional obstruction to the upgraded geometry cosmology being cyclic in the
whole genuine Hodge sector. -/
theorem gradedGeometricOrbitModuleCyclic_iff_no_separator
    (G : GeometricCycleClassSpine V H) :
    GradedGeometricOrbitModuleCyclic G ↔
      ∀ p : Nat, IsEmpty (GradedOrbitSeparator G p) := by
  constructor
  · exact no_gradedOrbitSeparator_of_cyclic G
  · intro hno p alpha halpha
    by_contra hnot
    let alphaH : ClassicalHodgeFiber V H p := ⟨alpha, halpha⟩
    have hsep : Nonempty (GradedOrbitSeparator G p) :=
      gradedOrbitSeparator_of_not_mem G p alphaH hnot
    rcases hsep with ⟨S⟩
    exact (hno p).false S

/-- Omniversal tomography formulation.  A detector which vanishes on every
actual mixed geometric program state must vanish on the entire genuine Hodge
sector. -/
def OmniversalProgramTomography
    (G : GeometricCycleClassSpine V H) : Prop :=
  ∀ p : Nat,
  ∀ ell : AmbientCoh (H := H) p →ₗ[ℚ] ℚ,
    (∀ P : GradedGeometricProgram V 0 p,
      ell (P.cohomologyEval G (geometricOriginClass V H)) = 0) →
    ∀ alpha : AmbientCoh (H := H) p,
      alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p) →
      ell alpha = 0

/-- Cyclicity immediately gives omniversal tomography. -/
theorem omniversalProgramTomography_of_cyclic
    (G : GeometricCycleClassSpine V H)
    (hcyclic : GradedGeometricOrbitModuleCyclic G) :
    OmniversalProgramTomography G := by
  intro p ell hprogram alpha halpha
  have horbit : alpha ∈ geometricProgramOrbitModule G p := hcyclic p halpha
  have hann :
      ∀ beta : AmbientCoh (H := H) p,
        beta ∈ geometricProgramOrbitModule G p → ell beta = 0 :=
    (annihilates_geometricProgramOrbit_iff_all_program_readouts_zero
      G p ell).mpr hprogram
  exact hann alpha horbit

/-- Conversely, tomography forces every Hodge state into the verified orbit:
otherwise the separating functional supplied by quotient duality would be
invisible to all programs yet detect that state. -/
theorem cyclic_of_omniversalProgramTomography
    (G : GeometricCycleClassSpine V H)
    (hT : OmniversalProgramTomography G) :
    GradedGeometricOrbitModuleCyclic G := by
  intro p alpha halpha
  by_contra hnot
  obtain ⟨ell, hell, hdetect⟩ :=
    exists_linearFunctional_separating_submodule
      (geometricProgramOrbitModule G p) alpha hnot
  have hprogram :
      ∀ P : GradedGeometricProgram V 0 p,
        ell (P.cohomologyEval G (geometricOriginClass V H)) = 0 :=
    (annihilates_geometricProgramOrbit_iff_all_program_readouts_zero
      G p ell).mp hell
  exact hdetect (hT p ell hprogram alpha halpha)

/-- **OMNIVERSAL TOMOGRAPHY EQUIVALENCE.**
The entire classical reachability problem is exactly the statement that the
verified native geometric programs separate the dual of the true Hodge sector. -/
theorem omniversalProgramTomography_iff_orbitCyclic
    (G : GeometricCycleClassSpine V H) :
    OmniversalProgramTomography G ↔ GradedGeometricOrbitModuleCyclic G := by
  exact ⟨cyclic_of_omniversalProgramTomography G,
    omniversalProgramTomography_of_cyclic G⟩

/-- Hodge landing from the tomography law, with no matrix-unit or per-sheet
realization hypothesis in the public theorem. -/
theorem bigradedBettiHodge_of_omniversalProgramTomography
    (G : GeometricCycleClassSpine V H)
    (hT : OmniversalProgramTomography G) :
    BigradedBettiHodgeStatement V H := by
  exact bigradedBettiHodge_of_gradedGeometricOrbitModuleCyclic G
    (cyclic_of_omniversalProgramTomography G hT)

/-- Contrapositive tomography failure generated by any Hodge failure. -/
theorem not_hodge_yields_failed_omniversal_tomography
    (G : GeometricCycleClassSpine V H)
    (hnot : ¬ BigradedBettiHodgeStatement V H) :
    ¬ OmniversalProgramTomography G := by
  intro hT
  exact hnot (bigradedBettiHodge_of_omniversalProgramTomography G hT)

#check GradedOrbitSeparator
#check GradedOrbitSeparator.probePairing_ne_zero
#check GradedOrbitSeparator.annihilates_every_program
#check GradedOrbitSeparator.ofAtomicSeparatorProbe
#check annihilates_geometricProgramOrbit_iff_all_program_readouts_zero
#check not_hodge_yields_gradedOrbitSeparator
#check gradedOrbitSeparator_of_not_mem
#check gradedGeometricOrbitModuleCyclic_iff_no_separator
#check OmniversalProgramTomography
#check omniversalProgramTomography_iff_orbitCyclic
#check bigradedBettiHodge_of_omniversalProgramTomography
#check not_hodge_yields_failed_omniversal_tomography

#print axioms GradedOrbitSeparator.ofAtomicSeparatorProbe
#print axioms not_hodge_yields_gradedOrbitSeparator
#print axioms gradedGeometricOrbitModuleCyclic_iff_no_separator
#print axioms omniversalProgramTomography_iff_orbitCyclic
#print axioms bigradedBettiHodge_of_omniversalProgramTomography

end GSTClassicalHodgeGradedOrbitAnnihilator
