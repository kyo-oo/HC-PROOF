import GSTClassicalHodgeGradedOrbitAnnihilator
import GSTClassicalHodgeAtomicDefectDuality

/-!
# GST CLASSICAL HODGE — GRADED ORBIT COMPLETED TOMOGRAPHY

The annihilator form of graded geometric reachability still speaks in ambient
linear functionals.  The limitless Hodge cosmology has a more intrinsic dual:
finite-support multiplicity addresses paired with arbitrary completed probes.

This module identifies the two formulations exactly.

Every completed probe on a genuine weight-p Hodge fiber defines a linear
functional on that fiber through basis coordinates.  Rational linear extension
then produces an ambient cohomology detector.  Conversely every ambient
detector restricts to its completed coordinate probe.  Therefore the
omniversal geometric-program tomography theorem can be stated entirely inside
the compact/completed limitless address universe:

  if a completed probe is blind to every genuine mixed geometric program state
  at weight p, it is blind to every genuine Hodge state at weight p.

The total fibered version retains all multiplicity labels and does not pass
through `forgetMultiplicityToGST`.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeGradedOrbitCompletedTomography

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicDefectDuality
open GSTClassicalHodgeSeparatorProbe
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeGradedGeometricProgramOrbit
open GSTClassicalHodgeGradedGeometricOrbitAlgebra
open GSTClassicalHodgeGradedOrbitAnnihilator

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- The linear functional on a genuine Hodge fiber represented by one
completed basis probe. -/
noncomputable def hodgeProbeFunctional
    (p : Nat)
    (g : HodgeFiberProbe V H p) :
    ClassicalHodgeFiber V H p →ₗ[ℚ] ℚ :=
  (hodgeFiberProbeLinearMap V H p g).comp
    (classicalHodgeBasis V H p).repr.toLinearMap

@[simp]
theorem hodgeProbeFunctional_apply
    (p : Nat)
    (g : HodgeFiberProbe V H p)
    (alpha : ClassicalHodgeFiber V H p) :
    hodgeProbeFunctional p g alpha =
      hodgeFiberPairing ((classicalHodgeBasis V H p).repr alpha) g := by
  rfl

/-- Extend a completed Hodge probe from the genuine Hodge subspace to an
ambient rational cohomology detector.  The extension is used only as a duality
bridge; no algebraicity assertion enters its construction. -/
noncomputable def ambientExtensionOfHodgeProbe
    (p : Nat)
    (g : HodgeFiberProbe V H p) :
    RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ] ℚ :=
  Classical.choose (LinearMap.exists_extend (hodgeProbeFunctional p g))

/-- The ambient extension restricts exactly to the original completed probe. -/
theorem ambientExtension_comp_hodgeSubtype
    (p : Nat)
    (g : HodgeFiberProbe V H p) :
    (ambientExtensionOfHodgeProbe p g).comp
        (rationalHodgeSubspace (H.hodgeBigrading p)).subtype =
      hodgeProbeFunctional p g :=
  Classical.choose_spec (LinearMap.exists_extend (hodgeProbeFunctional p g))

/-- Evaluation of the chosen ambient extension on a true Hodge state is exactly
the compact/completed coordinate pairing. -/
theorem ambientExtension_on_hodge
    (p : Nat)
    (g : HodgeFiberProbe V H p)
    (alpha : ClassicalHodgeFiber V H p) :
    ambientExtensionOfHodgeProbe p g alpha.1 =
      hodgeFiberPairing ((classicalHodgeBasis V H p).repr alpha) g := by
  have h := LinearMap.congr_fun
    (ambientExtension_comp_hodgeSubtype p g) alpha
  simpa [hodgeProbeFunctional_apply] using h

/-- Every mixed geometric program output from the canonical origin is a true
Hodge state, because the whole verified orbit lies inside the Hodge sector. -/
noncomputable def programHodgeState
    (G : GeometricCycleClassSpine V H)
    {p : Nat}
    (P : GradedGeometricProgram V 0 p) :
    ClassicalHodgeFiber V H p :=
  ⟨P.cohomologyEval G (geometricOriginClass V H),
    geometricProgramOrbitModule_le_hodge G p ⟨P, rfl⟩⟩

@[simp]
theorem programHodgeState_val
    (G : GeometricCycleClassSpine V H)
    {p : Nat}
    (P : GradedGeometricProgram V 0 p) :
    (programHodgeState G P).1 =
      P.cohomologyEval G (geometricOriginClass V H) :=
  rfl

/-- Completed-probe formulation at one weight. -/
def CompletedProgramTomography
    (G : GeometricCycleClassSpine V H) : Prop :=
  ∀ p : Nat,
  ∀ g : HodgeFiberProbe V H p,
    (∀ P : GradedGeometricProgram V 0 p,
      hodgeFiberPairing
        ((classicalHodgeBasis V H p).repr (programHodgeState G P)) g = 0) →
    ∀ alpha : ClassicalHodgeFiber V H p,
      hodgeFiberPairing ((classicalHodgeBasis V H p).repr alpha) g = 0

/-- Ambient omniversal tomography implies completed-probe tomography. -/
theorem completedProgramTomography_of_omniversal
    (G : GeometricCycleClassSpine V H)
    (hT : OmniversalProgramTomography G) :
    CompletedProgramTomography G := by
  intro p g hprogram alpha
  let ell := ambientExtensionOfHodgeProbe (H := H) p g
  have hprogram' :
      ∀ P : GradedGeometricProgram V 0 p,
        ell (P.cohomologyEval G (geometricOriginClass V H)) = 0 := by
    intro P
    rw [show P.cohomologyEval G (geometricOriginClass V H) =
      (programHodgeState G P).1 by rfl]
    rw [ambientExtension_on_hodge p g (programHodgeState G P)]
    exact hprogram P
  have hzero := hT p ell hprogram' alpha.1 alpha.2
  rw [ambientExtension_on_hodge p g alpha] at hzero
  exact hzero

/-- Conversely every ambient detector is represented on the Hodge fiber by its
completed coordinate probe, so completed tomography recovers the ambient
formulation exactly. -/
theorem omniversalProgramTomography_of_completed
    (G : GeometricCycleClassSpine V H)
    (hT : CompletedProgramTomography G) :
    OmniversalProgramTomography G := by
  intro p ell hprogram alpha halpha
  let g := functionalHodgeProbe V H p ell
  have hprogram' :
      ∀ P : GradedGeometricProgram V 0 p,
        hodgeFiberPairing
          ((classicalHodgeBasis V H p).repr (programHodgeState G P)) g = 0 := by
    intro P
    have hprobe := restrictedHodgeFunctional_eq_probe_pairing
      V H p ell (programHodgeState G P)
    have hz := hprogram P
    change ell (programHodgeState G P).1 = _ at hprobe
    rw [hz] at hprobe
    exact hprobe.symm
  let alphaH : ClassicalHodgeFiber V H p := ⟨alpha, halpha⟩
  have hpair := hT p g hprogram' alphaH
  have hprobe := restrictedHodgeFunctional_eq_probe_pairing
    V H p ell alphaH
  change ell alpha = _ at hprobe
  rw [hpair] at hprobe
  exact hprobe

/-- **COMPLETED TOMOGRAPHY EQUIVALENCE.** -/
theorem completedProgramTomography_iff_omniversal
    (G : GeometricCycleClassSpine V H) :
    CompletedProgramTomography G ↔ OmniversalProgramTomography G := by
  exact ⟨omniversalProgramTomography_of_completed G,
    completedProgramTomography_of_omniversal G⟩

/-- Hence completed-probe tomography is also exactly equivalent to cyclicity
of the genuine graded geometric program orbit. -/
theorem completedProgramTomography_iff_orbitCyclic
    (G : GeometricCycleClassSpine V H) :
    CompletedProgramTomography G ↔ GradedGeometricOrbitModuleCyclic G := by
  rw [completedProgramTomography_iff_omniversal G]
  exact omniversalProgramTomography_iff_orbitCyclic G

/-- Restrict a total limitless completed probe to one genuine weight fiber. -/
def restrictFiberedProbe
    (p : Nat)
    (g : FiberedCompletedAddress V H) :
    HodgeFiberProbe V H p :=
  fun i => g ⟨p, i⟩

/-- Embed one fixed-weight completed probe into the total limitless fibered
probe universe without collapsing multiplicity. -/
def extendFiberedProbe
    (p : Nat)
    (g : HodgeFiberProbe V H p) :
    FiberedCompletedAddress V H :=
  fun s =>
    if hp : s.1 = p then
      match hp ▸ s.2 with
      | i => g i
    else 0

@[simp]
theorem extendFiberedProbe_at_weight
    (p : Nat)
    (g : HodgeFiberProbe V H p)
    (i : ClassicalHodgeBasisIndex V H p) :
    extendFiberedProbe p g ⟨p, i⟩ = g i := by
  simp [extendFiberedProbe]

/-- Pairing a fixed-weight Hodge state with a total completed probe is exactly
pairing its native basis coordinates against the restriction of that probe. -/
theorem fiberedPairing_weight_eq_hodgePairing
    (p : Nat)
    (alpha : ClassicalHodgeFiber V H p)
    (g : FiberedCompletedAddress V H) :
    fiberedPairing (fiberedWeightCoordinates V H p alpha) g =
      hodgeFiberPairing
        ((classicalHodgeBasis V H p).repr alpha)
        (restrictFiberedProbe p g) := by
  classical
  unfold fiberedPairing fiberedWeightCoordinates hodgeFiberPairing
  simp [weightFiberEmbedding, restrictFiberedProbe, Finsupp.sum_embDomain]

/-- Fixed-weight probes embed faithfully into the total fibered pairing. -/
theorem fiberedPairing_extendFiberedProbe
    (p : Nat)
    (alpha : ClassicalHodgeFiber V H p)
    (g : HodgeFiberProbe V H p) :
    fiberedPairing
        (fiberedWeightCoordinates V H p alpha)
        (extendFiberedProbe p g) =
      hodgeFiberPairing ((classicalHodgeBasis V H p).repr alpha) g := by
  rw [fiberedPairing_weight_eq_hodgePairing]
  congr
  funext i
  exact extendFiberedProbe_at_weight p g i

/-- Total limitless fibered formulation: every completed multiplicity probe
which is invisible to all genuine geometric programs at a weight is invisible
to the whole genuine Hodge fiber at that weight. -/
def FiberedProgramTomography
    (G : GeometricCycleClassSpine V H) : Prop :=
  ∀ p : Nat,
  ∀ g : FiberedCompletedAddress V H,
    (∀ P : GradedGeometricProgram V 0 p,
      fiberedPairing
        (fiberedWeightCoordinates V H p (programHodgeState G P)) g = 0) →
    ∀ alpha : ClassicalHodgeFiber V H p,
      fiberedPairing (fiberedWeightCoordinates V H p alpha) g = 0

/-- Completed fixed-weight tomography implies the total fibered form. -/
theorem fiberedProgramTomography_of_completed
    (G : GeometricCycleClassSpine V H)
    (hT : CompletedProgramTomography G) :
    FiberedProgramTomography G := by
  intro p g hprogram alpha
  rw [fiberedPairing_weight_eq_hodgePairing]
  apply hT p (restrictFiberedProbe p g)
  · intro P
    rw [← fiberedPairing_weight_eq_hodgePairing]
    exact hprogram P

/-- The total fibered formulation recovers every fixed-weight probe by faithful
extension, so it is equivalent to the completed formulation. -/
theorem completedProgramTomography_of_fibered
    (G : GeometricCycleClassSpine V H)
    (hT : FiberedProgramTomography G) :
    CompletedProgramTomography G := by
  intro p g hprogram alpha
  have hprogram' :
      ∀ P : GradedGeometricProgram V 0 p,
        fiberedPairing
          (fiberedWeightCoordinates V H p (programHodgeState G P))
          (extendFiberedProbe p g) = 0 := by
    intro P
    rw [fiberedPairing_extendFiberedProbe]
    exact hprogram P
  have hout := hT p (extendFiberedProbe p g) hprogram' alpha
  rw [fiberedPairing_extendFiberedProbe] at hout
  exact hout

/-- **LIMITLESS FIBERED TOMOGRAPHY EQUIVALENCE.** -/
theorem fiberedProgramTomography_iff_orbitCyclic
    (G : GeometricCycleClassSpine V H) :
    FiberedProgramTomography G ↔ GradedGeometricOrbitModuleCyclic G := by
  constructor
  · intro h
    exact (completedProgramTomography_iff_orbitCyclic G).mp
      (completedProgramTomography_of_fibered G h)
  · intro h
    exact fiberedProgramTomography_of_completed G
      ((completedProgramTomography_iff_orbitCyclic G).mpr h)

/-- Full Hodge landing from total limitless fibered tomography. -/
theorem bigradedBettiHodge_of_fiberedProgramTomography
    (G : GeometricCycleClassSpine V H)
    (hT : FiberedProgramTomography G) :
    BigradedBettiHodgeStatement V H := by
  exact bigradedBettiHodge_of_gradedGeometricOrbitModuleCyclic G
    ((fiberedProgramTomography_iff_orbitCyclic G).mp hT)

#check hodgeProbeFunctional
#check ambientExtensionOfHodgeProbe
#check ambientExtension_on_hodge
#check programHodgeState
#check CompletedProgramTomography
#check completedProgramTomography_iff_orbitCyclic
#check restrictFiberedProbe
#check extendFiberedProbe
#check fiberedPairing_weight_eq_hodgePairing
#check FiberedProgramTomography
#check fiberedProgramTomography_iff_orbitCyclic
#check bigradedBettiHodge_of_fiberedProgramTomography

#print axioms ambientExtension_on_hodge
#print axioms completedProgramTomography_iff_orbitCyclic
#print axioms fiberedProgramTomography_iff_orbitCyclic
#print axioms bigradedBettiHodge_of_fiberedProgramTomography

end GSTClassicalHodgeGradedOrbitCompletedTomography
