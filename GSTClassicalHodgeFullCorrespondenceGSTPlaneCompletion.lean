import GSTClassicalHodgeGradedOrbitSingleProgramCollapse
import GSTClassicalHodgeOmniversalSeparatorGhostCrown
import GSTClassicalHodgeNativeExecutablePlane

/-!
# GST CLASSICAL HODGE — FULL CORRESPONDENCE GST PLANE COMPLETION

This file fixes the terminal geometric meaning of GST plane completeness in
the strongest verified program language currently present in the repository.

An edge is not an abstract Hodge matrix unit. It is one executable
GradedCorrespondenceProgram built from genuine realized finite closed
correspondences, genuine principal cuts, rational addition/scaling and
ordered composition.
-/

set_option maxHeartbeats 180000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry

namespace GSTClassicalHodgeFullCorrespondenceGSTPlaneCompletion

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeGradedCorrespondenceProgramOrbit
open GSTClassicalHodgeGradedCorrespondenceProgramOrbit.GradedCorrespondenceProgram
open GSTClassicalHodgeGradedOrbitSingleProgramCollapse
open GSTClassicalHodgeExactClayStatement
open GSTClassicalHodgeAtomicAnnihilator
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeLimitlessSeparatorGhost
open GSTClassicalHodgeOmniversalSeparatorGhostCrown

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- FULL GEOMETRIC GST PLANE COMPLETENESS.
Every Hodge basis sheet is the exact cohomological output of one actual full
correspondence/cut program from the canonical codimension-zero origin. -/
def FullCorrespondenceGSTPlaneCompleteness
    (G : GeometricCycleClassSpine V H) : Prop :=
  ∀ q : Nat, ∀ j : ClassicalHodgeBasisIndex V H q,
    ∃ P : GradedCorrespondenceProgram V H 0 q,
      P.cohomologyEval G (correspondenceGeometricOriginClass V H) =
        (classicalHodgeBasis V H q j).1

theorem basis_mem_fullOrbit_of_plane
    (G : GeometricCycleClassSpine V H)
    (hplane : FullCorrespondenceGSTPlaneCompleteness G)
    (q : Nat)
    (j : ClassicalHodgeBasisIndex V H q) :
    (classicalHodgeBasis V H q j).1 ∈
      fullCorrespondenceOrbitModule G q := by
  change (classicalHodgeBasis V H q j).1 ∈ fullCorrespondenceOrbitSet G q
  obtain ⟨P,hP⟩ := hplane q j
  exact ⟨P,hP.symm⟩

theorem fullOrbitCyclic_of_plane
    (G : GeometricCycleClassSpine V H)
    (hplane : FullCorrespondenceGSTPlaneCompleteness G) :
    FullCorrespondenceOrbitCyclic G := by
  intro q alpha halpha
  rw [fullCorrespondenceOrbitSubspace_eq_module G q]
  let alphaH : ClassicalHodgeFiber V H q := ⟨alpha,halpha⟩
  rw [show alpha =
      ∑ j ∈ ((classicalHodgeBasis V H q).repr alphaH).support,
        ((classicalHodgeBasis V H q).repr alphaH j) •
          (classicalHodgeBasis V H q j).1 by
    exact congrArg Subtype.val ((classicalHodgeBasis V H q).sum_repr alphaH)]
  apply Submodule.sum_mem
  intro j hj
  exact (fullCorrespondenceOrbitModule G q).smul_mem
    ((classicalHodgeBasis V H q).repr alphaH j)
    (basis_mem_fullOrbit_of_plane G hplane q j)

theorem plane_of_fullOrbitCyclic
    (G : GeometricCycleClassSpine V H)
    (hcyclic : FullCorrespondenceOrbitCyclic G) :
    FullCorrespondenceGSTPlaneCompleteness G := by
  intro q j
  have hmem :
      (classicalHodgeBasis V H q j).1 ∈
        fullCorrespondenceOrbitSubspace G q :=
    hcyclic q (classicalHodgeBasis V H q j).2
  obtain ⟨P,hP⟩ :=
    (mem_fullCorrespondenceOrbitSubspace_iff_singleProgram
      G q (classicalHodgeBasis V H q j).1).1 hmem
  exact ⟨P,hP.symm⟩

theorem fullCorrespondencePlane_iff_orbitCyclic
    (G : GeometricCycleClassSpine V H) :
    FullCorrespondenceGSTPlaneCompleteness G ↔
      FullCorrespondenceOrbitCyclic G := by
  constructor
  · exact fullOrbitCyclic_of_plane G
  · exact plane_of_fullOrbitCyclic G

theorem fullCorrespondencePlane_iff_singleProgramGeneration
    (G : GeometricCycleClassSpine V H) :
    FullCorrespondenceGSTPlaneCompleteness G ↔
      (∀ q : Nat,
       ∀ alpha : RationalSingularCohomology H.analytification (2 * q),
         alpha ∈ rationalHodgeSubspace (H.hodgeBigrading q) →
         ∃ P : GradedCorrespondenceProgram V H 0 q,
           alpha =
             P.cohomologyEval G
               (correspondenceGeometricOriginClass V H)) :=
  (fullCorrespondencePlane_iff_orbitCyclic G).trans
    (fullCorrespondenceOrbitCyclic_iff_singleProgramGeneration G)

/-- Hodge state produced by one executable full correspondence/cut program
from the canonical geometric origin.  Hodge type is derived from the native
cycle-class range, not stored in the program. -/
noncomputable def fullProgramHodgeState
    (G : GeometricCycleClassSpine V H)
    {q : Nat}
    (P : GradedCorrespondenceProgram V H 0 q) :
    ClassicalHodgeFiber V H q :=
  ⟨P.cohomologyEval G (correspondenceGeometricOriginClass V H), by
    have hrange :=
      P.cohomologyEval_mem_cycleClass_range G
        (GSTClassicalHodgeCodimensionZeroFundamentalCycle
          .codimensionZeroFundamentalCycle V)
    rcases hrange with ⟨Z, hZ⟩
    rw [← hZ]
    exact G.algebraic_is_hodge q Z⟩

/-- Exact unrestricted fibered address of one executable full program state. -/
noncomputable def fullProgramFiberedAddress
    (G : GeometricCycleClassSpine V H)
    {q : Nat}
    (P : GradedCorrespondenceProgram V H 0 q) :
    FiberedHodgeAddress V H :=
  fiberedWeightCoordinates V H q (fullProgramHodgeState G P)

/-- Full-correspondence version of the old no-ghost pairing-totality law. -/
def FullCorrespondenceNativeOrbitPairingTotal
    (G : GeometricCycleClassSpine V H) : Prop :=
  ∀ q : Nat,
  ∀ g : FiberedCompletedAddress V H,
    (∀ s : FiberedHodgeIndex V H, s.1 ≠ q → g s = 0) →
    (∀ P : GradedCorrespondenceProgram V H 0 q,
      fiberedPairing (fullProgramFiberedAddress G P) g = 0) →
    g = 0

/-- A full program that hits one basis sheet has exactly the corresponding
Kronecker fibered address. -/
theorem fullProgramFiberedAddress_eq_basis
    (G : GeometricCycleClassSpine V H)
    {q : Nat}
    {j : ClassicalHodgeBasisIndex V H q}
    (P : GradedCorrespondenceProgram V H 0 q)
    (hP :
      P.cohomologyEval G (correspondenceGeometricOriginClass V H) =
        (classicalHodgeBasis V H q j).1) :
    fullProgramFiberedAddress G P =
      Finsupp.single (⟨q,j⟩ : FiberedHodgeIndex V H) 1 := by
  unfold fullProgramFiberedAddress fullProgramHodgeState
  rw [show
      (⟨P.cohomologyEval G (correspondenceGeometricOriginClass V H), by
          have hrange :=
            P.cohomologyEval_mem_cycleClass_range G
              (GSTClassicalHodgeCodimensionZeroFundamentalCycle
                .codimensionZeroFundamentalCycle V)
          rcases hrange with ⟨Z, hZ⟩
          rw [← hZ]
          exact G.algebraic_is_hodge q Z⟩ :
        ClassicalHodgeFiber V H q) =
      classicalHodgeBasis V H q j by
    apply Subtype.ext
    exact hP]
  exact fiberedWeightCoordinates_basis V H q j

/-- Full geometric plane completeness makes the executable full-program orbit
pairing-total coordinate by coordinate. -/
theorem fullPairingTotal_of_fullCorrespondencePlane
    (G : GeometricCycleClassSpine V H)
    (hplane : FullCorrespondenceGSTPlaneCompleteness G) :
    FullCorrespondenceNativeOrbitPairingTotal G := by
  intro q g hsupp hkill
  funext s
  rcases s with ⟨r,j⟩
  by_cases hr : r = q
  · subst r
    obtain ⟨P, hP⟩ := hplane q j
    have hk := hkill P
    rw [fullProgramFiberedAddress_eq_basis G P hP] at hk
    simpa [fiberedPairing_single_left] using hk
  · exact hsupp ⟨r,j⟩ hr

/-- Pairing-totality forces the full executable orbit to contain the entire
Hodge fiber.  If a Hodge state were missing, a separating functional would
yield a nonzero completed probe invisible to every full program. -/
theorem fullOrbitCyclic_of_fullPairingTotal
    (G : GeometricCycleClassSpine V H)
    (htotal : FullCorrespondenceNativeOrbitPairingTotal G) :
    FullCorrespondenceOrbitCyclic G := by
  intro q alpha halpha
  rw [fullCorrespondenceOrbitSubspace_eq_module G q]
  by_contra hnot
  obtain ⟨ell, hell, hdetect⟩ :=
    exists_linearFunctional_separating_submodule
      (fullCorrespondenceOrbitModule G q) alpha hnot
  let g : FiberedCompletedAddress V H :=
    separatorFiberedProbe (V := V) (H := H) q ell
  have hsupp :
      ∀ s : FiberedHodgeIndex V H, s.1 ≠ q → g s = 0 := by
    intro s hs
    rcases s with ⟨r,j⟩
    exact separatorFiberedProbe_at_other_weight
      (V := V) (H := H) q r hs ell j
  have hkill :
      ∀ P : GradedCorrespondenceProgram V H 0 q,
        fiberedPairing (fullProgramFiberedAddress G P) g = 0 := by
    intro P
    have horbit :
        P.cohomologyEval G (correspondenceGeometricOriginClass V H) ∈
          fullCorrespondenceOrbitModule G q := by
      change
        P.cohomologyEval G (correspondenceGeometricOriginClass V H) ∈
          fullCorrespondenceOrbitSet G q
      exact ⟨P, rfl⟩
    have hzero :
        ell (P.cohomologyEval G (correspondenceGeometricOriginClass V H)) = 0 :=
      hell _ horbit
    let a : ClassicalHodgeFiber V H q := fullProgramHodgeState G P
    have hp :=
      fiberedPairing_separatorProbe
        (V := V) (H := H) q ell a
    simpa [g, a, fullProgramFiberedAddress, fullProgramHodgeState]
      using hp.trans hzero
  have hg : g = 0 := htotal q g hsupp hkill
  let alphaH : ClassicalHodgeFiber V H q := ⟨alpha, halpha⟩
  have hp :=
    fiberedPairing_separatorProbe
      (V := V) (H := H) q ell alphaH
  have hz : ell alpha = 0 := by
    rw [hg] at hp
    simpa [g, alphaH, fiberedPairing] using hp
  exact hdetect hz

/-- **EXACT FULL-PROGRAM IDENTIFICATION.**
Executable full-correspondence GST plane completeness is exactly completed-probe
pairing totality for the same executable program orbit. -/
theorem fullCorrespondencePlane_iff_fullPairingTotal
    (G : GeometricCycleClassSpine V H) :
    FullCorrespondenceGSTPlaneCompleteness G ↔
      FullCorrespondenceNativeOrbitPairingTotal G := by
  constructor
  · exact fullPairingTotal_of_fullCorrespondencePlane G
  · intro htotal
    exact plane_of_fullOrbitCyclic G
      (fullOrbitCyclic_of_fullPairingTotal G htotal)

/-- A basis separator kills every executable full-program address because every
such state lies in the actual cycle-class range, hence in the atomic point-cycle
span annihilated by the separator. -/
theorem separatorProbe_kills_fullProgramAddress
    {G : GeometricCycleClassSpine V H}
    (E : OmniversalSeparatorGhost G)
    (P : GradedCorrespondenceProgram V H 0 E.weight) :
    fiberedPairing
      (fullProgramFiberedAddress G P)
      (separatorFiberedProbe
        (V := V) (H := H) E.weight E.separator.detector) = 0 := by
  rw [fiberedPairing_separatorProbe]
  have hrange :=
    P.cohomologyEval_mem_cycleClass_range G
      (GSTClassicalHodgeCodimensionZeroFundamentalCycle
        .codimensionZeroFundamentalCycle V)
  rw [smoothProjective_cycleClass_range_eq_atomic_span V H E.weight] at hrange
  have hker :
      pointCycleClassSpan E.weight (H.cycleClass E.weight) ≤
        LinearMap.ker E.separator.detector :=
    (annihilatesPointCycles_iff_atomicSpan_le_ker
      E.weight (H.cycleClass E.weight) E.separator.detector).mp
        E.separator.annihilates_atoms
  exact hker hrange

/-- Full-program pairing totality kills every omniversal separator ghost. -/
theorem noGhost_of_fullCorrespondencePairingTotal
    (G : GeometricCycleClassSpine V H)
    (htotal : FullCorrespondenceNativeOrbitPairingTotal G) :
    IsEmpty (OmniversalSeparatorGhost G) := by
  refine ⟨?_⟩
  intro E
  let g : FiberedCompletedAddress V H :=
    separatorFiberedProbe
      (V := V) (H := H) E.weight E.separator.detector
  have hsupp :
      ∀ s : FiberedHodgeIndex V H, s.1 ≠ E.weight → g s = 0 := by
    simpa [g] using omniversalSeparatorProbe_supported_on_weight E
  have hkill :
      ∀ P : GradedCorrespondenceProgram V H 0 E.weight,
        fiberedPairing (fullProgramFiberedAddress G P) g = 0 := by
    intro P
    simpa [g] using separatorProbe_kills_fullProgramAddress E P
  have hg0 : g = 0 := htotal E.weight g hsupp hkill
  have hgne : g ≠ 0 := by
    simpa [g] using basisSeparator_ghost_ne_zero E.separator
  exact hgne hg0

/-- Full-program pairing totality therefore lands in the exact Stage-2G Hodge
statement without any additional ghost closure package. -/
theorem hodge_of_fullCorrespondencePairingTotal
    (G : GeometricCycleClassSpine V H)
    (htotal : FullCorrespondenceNativeOrbitPairingTotal G) :
    BigradedBettiHodgeStatement V H :=
  (hodge_iff_no_omniversalSeparatorGhost G).2
    (noGhost_of_fullCorrespondencePairingTotal G htotal)

noncomputable def basisCycle
    (G : GeometricCycleClassSpine V H)
    (hplane : FullCorrespondenceGSTPlaneCompleteness G)
    (q : Nat)
    (j : ClassicalHodgeBasisIndex V H q) :
    codimensionCycles V.X q :=
  let P := Classical.choose (hplane q j)
  P.cycleEval G
    (GSTClassicalHodgeCodimensionZeroFundamentalCycle.codimensionZeroFundamentalCycle V)

theorem basisCycle_spec
    (G : GeometricCycleClassSpine V H)
    (hplane : FullCorrespondenceGSTPlaneCompleteness G)
    (q : Nat)
    (j : ClassicalHodgeBasisIndex V H q) :
    H.cycleClass q (basisCycle G hplane q j) =
      (classicalHodgeBasis V H q j).1 := by
  let P := Classical.choose (hplane q j)
  have hP := Classical.choose_spec (hplane q j)
  have hnat :=
    P.cycleClass_cycleEval G
      (GSTClassicalHodgeCodimensionZeroFundamentalCycle.codimensionZeroFundamentalCycle V)
  rw [hP] at hnat
  simpa [basisCycle, P, correspondenceGeometricOriginClass] using hnat

theorem hodge_of_fullCorrespondenceGSTPlane
    (G : GeometricCycleClassSpine V H)
    (hplane : FullCorrespondenceGSTPlaneCompleteness G) :
    BigradedBettiHodgeStatement V H := by
  exact (everyHodgeClassIsRationalAlgebraic_iff_stage2G H).1
    (exactHodge_of_fullCorrespondenceOrbitCyclic G
      (fullOrbitCyclic_of_plane G hplane))

theorem nativeCycle_of_fullCorrespondenceGSTPlane
    (G : GeometricCycleClassSpine V H)
    (hplane : FullCorrespondenceGSTPlaneCompleteness G)
    (q : Nat)
    (alpha : RationalSingularCohomology H.analytification (2 * q))
    (halpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading q)) :
    ∃ Z : codimensionCycles V.X q,
      H.cycleClass q Z = alpha :=
  hodge_of_fullCorrespondenceGSTPlane G hplane q alpha halpha

#check FullCorrespondenceGSTPlaneCompleteness
#check basis_mem_fullOrbit_of_plane
#check fullCorrespondencePlane_iff_orbitCyclic
#check fullCorrespondencePlane_iff_singleProgramGeneration
#check basisCycle
#check basisCycle_spec
#check fullProgramHodgeState
#check fullProgramFiberedAddress
#check FullCorrespondenceNativeOrbitPairingTotal
#check fullCorrespondencePlane_iff_fullPairingTotal
#check separatorProbe_kills_fullProgramAddress
#check noGhost_of_fullCorrespondencePairingTotal
#check hodge_of_fullCorrespondencePairingTotal
#check nativeExecutablePlane_of_fullCorrespondencePlane
#check hodge_of_fullCorrespondenceGSTPlane
#check nativeCycle_of_fullCorrespondenceGSTPlane

#print axioms fullCorrespondencePlane_iff_orbitCyclic
#print axioms fullCorrespondencePlane_iff_singleProgramGeneration
#print axioms basisCycle_spec
#print axioms fullCorrespondencePlane_iff_fullPairingTotal
#print axioms separatorProbe_kills_fullProgramAddress
#print axioms noGhost_of_fullCorrespondencePairingTotal
#print axioms hodge_of_fullCorrespondencePairingTotal
#print axioms nativeExecutablePlane_of_fullCorrespondencePlane
#print axioms hodge_of_fullCorrespondenceGSTPlane

end GSTClassicalHodgeFullCorrespondenceGSTPlaneCompletion
