import GSTClassicalHodgeGradedOrbitSingleProgramCollapse
import GSTClassicalHodgeOmniversalSeparatorGhostCrown

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
#check hodge_of_fullCorrespondenceGSTPlane
#check nativeCycle_of_fullCorrespondenceGSTPlane

#print axioms fullCorrespondencePlane_iff_orbitCyclic
#print axioms fullCorrespondencePlane_iff_singleProgramGeneration
#print axioms basisCycle_spec
#print axioms hodge_of_fullCorrespondenceGSTPlane

end GSTClassicalHodgeFullCorrespondenceGSTPlaneCompletion
