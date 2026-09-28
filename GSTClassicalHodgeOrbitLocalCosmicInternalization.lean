import GSTClassicalHodgeCosmologyTransformedClosure
import GSTClassicalHodgeProjectiveWordOrbit

/-!
# GST CLASSICAL HODGE — ORBIT-LOCAL COSMIC INTERNALIZATION

The transformed cosmology does not need a realization of the universal GST
transfer word on the entire Hodge fiber.  The irreducibility theorem consumes
that word only on the genuine graded geometric orbit, and every genuine
projective word already acts internally on that orbit by program composition.

This file therefore weakens the remaining bridge from a global operator
identity to a statewise internalization law:

* choose two Hodge sheets `i,j`;
* choose one Hodge state already in the genuine native program orbit;
* realize the value of the universal two-slot GST word on that one state by
  one verified graded geometric program (or, more concretely, one genuine
  projective operator word).

No equality is requested on non-orbit states.  No basis-cycle representative,
cycle-class surjectivity, matrix-unit externalization on the ambient Hodge
fiber, or arbitrary correspondence action is assumed.

Once this orbit-local law holds, the existing graded orbit module theorem
places every universal-two-slot image back in the native orbit.  The existing
rank-free GST saturation theorem then forces the nonzero orbit to be the whole
Hodge fiber.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeOrbitLocalCosmicInternalization

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeUniversalTwoSlotSaturation
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeProjectiveWordOrbit
open GSTClassicalHodgeGradedGeometricProgramOrbit
open GSTClassicalHodgeGradedGeometricOrbitAlgebra
open GSTClassicalHodgeLimitlessSpinePropagation
open GSTClassicalHodgeCosmologyTransformedClosure

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- The exact transformed bridge actually needed by rank-free saturation.
The universal two-slot GST word only has to be internalized on states already
belonging to the genuine native program orbit. -/
def OrbitLocalTwoSlotInternalization
    (G : GeometricCycleClassSpine V H)
    (p : Nat) : Prop :=
  ∀ i j : ClassicalHodgeBasisIndex V H p,
    ∀ alpha : ClassicalHodgeFiber V H p,
      alpha ∈ orbitHodgeSubmodule G p →
        ∃ P : GradedGeometricProgram V p p,
          P.cohomologyEval G alpha.1 =
            (liftFiniteHodgeOperator (pairBasisIndex i j)
              (forwardArsenalWord sourceSlot targetSlot) alpha).1

/-- Orbit-local internalization is already enough to obtain the transformed
universal-two-slot invariance.  The reason is purely cosmological: every
verified graded program acts internally on the intrinsic reachable module. -/
theorem transformedInvariant_of_orbitLocalInternalization
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (R : OrbitLocalTwoSlotInternalization G p) :
    TransformedTwoSlotOrbitInvariant G p := by
  intro i j alpha halpha
  rcases R i j alpha halpha with ⟨P, hP⟩
  have himage :
      P.cohomologyEval G alpha.1 ∈ geometricProgramOrbitModule G p :=
    program_maps_geometricProgramOrbitModule G P halpha
  rw [hP] at himage
  exact himage

/-- Fixed-weight transformed saturation from the strictly orbit-local bridge.
No action on the complement of the genuine native orbit is required. -/
theorem orbitHodgeSubmodule_eq_top_of_orbitLocalInternalization
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (R : OrbitLocalTwoSlotInternalization G p)
    (hspine : spineHodgeSeed G p ≠ 0) :
    orbitHodgeSubmodule G p = ⊤ := by
  exact orbitHodgeSubmodule_eq_top G p
    (transformedInvariant_of_orbitLocalInternalization G p R) hspine

/-- Exact fixed-weight Hodge landing from orbit-local cosmic internalization. -/
theorem hodge_weight_of_orbitLocalInternalization
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (R : OrbitLocalTwoSlotInternalization G p)
    (hspine : spineHodgeSeed G p ≠ 0) :
    rationalHodgeSubspace (H.hodgeBigrading p) ≤
      LinearMap.range (H.cycleClass p) := by
  exact hodge_weight_of_transformed_cosmology G p
    (transformedInvariant_of_orbitLocalInternalization G p R) hspine

/-- Global crown in the weakened, orbit-local form. -/
theorem bigradedBettiHodge_of_orbitLocalInternalization
    (G : GeometricCycleClassSpine V H)
    (R : ∀ p : Nat, OrbitLocalTwoSlotInternalization G p)
    (hspine : ∀ p : Nat,
      rationalHodgeSubspace (H.hodgeBigrading p) ≠ ⊥ →
        spineHodgeSeed G p ≠ 0) :
    BigradedBettiHodgeStatement V H := by
  exact bigradedBettiHodge_of_transformed_cosmology G
    (fun p => transformedInvariant_of_orbitLocalInternalization G p (R p))
    hspine

/-- Concrete projective-word form of the local bridge.  For each ordered pair
and each state already in the native orbit, only one genuine projective word
has to agree with the universal GST transfer on that single state. -/
def OrbitLocalProjectiveWordRealization
    (G : GeometricCycleClassSpine V H)
    (p : Nat) : Prop :=
  ∀ i j : ClassicalHodgeBasisIndex V H p,
    ∀ alpha : ClassicalHodgeFiber V H p,
      alpha ∈ orbitHodgeSubmodule G p →
        ∃ W : ProjectiveOperatorWord V p,
          (W.operatorPair G).cohomologyOperator alpha.1 =
            (liftFiniteHodgeOperator (pairBasisIndex i j)
              (forwardArsenalWord sourceSlot targetSlot) alpha).1

/-- A statewise projective word is a graded geometric program, hence the
projective-word version implies orbit-local cosmic internalization. -/
theorem orbitLocalInternalization_of_projectiveWords
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (R : OrbitLocalProjectiveWordRealization G p) :
    OrbitLocalTwoSlotInternalization G p := by
  intro i j alpha halpha
  rcases R i j alpha halpha with ⟨W, hW⟩
  refine ⟨GradedGeometricProgram.word W, ?_⟩
  exact hW

/-- The transformed Hodge problem is therefore closed by one projective word
per ordered pair and per *native-orbit state*, rather than a whole-fiber
externalization theorem. -/
theorem bigradedBettiHodge_of_orbitLocalProjectiveWords
    (G : GeometricCycleClassSpine V H)
    (R : ∀ p : Nat, OrbitLocalProjectiveWordRealization G p)
    (hspine : ∀ p : Nat,
      rationalHodgeSubspace (H.hodgeBigrading p) ≠ ⊥ →
        spineHodgeSeed G p ≠ 0) :
    BigradedBettiHodgeStatement V H := by
  exact bigradedBettiHodge_of_orbitLocalInternalization G
    (fun p => orbitLocalInternalization_of_projectiveWords G p (R p))
    hspine

/-- Ghost-free receipt: under orbit-local projective internalization and spine
survival there is no transformed omniversal separator obstruction. -/
theorem no_omniversalSeparatorGhost_of_orbitLocalProjectiveWords
    (G : GeometricCycleClassSpine V H)
    (R : ∀ p : Nat, OrbitLocalProjectiveWordRealization G p)
    (hspine : ∀ p : Nat,
      rationalHodgeSubspace (H.hodgeBigrading p) ≠ ⊥ →
        spineHodgeSeed G p ≠ 0) :
    IsEmpty (GSTClassicalHodgeOmniversalSeparatorGhostCrown.OmniversalSeparatorGhost G) := by
  exact no_omniversalSeparatorGhost_of_transformed_cosmology G
    (fun p => transformedInvariant_of_orbitLocalInternalization G p
      (orbitLocalInternalization_of_projectiveWords G p (R p)))
    hspine

#check OrbitLocalTwoSlotInternalization
#check transformedInvariant_of_orbitLocalInternalization
#check orbitHodgeSubmodule_eq_top_of_orbitLocalInternalization
#check hodge_weight_of_orbitLocalInternalization
#check bigradedBettiHodge_of_orbitLocalInternalization
#check OrbitLocalProjectiveWordRealization
#check orbitLocalInternalization_of_projectiveWords
#check bigradedBettiHodge_of_orbitLocalProjectiveWords
#check no_omniversalSeparatorGhost_of_orbitLocalProjectiveWords

#print axioms transformedInvariant_of_orbitLocalInternalization
#print axioms orbitHodgeSubmodule_eq_top_of_orbitLocalInternalization
#print axioms bigradedBettiHodge_of_orbitLocalProjectiveWords
#print axioms no_omniversalSeparatorGhost_of_orbitLocalProjectiveWords

end GSTClassicalHodgeOrbitLocalCosmicInternalization
