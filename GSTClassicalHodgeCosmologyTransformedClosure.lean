import GSTClassicalHodgeGradedGeometricOrbitAlgebra
import GSTClassicalHodgeOmniversalSeparatorGhostCrown
import GSTClassicalHodgeUniversalTwoSlotSaturation
import GSTClassicalHodgeLimitlessSpinePropagation

/-!
# GST CLASSICAL HODGE — COSMOLOGY-TRANSFORMED CLOSURE

This file moves the remaining obstruction completely into the GST cosmology.

At each Hodge weight p, take the genuine graded-geometric program orbit inside
ambient cohomology and pull it back to the true rational (p,p) Hodge fiber.
This is the Hodge-visible part of the native projective/cut universe.

A classical Hodge failure gives an omniversal separator ghost.  That ghost
annihilates every state in the graded geometric orbit.  On the other hand the
rank-free GST theorem says that any nonzero Hodge submodule invariant under the
single universal two-slot word is the whole Hodge fiber.  Therefore, once the
program orbit is closed under the transformed universal two-slot machine and
contains one nonzero spine state, an omniversal ghost is impossible.

The only bridge exposed below is a genuinely cosmological realization law:
for each ordered pair of Hodge sheets, the universal two-slot GST word is the
Hodge restriction of some already-verified graded geometric program.  This is
strictly a program-realization statement; it contains no basis-cycle witness,
no Hodge-surjectivity clause, and no algebraicity conclusion.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeCosmologyTransformedClosure

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeGradedGeometricProgramOrbit
open GSTClassicalHodgeGradedGeometricOrbitAlgebra
open GSTClassicalHodgeOmniversalSeparatorGhostCrown
open GSTClassicalHodgeUniversalTwoSlotSaturation
open GSTClassicalHodgeRankFreePrimitiveGeneration
open GSTClassicalHodgeLimitlessSpinePropagation

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- The native graded-program universe viewed as an actual Hodge submodule. -/
noncomputable def orbitHodgeSubmodule
    (G : GeometricCycleClassSpine V H)
    (p : Nat) :
    Submodule ℚ (ClassicalHodgeFiber V H p) :=
  (geometricProgramOrbitModule G p).comap
    (rationalHodgeSubspace (H.hodgeBigrading p)).subtype

@[simp]
theorem mem_orbitHodgeSubmodule
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (alpha : ClassicalHodgeFiber V H p) :
    alpha ∈ orbitHodgeSubmodule G p ↔
      alpha.1 ∈ geometricProgramOrbitModule G p :=
  Iff.rfl

/-- The canonical normalized projective-cut spine is already inside the
cosmological orbit. -/
theorem spineHodgeSeed_mem_orbitHodgeSubmodule
    (G : GeometricCycleClassSpine V H)
    (p : Nat) :
    spineHodgeSeed G p ∈ orbitHodgeSubmodule G p := by
  exact spineHodgeSeed_mem_geometricProgramOrbitModule G p

/-- A nonzero spine state makes the transformed orbit nontrivial. -/
theorem orbitHodgeSubmodule_ne_bot_of_spine
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (hspine : spineHodgeSeed G p ≠ 0) :
    orbitHodgeSubmodule G p ≠ ⊥ := by
  intro hbot
  have hm : spineHodgeSeed G p ∈
      (⊥ : Submodule ℚ (ClassicalHodgeFiber V H p)) := by
    rw [← hbot]
    exact spineHodgeSeed_mem_orbitHodgeSubmodule G p
  exact hspine (by simpa using hm)

/-- Pure cosmology statement: the native program orbit is stable under the one
universal recoordination-local GST transfer machine. -/
def TransformedTwoSlotOrbitInvariant
    (G : GeometricCycleClassSpine V H)
    (p : Nat) : Prop :=
  UniversalTwoSlotInvariant (orbitHodgeSubmodule G p)

/-- GST irreducibility now fires directly on the transformed native orbit. -/
theorem orbitHodgeSubmodule_eq_top
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (hInv : TransformedTwoSlotOrbitInvariant G p)
    (hspine : spineHodgeSeed G p ≠ 0) :
    orbitHodgeSubmodule G p = ⊤ := by
  exact universalTwoSlotInvariant_eq_top
    (orbitHodgeSubmodule G p) hInv
    (orbitHodgeSubmodule_ne_bot_of_spine G p hspine)

/-- Once the transformed orbit is top, every true Hodge state is already the
class of an actual native cycle because the entire orbit was built from native
program execution. -/
theorem hodge_weight_of_transformed_cosmology
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (hInv : TransformedTwoSlotOrbitInvariant G p)
    (hspine : spineHodgeSeed G p ≠ 0) :
    rationalHodgeSubspace (H.hodgeBigrading p) ≤
      LinearMap.range (H.cycleClass p) := by
  have htop := orbitHodgeSubmodule_eq_top G p hInv hspine
  intro alpha halpha
  let a : ClassicalHodgeFiber V H p := ⟨alpha, halpha⟩
  have ha : a ∈ orbitHodgeSubmodule G p := by
    rw [htop]
    trivial
  exact geometricProgramOrbitModule_le_cycleClass_range G p ha

/-- Global transformed closure.  All algebraic saturation is discharged by the
GST universal-two-slot irreducibility theorem. -/
theorem bigradedBettiHodge_of_transformed_cosmology
    (G : GeometricCycleClassSpine V H)
    (hInv : ∀ p : Nat, TransformedTwoSlotOrbitInvariant G p)
    (hspine : ∀ p : Nat,
      rationalHodgeSubspace (H.hodgeBigrading p) ≠ ⊥ →
        spineHodgeSeed G p ≠ 0) :
    BigradedBettiHodgeStatement V H := by
  intro p alpha halpha
  by_cases hH : rationalHodgeSubspace (H.hodgeBigrading p) = ⊥
  · have hz : alpha = 0 := by
      have hm : alpha ∈ (⊥ : Submodule ℚ
          (RationalSingularCohomology H.analytification (2 * p))) := by
        simpa [hH] using halpha
      simpa using hm
    subst alpha
    exact ⟨0, by simp⟩
  · exact hodge_weight_of_transformed_cosmology
      G p (hInv p) (hspine p hH) halpha

/-- The exact transformation bridge: each recoordination of the universal
2-slot GST word is represented by one verified native graded program at the
same weight. -/
def UniversalTwoSlotProgramRealization
    (G : GeometricCycleClassSpine V H)
    (p : Nat) : Prop :=
  ∀ i j : ClassicalHodgeBasisIndex V H p,
    ∃ P : GradedGeometricProgram V p p,
      ∀ alpha : ClassicalHodgeFiber V H p,
        P.cohomologyEval G alpha.1 =
          (liftFiniteHodgeOperator (pairBasisIndex i j)
            (forwardArsenalWord sourceSlot targetSlot) alpha).1

/-- Program realization immediately gives transformed-orbit invariance because
the graded native orbit is already a module over every verified program. -/
theorem transformedInvariant_of_programRealization
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (R : UniversalTwoSlotProgramRealization G p) :
    TransformedTwoSlotOrbitInvariant G p := by
  intro i j alpha halpha
  rcases R i j with ⟨P, hP⟩
  have himage :
      P.cohomologyEval G alpha.1 ∈ geometricProgramOrbitModule G p :=
    program_maps_geometricProgramOrbitModule G P halpha
  rw [hP alpha] at himage
  exact himage

/-- **COSMOLOGY-TRANSFORMED CROWN.**
After the classical obstruction has been transformed into the GST graded orbit,
the existing universal two-slot theorem closes Hodge as soon as the universal
local GST word is compiled into the verified program algebra and the canonical
spine survives in every live weight. -/
theorem bigradedBettiHodge_of_program_realization
    (G : GeometricCycleClassSpine V H)
    (R : ∀ p : Nat, UniversalTwoSlotProgramRealization G p)
    (hspine : ∀ p : Nat,
      rationalHodgeSubspace (H.hodgeBigrading p) ≠ ⊥ →
        spineHodgeSeed G p ≠ 0) :
    BigradedBettiHodgeStatement V H := by
  exact bigradedBettiHodge_of_transformed_cosmology G
    (fun p => transformedInvariant_of_programRealization G p (R p))
    hspine

/-- Ghost form: under the transformed cosmology there is no omniversal
separator obstruction at all. -/
theorem no_omniversalSeparatorGhost_of_transformed_cosmology
    (G : GeometricCycleClassSpine V H)
    (hInv : ∀ p : Nat, TransformedTwoSlotOrbitInvariant G p)
    (hspine : ∀ p : Nat,
      rationalHodgeSubspace (H.hodgeBigrading p) ≠ ⊥ →
        spineHodgeSeed G p ≠ 0) :
    IsEmpty (OmniversalSeparatorGhost G) := by
  have hH := bigradedBettiHodge_of_transformed_cosmology G hInv hspine
  exact (hodge_iff_no_omniversalSeparatorGhost G).mp hH

#check orbitHodgeSubmodule
#check TransformedTwoSlotOrbitInvariant
#check UniversalTwoSlotProgramRealization
#check transformedInvariant_of_programRealization
#check bigradedBettiHodge_of_transformed_cosmology
#check bigradedBettiHodge_of_program_realization
#check no_omniversalSeparatorGhost_of_transformed_cosmology

#print axioms transformedInvariant_of_programRealization
#print axioms bigradedBettiHodge_of_transformed_cosmology
#print axioms bigradedBettiHodge_of_program_realization

end GSTClassicalHodgeCosmologyTransformedClosure
