import GSTClassicalHodgeTomographicGhostObstruction
import GSTClassicalHodgeOrbitLocalNativeMassClosure

/-!
# GST CLASSICAL HODGE — TOMOGRAPHIC / ORBIT-LOCAL COLLISION

This module fuses the transformed tomographic obstruction with the strongest
native-mass / orbit-local GST saturation theorem already available in the
cosmology.

The point is fixed-weight and deliberately sharper than the global crown.
A hypothetical classical Hodge failure first becomes a `TomographicDarkGhost`.
At that ghost's own weight:

* native mass proves the canonical normalized projective spine is nonzero;
* orbit-local internalization makes the genuine graded-program Hodge orbit
  invariant under every recoordination of the universal two-slot GST word;
* rank-free GST irreducibility forces that genuine native orbit to be the whole
  Hodge fiber;
* consequently the very basis state detected by the ghost belongs to the
  genuine cycle-class range;
* but the ghost separator annihilates that range while detecting that state.

Hence the transformed ghost cannot survive.  No global whole-fiber operator
identity and no basis-cycle representative is inserted.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeTomographicOrbitLocalCollision

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeAtomicAnnihilator
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeGradedGeometricProgramOrbit
open GSTClassicalHodgeCosmologyTransformedClosure
open GSTClassicalHodgeOrbitLocalCosmicInternalization
open GSTClassicalHodgeLimitlessSpinePropagation
open GSTClassicalHodgeTomographicGhostObstruction

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- **FIXED-WEIGHT GST COLLISION.**

After transforming a Hodge failure into a tomographic dark ghost, native mass
plus orbit-local two-slot internalization at *that one ghost weight* already
forces a contradiction.

The contradiction is semantic, not merely operator-theoretic: saturation puts
the ghost-detected Hodge basis vector in the genuine cycle-class range, while
the stored separator annihilates that entire range and is nonzero on exactly
that basis vector. -/
theorem tomographicDarkGhost_false_of_nativeMass_orbitLocal
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (T : TomographicDarkGhost G)
    (R : OrbitLocalTwoSlotInternalization G T.ghost.weight) :
    False := by
  have htop :
      orbitHodgeSubmodule G T.ghost.weight = ⊤ :=
    orbitHodgeSubmodule_eq_top_of_orbitLocalInternalization
      G T.ghost.weight R
      (M.spineHodgeSeed_ne_zero G T.ghost.weight)
  let beta : ClassicalHodgeFiber V H T.ghost.weight :=
    classicalHodgeBasis V H T.ghost.weight T.ghost.sheet
  have hbetaOrbit : beta ∈ orbitHodgeSubmodule G T.ghost.weight := by
    rw [htop]
    trivial
  have hbetaRange :
      beta.1 ∈ LinearMap.range (H.cycleClass T.ghost.weight) :=
    geometricProgramOrbitModule_le_cycleClass_range
      G T.ghost.weight hbetaOrbit
  have hbetaSpan :
      beta.1 ∈ pointCycleClassSpan T.ghost.weight
        (H.cycleClass T.ghost.weight) := by
    rw [← smoothProjective_cycleClass_range_eq_atomic_span
      V H T.ghost.weight]
    exact hbetaRange
  have hker :
      pointCycleClassSpan T.ghost.weight
          (H.cycleClass T.ghost.weight) ≤
        LinearMap.ker T.ghost.separator.detector :=
    (annihilatesPointCycles_iff_atomicSpan_le_ker
      T.ghost.weight
      (H.cycleClass T.ghost.weight)
      T.ghost.separator.detector).mp
        T.ghost.separator.annihilates_atoms
  have hzero : T.ghost.separator.detector beta.1 = 0 :=
    hker hbetaSpan
  exact T.ghost.separator.detects_basis hzero

/-- The transformation lets us weaken the global internalization demand:
it is enough to supply orbit-local GST internalization only at the weight of
each hypothetical tomographic ghost.  If no ghost exists the premise is
vacuous; if one exists, the fixed-weight collision above destroys it. -/
theorem bigradedBettiHodge_of_nativeMass_ghostWeightInternalization
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (R : ∀ T : TomographicDarkGhost G,
      OrbitLocalTwoSlotInternalization G T.ghost.weight) :
    BigradedBettiHodgeStatement V H := by
  rw [hodge_iff_no_tomographicDarkGhost G]
  refine ⟨?_⟩
  intro T
  exact tomographicDarkGhost_false_of_nativeMass_orbitLocal G M T (R T)

/-- Concrete projective-word form of the ghost-weight-only closure.  It is
strictly localized to weights where a transformed obstruction would actually
exist. -/
theorem bigradedBettiHodge_of_nativeMass_ghostWeightProjectiveWords
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (R : ∀ T : TomographicDarkGhost G,
      OrbitLocalProjectiveWordRealization G T.ghost.weight) :
    BigradedBettiHodgeStatement V H := by
  apply bigradedBettiHodge_of_nativeMass_ghostWeightInternalization G M
  intro T
  exact orbitLocalInternalization_of_projectiveWords
    G T.ghost.weight (R T)

/-- Equivalent ghost-free receipt in the transformed cosmology. -/
theorem no_tomographicDarkGhost_of_nativeMass_ghostWeightInternalization
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (R : ∀ T : TomographicDarkGhost G,
      OrbitLocalTwoSlotInternalization G T.ghost.weight) :
    IsEmpty (TomographicDarkGhost G) := by
  exact (hodge_iff_no_tomographicDarkGhost G).mp
    (bigradedBettiHodge_of_nativeMass_ghostWeightInternalization G M R)

#check tomographicDarkGhost_false_of_nativeMass_orbitLocal
#check bigradedBettiHodge_of_nativeMass_ghostWeightInternalization
#check bigradedBettiHodge_of_nativeMass_ghostWeightProjectiveWords
#check no_tomographicDarkGhost_of_nativeMass_ghostWeightInternalization

#print axioms tomographicDarkGhost_false_of_nativeMass_orbitLocal
#print axioms bigradedBettiHodge_of_nativeMass_ghostWeightInternalization
#print axioms bigradedBettiHodge_of_nativeMass_ghostWeightProjectiveWords

end GSTClassicalHodgeTomographicOrbitLocalCollision
