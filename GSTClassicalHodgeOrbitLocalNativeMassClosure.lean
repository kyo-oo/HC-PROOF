import GSTClassicalHodgeOrbitLocalCosmicInternalization
import GSTClassicalHodgeLimitlessSpinePropagation

/-!
# GST CLASSICAL HODGE — ORBIT-LOCAL / NATIVE-MASS CLOSURE

The orbit-local transformed closure still displayed spine nonvanishing as a
separate family.  The limitless spine cosmology has already reduced that
family to the native-mass bridge: its conserved-charge construction proves
that every normalized projective spine seed is nonzero.

This file removes the redundant all-weight spine premise.  After the
classical obstruction has been transformed into the genuine GST orbit, the
only remaining fixed-weight transport target is orbit-local internalization of
the universal two-slot word.  Native mass supplies the nonzero seed required
by rank-free saturation automatically.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeOrbitLocalNativeMassClosure

open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeLimitlessSpinePropagation
open GSTClassicalHodgeOrbitLocalCosmicInternalization

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Native mass discharges the entire spine-survival family required by the
orbit-local transformed crown. -/
theorem bigradedBettiHodge_of_nativeMass_orbitLocalInternalization
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (R : ∀ p : Nat, OrbitLocalTwoSlotInternalization G p) :
    BigradedBettiHodgeStatement V H := by
  exact bigradedBettiHodge_of_orbitLocalInternalization G R
    (fun p _ => M.spineHodgeSeed_ne_zero G p)

/-- Concrete projective-word version.  Once native mass certifies the genuine
spine, only statewise projective realization on the already-native orbit is
needed; no separate nonvanishing family remains. -/
theorem bigradedBettiHodge_of_nativeMass_orbitLocalProjectiveWords
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (R : ∀ p : Nat, OrbitLocalProjectiveWordRealization G p) :
    BigradedBettiHodgeStatement V H := by
  exact bigradedBettiHodge_of_orbitLocalProjectiveWords G R
    (fun p _ => M.spineHodgeSeed_ne_zero G p)

/-- Ghost-free form of the same transformed collision. -/
theorem no_omniversalSeparatorGhost_of_nativeMass_orbitLocalWords
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (R : ∀ p : Nat, OrbitLocalProjectiveWordRealization G p) :
    IsEmpty (GSTClassicalHodgeOmniversalSeparatorGhostCrown.OmniversalSeparatorGhost G) := by
  exact no_omniversalSeparatorGhost_of_orbitLocalProjectiveWords G R
    (fun p _ => M.spineHodgeSeed_ne_zero G p)

#check bigradedBettiHodge_of_nativeMass_orbitLocalInternalization
#check bigradedBettiHodge_of_nativeMass_orbitLocalProjectiveWords
#check no_omniversalSeparatorGhost_of_nativeMass_orbitLocalWords

#print axioms bigradedBettiHodge_of_nativeMass_orbitLocalInternalization
#print axioms bigradedBettiHodge_of_nativeMass_orbitLocalProjectiveWords
#print axioms no_omniversalSeparatorGhost_of_nativeMass_orbitLocalWords

end GSTClassicalHodgeOrbitLocalNativeMassClosure
