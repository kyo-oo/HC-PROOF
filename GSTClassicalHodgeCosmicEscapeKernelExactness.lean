import GSTClassicalHodgeSuccessorSeedEscapeDichotomy
import GSTClassicalHodgeLimitlessSpinePropagation

/-!
# GST CLASSICAL HODGE — COSMIC ESCAPE / KERNEL EXACTNESS

The successor-seed dichotomy isolates a `PositiveCosmicHomologyEscape`: an
actual algebraic cycle with nonzero native mass and nonzero limitless shadow
whose genuine Betti cycle class vanishes.

The limitless spine, independently, asks for the kernel law

  cycleClass Z = 0 -> nativeCycleMass Z = 0.

These are not two unrelated assumptions.  Because nonzero native mass already
forces a nonzero cosmic shadow, they are exact logical complements at each
weight.  This file records that equivalence and then feeds the *local* kernel
law directly into the separator-successor dichotomy.

The gain is architectural: seed production at weight `p+1` needs only kernel
exactness at that same weight, not a global no-escape package over all weights.
No Hodge-surjectivity, basis-cycle representative, or correspondence
realization is introduced.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeCosmicEscapeKernelExactness

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2G
open GSTClassicalHodgePrincipalCutSuccessorOperator
open GSTClassicalHodgeNativeCycleCosmicShadow
open GSTClassicalHodgeSingleExactSuccessorSurvival
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeSynchronizedDefectOrbit
open GSTClassicalHodgeSuccessorSeedEscapeDichotomy
open GSTClassicalHodgeLimitlessSpinePropagation

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- The bare kernel defect behind a positive cosmic homology escape: one
class-zero native cycle whose canonical native mass is nevertheless nonzero. -/
structure NativeMassKernelEscape (q : Nat) where
  cycle : codimensionCycles V.X q
  class_zero : H.cycleClass q cycle = 0
  mass_ne_zero : nativeCycleMass V q cycle ≠ 0

/-- Nonzero mass automatically upgrades the bare kernel defect to the full
positive-cosmic escape used by the successor dichotomy. -/
noncomputable def NativeMassKernelEscape.toPositiveCosmicHomologyEscape
    {q : Nat}
    (E : NativeMassKernelEscape (V := V) (H := H) q) :
    PositiveCosmicHomologyEscape (V := V) (H := H) q where
  cycle := E.cycle
  mass_ne_zero := E.mass_ne_zero
  shadow_ne_zero :=
    nativeCycleCosmicShadow_self_ne_zero_of_mass
      (V := V) q E.cycle E.mass_ne_zero
  class_zero := E.class_zero

/-- Forgetting the redundant shadow witness recovers the bare mass-kernel
escape. -/
def NativeMassKernelEscape.ofPositiveCosmicHomologyEscape
    {q : Nat}
    (E : PositiveCosmicHomologyEscape (V := V) (H := H) q) :
    NativeMassKernelEscape (V := V) (H := H) q where
  cycle := E.cycle
  class_zero := E.class_zero
  mass_ne_zero := E.mass_ne_zero

/-- Positive cosmic homology escape is exactly the existence of a nonzero-mass
cycle in the genuine Betti cycle-class kernel. -/
theorem nonempty_nativeMassKernelEscape_iff_positiveCosmicHomologyEscape
    (q : Nat) :
    Nonempty (NativeMassKernelEscape (V := V) (H := H) q) ↔
      Nonempty (PositiveCosmicHomologyEscape (V := V) (H := H) q) := by
  constructor
  · rintro ⟨E⟩
    exact ⟨E.toPositiveCosmicHomologyEscape⟩
  · rintro ⟨E⟩
    exact ⟨NativeMassKernelEscape.ofPositiveCosmicHomologyEscape E⟩

/-- Weight-local kernel exactness for the canonical native mass. -/
def NativeMassKernelExactAt (q : Nat) : Prop :=
  ∀ Z : codimensionCycles V.X q,
    H.cycleClass q Z = 0 → nativeCycleMass V q Z = 0

/-- **EXACT ESCAPE/KERNEL DUALITY.**
At a fixed weight, native mass annihilates the genuine cycle-class kernel if
and only if positive cosmic homology escape is impossible. -/
theorem nativeMassKernelExactAt_iff_noPositiveCosmicHomologyEscape
    (q : Nat) :
    NativeMassKernelExactAt (V := V) (H := H) q ↔
      ¬ Nonempty (PositiveCosmicHomologyEscape (V := V) (H := H) q) := by
  constructor
  · intro hExact hEscape
    let E := Classical.choice hEscape
    exact E.mass_ne_zero (hExact E.cycle E.class_zero)
  · intro hNoEscape Z hclass
    by_contra hmass
    apply hNoEscape
    exact ⟨{
      cycle := Z
      mass_ne_zero := hmass
      shadow_ne_zero :=
        nativeCycleCosmicShadow_self_ne_zero_of_mass
          (V := V) q Z hmass
      class_zero := hclass
    }⟩

/-- The kernel field of the existing native-mass bridge is precisely the
weight-local exactness predicate above. -/
theorem NativeMassCycleClassBridge.kernelExactAt
    (M : NativeMassCycleClassBridge V H)
    (q : Nat) :
    NativeMassKernelExactAt (V := V) (H := H) q :=
  M.kernel_mass_zero q

/-- Hence a native-mass bridge excludes the positive cosmic escape at every
weight, with no additional shadow argument required downstream. -/
theorem NativeMassCycleClassBridge.noPositiveCosmicHomologyEscape
    (M : NativeMassCycleClassBridge V H)
    (q : Nat) :
    ¬ Nonempty (PositiveCosmicHomologyEscape (V := V) (H := H) q) :=
  (nativeMassKernelExactAt_iff_noPositiveCosmicHomologyEscape
    (V := V) (H := H) q).1 (M.kernelExactAt q)

/-- **LOCAL SUCCESSOR SEED CLOSURE.**
For one exact separator successor at weight `p+1`, only kernel exactness at
that same target weight is needed to eliminate the escape branch and obtain a
genuine nonzero algebraic Hodge orbit seed. -/
theorem separator_successor_seed_of_kernelExactAt
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hlive : ProjectivelyLiveSource V.projective.n
      (V.projective.immersion x.1))
    (hExactCodim :
      Order.coheight
        (ambientSuccessorPoint V x.1
          (relativeHeightOneSeparatorSuccessor V x.1 hlive)) = p + 1)
    (hKernel : NativeMassKernelExactAt (V := V) (H := H) (p + 1)) :
    Nonempty (NativeHodgeOrbitSeed (V := V) (H := H) (p := p + 1)) := by
  rcases separator_successor_seed_or_escape
      G p x hlive hExactCodim with hseed | hescape
  · exact hseed
  · let E := Classical.choice hescape
    exact False.elim (E.mass_ne_zero (hKernel E.cycle E.class_zero))

/-- Existing native-mass bridge data therefore close the separator seed locally
without first packaging a global all-weight no-escape hypothesis. -/
theorem separator_successor_seed_of_nativeMassBridge
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hlive : ProjectivelyLiveSource V.projective.n
      (V.projective.immersion x.1))
    (hExactCodim :
      Order.coheight
        (ambientSuccessorPoint V x.1
          (relativeHeightOneSeparatorSuccessor V x.1 hlive)) = p + 1) :
    Nonempty (NativeHodgeOrbitSeed (V := V) (H := H) (p := p + 1)) :=
  separator_successor_seed_of_kernelExactAt
    G p x hlive hExactCodim (M.kernelExactAt (p + 1))

#check NativeMassKernelEscape
#check NativeMassKernelEscape.toPositiveCosmicHomologyEscape
#check NativeMassKernelEscape.ofPositiveCosmicHomologyEscape
#check nonempty_nativeMassKernelEscape_iff_positiveCosmicHomologyEscape
#check NativeMassKernelExactAt
#check nativeMassKernelExactAt_iff_noPositiveCosmicHomologyEscape
#check NativeMassCycleClassBridge.kernelExactAt
#check NativeMassCycleClassBridge.noPositiveCosmicHomologyEscape
#check separator_successor_seed_of_kernelExactAt
#check separator_successor_seed_of_nativeMassBridge

#print axioms nonempty_nativeMassKernelEscape_iff_positiveCosmicHomologyEscape
#print axioms nativeMassKernelExactAt_iff_noPositiveCosmicHomologyEscape
#print axioms NativeMassCycleClassBridge.noPositiveCosmicHomologyEscape
#print axioms separator_successor_seed_of_kernelExactAt
#print axioms separator_successor_seed_of_nativeMassBridge

end GSTClassicalHodgeCosmicEscapeKernelExactness
