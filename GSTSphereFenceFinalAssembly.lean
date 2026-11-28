import Mathlib
import GSTSphereFenceOmegaDischarge
import HamSandwich.H2SphereQ

/-
Copyright (c) 2026. The HC-PROOF campaign. All rights reserved.

# THE FENCE FINAL ASSEMBLY — the port composed with the corpus (wave 13)

THE LAST SUBCASE OF THE X-AUDIT, CLOSED IN ONE COMPOSITION:

* the wave-13 port (the vendored HamSandwich machine, ℚ-instantiated)
  certifies `SphereOddDegree.nontrivial_sphereHomology_two` — the
  degree-2 rational singular homology of the honest sphere
  `unitSphereType = ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)`
  is NONTRIVIAL (the suspension tower: subdivision → small chains →
  Mayer-Vietoris → H₂(S²;ℚ) ≅ ℚ);
* the wave-13 composition (`GSTSphereFenceOmegaDischarge`) turns that
  nontriviality into FENCE-Ω (`∃ ω : singularCohomologyOf
  (TopCat.of unitSphereType) 2, ω ≠ 0`) — the non-bounding cycle
  extraction, the pinned extension lemma, the wave-12 realization
  replay — and instantiates the exists-flip master;
* THIS MODULE applies one to the other: the FULL eight-conjunct wave-9
  apex package holds UNCONDITIONALLY — both source families linearly
  independent at every `M ≥ 1` with the weight-one conjunct UNGUARDED,
  every weight-0/1 rational Hodge class an explicit combination, every
  weight-`p ≥ 2` rational Hodge class zero, both compilers correct, and
  the single-fold orbit law itself at the honest data.

The wave-9 apex package's last guarded conjunct is thereby discharged at
the constructed domain — the fence chain of waves 9-13 complete.

HONESTY LEDGER. This statement is kernel-certified exactly when BOTH
inputs are: the port lane (`ham-sandwich-port.yml`, ladders 1-6) and the
fence lane's ladders for the composition. No `sorry`, no new axioms, no
`native_decide`.
-/

set_option maxHeartbeats 70000000
set_option maxRecDepth 20000

noncomputable section

open CategoryTheory
open AlgebraicTopology
open Simplicial
open GSTSphereUnionComponents
open GSTSingularCohomologyMaps
open GSTSphereNonzeroClass
open GSTSphereFundamentalCycle
open GSTSphereFenceRealization
open GSTSphereFenceOmegaDischarge
open GSTFiniteLineFenceDischarge

namespace GSTSphereFenceFinalAssembly

/-- **THE WAVE-9 APEX PACKAGE, UNCONDITIONAL.**  The composition of the
wave-13 port's homology nontriviality with the fence-Ω discharge: the
complete eight-conjunct master at the certified witness. -/
theorem the_unconditional_source_package_unconditional :
    ∃ ω : singularCohomologyOf (TopCat.of unitSphereType) 2,
      (∀ (M : ℕ) (hM : NeZero M),
        LinearIndependent ℚ (fun i : Fin M =>
          (finiteLineHodgeDataHonest M (finiteLineAnalytificationUnconditional M)
            (finiteLineAnalytificationUnconditional_space M) ω).cycleClass 1
            (finiteLineSourceOne M i))) ∧
      (∀ (M : ℕ) (hM : NeZero M),
        LinearIndependent ℚ (fun i : Fin M =>
          (finiteLineHodgeDataHonest M (finiteLineAnalytificationUnconditional M)
            (finiteLineAnalytificationUnconditional_space M) ω).cycleClass 0
            (finiteLineSourceZero M i))) ∧
      (∀ (M : ℕ) (hM : NeZero M),
        ∀ α : RationalSingularCohomology
            (finiteLineAnalytificationUnconditional M) 0,
          α ∈ rationalHodgeSubspace
            ((finiteLineHodgeDataHonest M (finiteLineAnalytificationUnconditional M)
              (finiteLineAnalytificationUnconditional_space M) ω).hodgeBigrading 0) →
          ∃ q : Fin M → ℚ,
            α = ∑ i, q i • (finiteLineHodgeDataHonest M
              (finiteLineAnalytificationUnconditional M)
              (finiteLineAnalytificationUnconditional_space M) ω).cycleClass 0
              (finiteLineSourceZero M i)) ∧
      (∀ (M : ℕ) (hM : NeZero M),
        ∀ α : RationalSingularCohomology
            (finiteLineAnalytificationUnconditional M) 2,
          α ∈ rationalHodgeSubspace
            ((finiteLineHodgeDataHonest M (finiteLineAnalytificationUnconditional M)
              (finiteLineAnalytificationUnconditional_space M) ω).hodgeBigrading 1) →
          ∃ q : Fin M → ℚ,
            α = ∑ i, q i • (finiteLineHodgeDataHonest M
              (finiteLineAnalytificationUnconditional M)
              (finiteLineAnalytificationUnconditional_space M) ω).cycleClass 1
              (finiteLineSourceOne M i)) ∧
      (∀ (M : ℕ) (hM : NeZero M),
        ∀ p : ℕ, 1 < p →
        ∀ α : RationalSingularCohomology
            (finiteLineAnalytificationUnconditional M) (2 * p),
          α ∈ rationalHodgeSubspace
            ((finiteLineHodgeDataHonest M (finiteLineAnalytificationUnconditional M)
              (finiteLineAnalytificationUnconditional_space M) ω).hodgeBigrading p) →
          α = 0) ∧
      (∀ (M : ℕ) (hM : NeZero M),
        ∀ α : RationalSingularCohomology
            (finiteLineAnalytificationUnconditional M) 0,
        (finiteLineHodgeDataHonest M (finiteLineAnalytificationUnconditional M)
          (finiteLineAnalytificationUnconditional_space M) ω).cycleClass 0
          (finiteLineSourceCompilerZero M
            (finiteLineAnalytificationUnconditional M)
            (finiteLineAnalytificationUnconditional_space M) α) = α) ∧
      (∀ (M : ℕ) (hM : NeZero M),
        ∀ α : RationalSingularCohomology
            (finiteLineAnalytificationUnconditional M) 2,
        ∀ hmem : α ∈ rationalHodgeSubspace
            ((finiteLineHodgeDataHonest M (finiteLineAnalytificationUnconditional M)
              (finiteLineAnalytificationUnconditional_space M) ω).hodgeBigrading 1),
        (finiteLineHodgeDataHonest M (finiteLineAnalytificationUnconditional M)
          (finiteLineAnalytificationUnconditional_space M) ω).cycleClass 1
          (finiteLineSourceCompilerOne M
            (finiteLineAnalytificationUnconditional M)
            (finiteLineAnalytificationUnconditional_space M) ω α hmem) = α) ∧
      (∀ (M : ℕ) (hM : NeZero M),
        NativeGSTSingleFoldOrbitLaw (finiteLineWorld M)
          (finiteLineHodgeDataHonest M (finiteLineAnalytificationUnconditional M)
            (finiteLineAnalytificationUnconditional_space M) ω)) :=
  the_unconditional_source_package_of_nontrivial_homology
    SphereOddDegree.nontrivial_sphereHomology_two

/-! ## Receipts -/

#check @GSTSphereFenceFinalAssembly.the_unconditional_source_package_unconditional

#print axioms GSTSphereFenceFinalAssembly.the_unconditional_source_package_unconditional

end GSTSphereFenceFinalAssembly

end -- noncomputable section

/-
PORT NOTES (the designated CI repair points of this file):

* (FA-1) The composition is ONE application — the port's
  `nontrivial_sphereHamologyHomology`-shaped endpoint
  (`SphereOddDegree.nontrivial_sphereHomology_two`, HamSandwich/H2SphereQ.lean)
  into the composition's hypothesis (GSTSphereFenceOmegaDischarge).  The
  only seam is the TYPE IDENTIFICATION: both sides spell the homology
  object as `((singularChainComplexFunctor (ModuleCat ℚ)).obj
  (ModuleCat.of ℚ ℚ)).obj (TopCat.of unitSphereType) |>.homology 2` —
  the port's `singularChainsOf_unitSphereType_eq` receipt (the `rfl`
  identification, H2SphereQ.lean's PORT NOTES) closes any residual
  spelling gap; if `exact` stalls on the Nontrivial-type coercion
  (`↥(ModuleCat …)` vs the object's sort), restage with the
  `Nontrivial`-of-coe unfolded.
* (FA-2) This file is green ONLY when both inputs are: the port lane's
  six ladders AND the fence lane's composition ladders. The two-status
  law: nothing here is a claim of the corpus until its own lane runs
  green at the pushed SHA.
-/
