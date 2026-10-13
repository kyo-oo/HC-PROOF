import HodgeConjecture

/-!
# The witness-kernel geometry upgrade

This module upgrades the public Hodge landing with the geometry of the
native witness spaces themselves.  The cycle-class map of every
codimension `p` is a `ℚ`-linear map

  `H.cycleClass p : codimensionCycles V.X p →ₗ[ℚ] RationalSingularCohomology …`,

so the native witnesses of one rational `(p,p)` class form a coset of the
cycle-class kernel: two witnesses differ by a rational equivalence class of
codimension-`p` cycles with vanishing cohomology class, and every such
translate of a witness is again a witness.

Consequences:

* the witness space of a rational `(p,p)` class is either empty or an
  affine translate of `LinearMap.ker (H.cycleClass p)`;
* when the cycle-class map is injective in codimension `p` (trivial
  kernel, i.e. rational-equivalence injectivity), every rational `(p,p)`
  class has a *unique* native witness;
* both strengthened public landing routes (the full limitless crown and
  the geometry-first brute-force route) compose with this coset geometry;
* the flagship statement combines the geometry-first route with injectivity
  in every codimension: unique native witnesses for every rational `(p,p)`
  class, in every degree, in one theorem.

No input surface is weakened; every statement is proved from the existing
root API by linearity of the cycle-class map.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G

namespace HodgeConjecture

/-! ## The witness-kernel geometry of native cycle witnesses -/

/-- Any two native codimension-`p` witnesses of one rational `(p,p)` class
differ by an element of the kernel of the cycle-class map: a rational
equivalence class of codimension-`p` cycles whose cohomology class
vanishes. -/
theorem cycle_witness_diff_mem_kernel
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (Z₁ Z₂ : codimensionCycles V.X p)
    (h₁ : H.cycleClass p Z₁ = alpha)
    (h₂ : H.cycleClass p Z₂ = alpha) :
    Z₁ - Z₂ ∈ LinearMap.ker (H.cycleClass p) := by
  rw [LinearMap.mem_ker, map_sub, h₁, h₂, sub_self]

/-- The native witness space of a rational `(p,p)` class, when nonempty, is
exactly a translate of the cycle-class kernel: anchored at any witness `Z₀`,
the witnesses are precisely the elements `Z₀ + k` with `k` in the kernel. -/
theorem cycle_witness_coset_of_anchor
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (Z₀ : codimensionCycles V.X p)
    (h₀ : H.cycleClass p Z₀ = alpha) :
    ∀ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha ↔
        ∃ k ∈ LinearMap.ker (H.cycleClass p), Z = Z₀ + k := by
  intro Z
  constructor
  · intro hZ
    exact
      ⟨Z - Z₀,
        cycle_witness_diff_mem_kernel V H p alpha Z Z₀ hZ h₀,
        by abel⟩
  · rintro ⟨k, hk, hkZ⟩
    rw [hkZ, map_add, h₀, LinearMap.mem_ker.1 hk, add_zero]

/-- Under the exact classical Hodge target, every rational `(p,p)` class
acquires a native witness space that is a full coset of the cycle-class
kernel. -/
theorem cycle_witness_space_coset
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha :
      complexificationMapQ
          (RationalSingularCohomology H.analytification (2 * p)) alpha
        ∈ (H.hodgeBigrading p).ppComponent)
    (hT : ClassicalHodgeTarget V H) :
    ∃ Z₀ : codimensionCycles V.X p,
      ∀ Z : codimensionCycles V.X p,
        H.cycleClass p Z = alpha ↔
          ∃ k ∈ LinearMap.ker (H.cycleClass p), Z = Z₀ + k := by
  obtain ⟨Z₀, hZ₀⟩ :=
    (classicalHodgeTarget_iff_explicit_witness V H).mp hT p alpha halpha
  exact ⟨Z₀, cycle_witness_coset_of_anchor V H p alpha Z₀ hZ₀⟩

/-- Injectivity of the codimension-`p` cycle-class map (trivial kernel:
rational-equivalence injectivity) upgrades every rational `(p,p)` class to a
*unique* native codimension-`p` witness. -/
theorem unique_native_cycle_witness_of_injective
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (halpha :
      complexificationMapQ
          (RationalSingularCohomology H.analytification (2 * p)) alpha
        ∈ (H.hodgeBigrading p).ppComponent)
    (hT : ClassicalHodgeTarget V H)
    (hker : LinearMap.ker (H.cycleClass p) = ⊥) :
    ∃! Z : codimensionCycles V.X p, H.cycleClass p Z = alpha := by
  obtain ⟨Z, hZ⟩ :=
    (classicalHodgeTarget_iff_explicit_witness V H).mp hT p alpha halpha
  refine ⟨Z, hZ, fun Z' hZ' => ?_⟩
  have hd : Z' - Z ∈ LinearMap.ker (H.cycleClass p) :=
    cycle_witness_diff_mem_kernel V H p alpha Z' Z hZ' hZ
  rw [hker] at hd
  have h0 : Z' - Z = 0 := Submodule.mem_bot.1 hd
  exact sub_eq_zero.mp h0

/-! ## Grand landing composites through the strengthened routes -/

/-- The full limitless geometric route lands directly in the kernel-coset
geometry: every rational `(p,p)` class acquires a native witness space that
is a translate of the cycle-class kernel. -/
theorem every_hodge_class_has_kernel_coset_witness_of_full_limitless_geometry
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (G :
      GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (hNV :
      GSTClassicalHodgeFullLimitlessCrown.SpineTowerNonvanishing G)
    (R :
      GSTClassicalHodgeFullLimitlessCrown.FullProjectiveCosmicExternalization G) :
    ∀ p : Nat,
    ∀ alpha : RationalSingularCohomology H.analytification (2 * p),
      complexificationMapQ
          (RationalSingularCohomology H.analytification (2 * p)) alpha
        ∈ (H.hodgeBigrading p).ppComponent →
      ∃ Z₀ : codimensionCycles V.X p,
        ∀ Z : codimensionCycles V.X p,
          H.cycleClass p Z = alpha ↔
            ∃ k ∈ LinearMap.ker (H.cycleClass p), Z = Z₀ + k := by
  intro p alpha halpha
  exact cycle_witness_space_coset V H p alpha halpha
    (classicalHodgeTarget_of_full_limitless_geometry G hNV R)

/-- The strengthened geometry-first brute-force route (one conserved
native/cohomological tower charge + two genuine projective primitive actions
per ordered Hodge pair) lands in the same kernel-coset geometry. -/
theorem every_hodge_class_has_kernel_coset_witness_of_conserved_spine_and_projective_two_generators
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (G :
      GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (D :
      GSTClassicalHodgeLimitlessSpinePropagation.SpineTowerConservedCharge G)
    (R : ∀ q : Nat,
      ∀ i j : GSTClassicalHodgeFiberedCosmology.ClassicalHodgeBasisIndex V H q,
        GSTClassicalHodgeProjectiveTwoGeneratorExternalization.ProjectiveTwoGenerator
          (V := V) (H := H) i j) :
    ∀ p : Nat,
    ∀ alpha : RationalSingularCohomology H.analytification (2 * p),
      complexificationMapQ
          (RationalSingularCohomology H.analytification (2 * p)) alpha
        ∈ (H.hodgeBigrading p).ppComponent →
      ∃ Z₀ : codimensionCycles V.X p,
        ∀ Z : codimensionCycles V.X p,
          H.cycleClass p Z = alpha ↔
            ∃ k ∈ LinearMap.ker (H.cycleClass p), Z = Z₀ + k := by
  intro p alpha halpha
  exact cycle_witness_space_coset V H p alpha halpha
    (classicalHodgeTarget_of_conserved_spine_and_projective_two_generators G D R)

/-- **THE FLAGSHIP.**  The strengthened geometry-first route, combined with
rational-equivalence injectivity of the cycle-class map in every
codimension, produces a *unique* native codimension-`p` witness for every
rational `(p,p)` class, in every degree, in one statement. -/
theorem every_hodge_class_has_unique_native_witness_of_injective_and_conserved_spine
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (G :
      GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (D :
      GSTClassicalHodgeLimitlessSpinePropagation.SpineTowerConservedCharge G)
    (R : ∀ q : Nat,
      ∀ i j : GSTClassicalHodgeFiberedCosmology.ClassicalHodgeBasisIndex V H q,
        GSTClassicalHodgeProjectiveTwoGeneratorExternalization.ProjectiveTwoGenerator
          (V := V) (H := H) i j)
    (hkers :
      ∀ p : Nat, LinearMap.ker (H.cycleClass p) = ⊥) :
    ∀ p : Nat,
    ∀ alpha : RationalSingularCohomology H.analytification (2 * p),
      complexificationMapQ
          (RationalSingularCohomology H.analytification (2 * p)) alpha
        ∈ (H.hodgeBigrading p).ppComponent →
      ∃! Z : codimensionCycles V.X p, H.cycleClass p Z = alpha := by
  intro p alpha halpha
  exact unique_native_cycle_witness_of_injective V H p alpha halpha
    (classicalHodgeTarget_of_conserved_spine_and_projective_two_generators G D R)
    (hkers p)

/-! ## The range-inclusion and atomic-span restatements of the target -/

/-- The exact classical Hodge target, restated per codimension: the rational
`(p,p)` Hodge subspace is contained in the range of the native cycle-class
map. -/
theorem classicalHodgeTarget_iff_range_le
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) :
    ClassicalHodgeTarget V H ↔
      ∀ p : Nat,
        rationalHodgeSubspace (H.hodgeBigrading p) ≤
          LinearMap.range (H.cycleClass p) := by
  constructor
  · intro hT p alpha halpha
    exact
      (classicalHodgeTarget_iff_explicit_witness V H).mp hT p alpha
        ((mem_rationalHodgeSubspace_iff (H.hodgeBigrading p) alpha).1 halpha)
  · intro hle p alpha halpha
    rcases hle p alpha
      ((mem_rationalHodgeSubspace_iff (H.hodgeBigrading p) alpha).2 halpha)
      with ⟨Z, hZ⟩
    exact ⟨Z, hZ⟩

/-- The atomic-span restatement: the target holds iff, in every codimension,
the rational `(p,p)` Hodge subspace is contained in the span of genuine
codimension-`p` point-cycle classes. -/
theorem classicalHodgeTarget_iff_atomic_span_le
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) :
    ClassicalHodgeTarget V H ↔
      ∀ p : Nat,
        rationalHodgeSubspace (H.hodgeBigrading p) ≤
          GSTClassicalHodgeAtomicSpan.pointCycleClassSpan p (H.cycleClass p) := by
  rw [classicalHodgeTarget_iff_range_le V H]
  constructor
  · intro hle p
    have hr := hle p
    rw
      [GSTClassicalHodgeAtomicSpan.smoothProjective_cycleClass_range_eq_atomic_span
        V H p] at hr
    exact hr
  · intro hsp p
    rw
      [GSTClassicalHodgeAtomicSpan.smoothProjective_cycleClass_range_eq_atomic_span
        V H p]
    exact hsp p

/-- The full limitless geometric route lands in the atomic-span form: in
every codimension, the rational `(p,p)` Hodge subspace is contained in the
span of genuine codimension-`p` point-cycle classes. -/
theorem atomic_span_le_of_full_limitless_geometry
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (G :
      GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (hNV :
      GSTClassicalHodgeFullLimitlessCrown.SpineTowerNonvanishing G)
    (R :
      GSTClassicalHodgeFullLimitlessCrown.FullProjectiveCosmicExternalization G) :
    ∀ p : Nat,
        rationalHodgeSubspace (H.hodgeBigrading p) ≤
          GSTClassicalHodgeAtomicSpan.pointCycleClassSpan p (H.cycleClass p) := by
  intro p
  exact (classicalHodgeTarget_iff_atomic_span_le V H).mp
    (classicalHodgeTarget_of_full_limitless_geometry G hNV R) p

/-- The strengthened geometry-first brute-force route lands in the same
atomic-span form. -/
theorem atomic_span_le_of_conserved_spine_and_projective_two_generators
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (G :
      GSTClassicalHodgeGeometricCycleClassSpine.GeometricCycleClassSpine V H)
    (D :
      GSTClassicalHodgeLimitlessSpinePropagation.SpineTowerConservedCharge G)
    (R : ∀ q : Nat,
      ∀ i j : GSTClassicalHodgeFiberedCosmology.ClassicalHodgeBasisIndex V H q,
        GSTClassicalHodgeProjectiveTwoGeneratorExternalization.ProjectiveTwoGenerator
          (V := V) (H := H) i j) :
    ∀ p : Nat,
        rationalHodgeSubspace (H.hodgeBigrading p) ≤
          GSTClassicalHodgeAtomicSpan.pointCycleClassSpan p (H.cycleClass p) := by
  intro p
  exact (classicalHodgeTarget_iff_atomic_span_le V H).mp
    (classicalHodgeTarget_of_conserved_spine_and_projective_two_generators G D R) p

end HodgeConjecture

end
