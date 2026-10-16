import GSTGeometricRealizationStage2G

/-!
# GST exact descent to an ARBITRARY TARGET VARIETY X

Target:
For every smooth projective complex X, p, and rational (p,p)
Hodge alpha, produce a genuine rational algebraic cycle Z on X.

This module constructs Z on X, not just a primitive on X x X.
It uses an independently geometric Chow correspondence from a source Y,
where the needed Hodge class has actually been represented.

For Y=X x X, a cohomological section is
  alpha |-> pr1^*(alpha) cup pr2^*(h^d)/deg(h^d)
and projection pr1_* is a left inverse.
Native proper pushforward and Betti Gysin must commute with cycleClass.
The source Hodge representatives need independent geometric proofs.
The known universal alternating product primitive alone does not supply them.

No arbitrary target-cycle selector is assumed, and no universal
Hodge theorem is claimed without the concrete geometric source theorem.
-/

set_option maxHeartbeats 5000000
noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G

namespace GSTUniversalChowRetractToTarget

/-- Actual native Chow and rational Betti correspondence for a
source Y and a target X. Every field is geometric input, and
NONE asserts a target Hodge class is algebraic. -/
structure NativeHodgeRetract
    (Y X : SmoothProjectiveComplexScheme)
    (D : HodgeBigradedBettiData Y)
    (H : HodgeBigradedBettiData X)
    (q p : Nat) where
  native :
    codimensionCycles Y.X q →ₗ[ℚ] codimensionCycles X.X p
  betti :
    RationalSingularCohomology D.analytification (2 * q) →ₗ[ℚ]
      RationalSingularCohomology H.analytification (2 * p)
  hodgeSection :
    RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
      RationalSingularCohomology D.analytification (2 * q)
  section_is_hodge :
    ∀ alpha : RationalSingularCohomology H.analytification (2 * p),
      alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p) →
        hodgeSection alpha ∈ rationalHodgeSubspace (D.hodgeBigrading q)
  betti_retract :
    ∀ alpha : RationalSingularCohomology H.analytification (2 * p),
      betti (hodgeSection alpha) = alpha
  cycleClass_natural :
    ∀ Z : codimensionCycles Y.X q,
      H.cycleClass p (native Z) = betti (D.cycleClass q Z)

variable {Y X : SmoothProjectiveComplexScheme}
variable {D : HodgeBigradedBettiData Y}
variable {H : HodgeBigradedBettiData X}
variable {q p : Nat}

/-- Given a SOURCE native cycle for the cohomological section,
construct the actual TARGET rational algebraic cycle, through the
geometrically natural native correspondence. -/
theorem construct_target_cycle_from_source_hodge_lift
    (R : NativeHodgeRetract Y X D H q p)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (hsource :
      ∃ Z : codimensionCycles Y.X q,
        D.cycleClass q Z = R.hodgeSection alpha) :
    ∃ Z : codimensionCycles X.X p,
      H.cycleClass p Z = alpha := by
  obtain ⟨Z, hZ⟩ := hsource
  refine ⟨R.native Z, ?_⟩
  calc
    H.cycleClass p (R.native Z) =
        R.betti (D.cycleClass q Z) := R.cycleClass_natural Z
    _ = R.betti (R.hodgeSection alpha) := by rw [hZ]
    _ = alpha := R.betti_retract alpha

/-- Full Hodge on X is DERIVED if X is a true Chow motivic
retract of a source Y with previously established Hodge
algebraicity. There is no target algebraicity assumption. -/
theorem every_target_hodge_class_from_solved_source
    (R : NativeHodgeRetract Y X D H q p)
    (hY : ∀ beta : RationalSingularCohomology D.analytification (2 * q),
      beta ∈ rationalHodgeSubspace (D.hodgeBigrading q) →
        ∃ Z : codimensionCycles Y.X q,
          D.cycleClass q Z = beta) :
    ∀ alpha : RationalSingularCohomology H.analytification (2 * p),
      alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p) →
        ∃ Z : codimensionCycles X.X p,
          H.cycleClass p Z = alpha := by
  intro alpha hAlpha
  exact construct_target_cycle_from_source_hodge_lift R alpha
    (hY (R.hodgeSection alpha) (R.section_is_hodge alpha hAlpha))

/-- Direct compatibility with the original omniversal GST ghost
separator: the actual target Hodge fiber lies in the native-cycle
range when the geometric retract source has been solved. -/
theorem target_hodge_subset_native_cycleClass_range
    (R : NativeHodgeRetract Y X D H q p)
    (hY : ∀ beta : RationalSingularCohomology D.analytification (2 * q),
      beta ∈ rationalHodgeSubspace (D.hodgeBigrading q) →
        ∃ Z : codimensionCycles Y.X q,
          D.cycleClass q Z = beta) :
    rationalHodgeSubspace (H.hodgeBigrading p) ≤
      LinearMap.range (H.cycleClass p) := by
  intro alpha hAlpha
  obtain ⟨Z, hZ⟩ :=
    every_target_hodge_class_from_solved_source R hY alpha hAlpha
  exact ⟨Z, hZ⟩

/-- Necessary source limitation:
the genuine target of an algebraic source cycle is again algebraic.
It cannot equal a hypothetical target class absent from the native
cycle-class range. A correspondence alone does not manufacture
unrepresented Hodge classes. -/
theorem no_unrepresented_target_from_algebraic_source
    (R : NativeHodgeRetract Y X D H q p)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (hmissing : alpha ∉ LinearMap.range (H.cycleClass p))
    (Z : codimensionCycles Y.X q) :
    R.betti (D.cycleClass q Z) ≠ alpha := by
  intro heq
  apply hmissing
  refine ⟨R.native Z, ?_⟩
  rw [R.cycleClass_natural]
  exact heq


/-! ## Scheme-typed, arbitrary-codimension GST geometric world birth

This upgrades the former abstract GST world-birth calculus into the actual
native codimension-cycle types of Mathlib smooth projective complex schemes.

For a chosen codimension p on a genuine target scheme, each finite source
index carries its OWN genuine smooth projective source scheme and codimension
q_i. The native assembly maps LAND IN codimensionCycles target.X p and the
Betti assembly maps LAND IN genuine rational singular cohomology of that target.
The required geometric Hodge expansion is a statement about the target's
actual Hodge bigrading, NOT an arbitrary vector-space presentation.

Projective bundles and blowups instantiate these fields through hyperplane/
exceptional-divisor intersection and Gysin operations. Their concrete scheme
constructions must be provided separately: do not mistake a packet containing
their comparison laws for an unconditional construction of all such maps.
-/

open scoped BigOperators

/-- Finite geometric birth with genuinely different source SCHEMES and
codimensions, and direct compatibility with the original cycleClass maps.
In particular the target cycle map is not chosen to make surjectivity true. -/
structure GeometricMultiSourceChowBirth
    (X : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData X)
    (p : ℕ)
    (ι : Type*) [Fintype ι] where
  source : ι → SmoothProjectiveComplexScheme
  data : (i : ι) → HodgeBigradedBettiData (source i)
  codim : ι → ℕ
  native : (i : ι) →
    codimensionCycles (source i).X (codim i) →ₗ[ℚ]
      codimensionCycles X.X p
  betti : (i : ι) →
    RationalSingularCohomology (data i).analytification (2 * codim i) →ₗ[ℚ]
      RationalSingularCohomology H.analytification (2 * p)
  naturality : ∀ i (Z : codimensionCycles (source i).X (codim i)),
    H.cycleClass p (native i Z) =
      betti i ((data i).cycleClass (codim i) Z)
  hodgeSpan : ∀ alpha : RationalSingularCohomology
      H.analytification (2 * p),
    alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p) →
      ∃ beta : (i : ι) →
        RationalSingularCohomology (data i).analytification (2 * codim i),
        (∀ i, beta i ∈ rationalHodgeSubspace
          ((data i).hodgeBigrading (codim i))) ∧
        (∑ i : ι, betti i (beta i)) = alpha

variable {ι : Type*} [Fintype ι]

/-- An EXPLICIT rational algebraic cycle on the actual target scheme:
assemble the native source cycles using the genuine Chow maps and
certify that its rational Betti class is precisely the target class. -/
theorem actual_target_cycle_of_geometric_multi_source_birth
    (P : GeometricMultiSourceChowBirth X H p ι)
    (hSource : ∀ i : ι,
      BigradedBettiHodgeStatement (P.source i) (P.data i))
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (hAlpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p)) :
    ∃ Z : codimensionCycles X.X p, H.cycleClass p Z = alpha := by
  classical
  obtain ⟨beta, hHodge, hReconstruct⟩ := P.hodgeSpan alpha hAlpha
  have hWitness : ∀ i : ι,
      ∃ Z : codimensionCycles (P.source i).X (P.codim i),
        (P.data i).cycleClass (P.codim i) Z = beta i := by
    intro i
    exact hSource i (P.codim i) (hHodge i)
  let native : (i : ι) → codimensionCycles (P.source i).X (P.codim i) :=
    fun i => Classical.choose (hWitness i)
  refine ⟨∑ i : ι, P.native i (native i), ?_⟩
  calc
    H.cycleClass p (∑ i : ι, P.native i (native i)) =
        ∑ i : ι, H.cycleClass p (P.native i (native i)) := by
          rw [map_sum]
    _ = ∑ i : ι,
        P.betti i ((P.data i).cycleClass (P.codim i) (native i)) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact P.naturality i (native i)
    _ = ∑ i : ι, P.betti i (beta i) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Classical.choose_spec (hWitness i)]
    _ = alpha := hReconstruct

/-- Scheme-typed (p,p) rational-Hodge surjectivity under a genuinely
geometric projective-bundle/blowup source splitting, with no fixed rank
or dimension assumption. This is directly a theorem about the ORIGINAL
target cycleClass map, not an abstract GST surrogate. -/
theorem actual_hodge_range_of_geometric_multi_source_birth
    (P : GeometricMultiSourceChowBirth X H p ι)
    (hSource : ∀ i : ι,
      BigradedBettiHodgeStatement (P.source i) (P.data i)) :
    rationalHodgeSubspace (H.hodgeBigrading p) ≤
      LinearMap.range (H.cycleClass p) := by
  intro alpha hAlpha
  obtain ⟨Z, hZ⟩ :=
    actual_target_cycle_of_geometric_multi_source_birth
      P hSource alpha hAlpha
  exact ⟨Z, hZ⟩


/-! ## Full coordinate-readout interface for genuine bundle and blowup formulas

The previous multivariate birth required a Hodge spanning equation.
A TRUE geometric blowup or projective bundle instead supplies explicit
cohomological extraction/readout operators (pullback, exceptional
Gysin inverse and fiber integration) and an exact reconstruction.

This law assembles a scheme-typed birth from those READOUT operations
and their Hodge preservation, deriving the Hodge spanning equation.
The underlying geometric Gysin and bundle maps are separate
scheme-level instances to be proved; the Lean record does not
silently instantiate them for an arbitrary X.
-/

/-- A certified actual Chow/Gysin splitting with explicit independent
cohomological readout from target to ALL source schemes.
Unlike a freely chosen Hodge class-to-cycle map, each readout stays in
COHOMOLOGY and its rational Hodge type is verified. -/
structure GeometricSplitGysinPacket
    (X : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData X)
    (p : ℕ) (ι : Type*) [Fintype ι] where
  source : ι → SmoothProjectiveComplexScheme
  data : (i : ι) → HodgeBigradedBettiData (source i)
  codim : ι → ℕ
  native : (i : ι) →
    codimensionCycles (source i).X (codim i) →ₗ[ℚ]
      codimensionCycles X.X p
  betti : (i : ι) →
    RationalSingularCohomology (data i).analytification (2 * codim i) →ₗ[ℚ]
      RationalSingularCohomology H.analytification (2 * p)
  readout : (i : ι) →
    RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
      RationalSingularCohomology (data i).analytification (2 * codim i)
  naturality : ∀ i (Z : codimensionCycles (source i).X (codim i)),
    H.cycleClass p (native i Z) =
      betti i ((data i).cycleClass (codim i) Z)
  readout_hodge : ∀ i
      (alpha : RationalSingularCohomology H.analytification (2 * p)),
    alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p) →
      readout i alpha ∈
        rationalHodgeSubspace ((data i).hodgeBigrading (codim i))
  reconstruct : ∀ alpha : RationalSingularCohomology
      H.analytification (2 * p),
    (∑ i : ι, betti i (readout i alpha)) = alpha

/-- Convert the actual projective-bundle / exceptional-Gysin
readout data into the previously verified SCHEME-TYPED birth law.
Importantly the Hodge decomposition is now DEDUCED from actual
cohomology readouts and the reconstruction identity. -/
noncomputable def GeometricSplitGysinPacket.toChowBirth
    (P : GeometricSplitGysinPacket X H p ι) :
    GeometricMultiSourceChowBirth X H p ι where
  source := P.source
  data := P.data
  codim := P.codim
  native := P.native
  betti := P.betti
  naturality := P.naturality
  hodgeSpan := by
    intro alpha hAlpha
    refine ⟨fun i => P.readout i alpha, ?_, P.reconstruct alpha⟩
    intro i
    exact P.readout_hodge i alpha hAlpha

/-- Actual codimension-p Hodge surjectivity on a TARGET SCHEME,
deduced from fully specified Chow/Gysin readouts and actual
source-scheme Hodge surjectivity; no target-cycle witness field. -/
theorem actual_chow_cycle_of_geometric_gysin_split
    (P : GeometricSplitGysinPacket X H p ι)
    (hSource : ∀ i : ι,
      BigradedBettiHodgeStatement (P.source i) (P.data i))
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (hAlpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p)) :
    ∃ Z : codimensionCycles X.X p,
      H.cycleClass p Z = alpha := by
  exact actual_target_cycle_of_geometric_multi_source_birth
    P.toChowBirth hSource alpha hAlpha

/-- One weight of the genuine Hodge conjecture on X, extracted from
a verified geometrical decomposition of the same Betti and Chow
sources, for any finite number of exceptional/projective-bundle terms. -/
theorem actual_hodge_of_geometric_gysin_split
    (P : GeometricSplitGysinPacket X H p ι)
    (hSource : ∀ i : ι,
      BigradedBettiHodgeStatement (P.source i) (P.data i)) :
    rationalHodgeSubspace (H.hodgeBigrading p) ≤
      LinearMap.range (H.cycleClass p) :=
  actual_hodge_range_of_geometric_multi_source_birth
    P.toChowBirth hSource

#check GeometricSplitGysinPacket
#check GeometricSplitGysinPacket.toChowBirth
#check actual_chow_cycle_of_geometric_gysin_split
#check actual_hodge_of_geometric_gysin_split
#print axioms actual_hodge_of_geometric_gysin_split

#check GeometricMultiSourceChowBirth
#check actual_target_cycle_of_geometric_multi_source_birth
#check actual_hodge_range_of_geometric_multi_source_birth
#print axioms actual_target_cycle_of_geometric_multi_source_birth
#print axioms actual_hodge_range_of_geometric_multi_source_birth

#check construct_target_cycle_from_source_hodge_lift
#check every_target_hodge_class_from_solved_source
#check target_hodge_subset_native_cycleClass_range
#check no_unrepresented_target_from_algebraic_source
#print axioms every_target_hodge_class_from_solved_source
#print axioms no_unrepresented_target_from_algebraic_source

end GSTUniversalChowRetractToTarget
