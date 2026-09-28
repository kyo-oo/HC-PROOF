import GSTClassicalHodgeNativeCycleCosmicShadow
import GSTClassicalHodgeProjectiveSeparatorUnconditionalHeightOne

/-!
# GST CLASSICAL HODGE — INTRINSIC PROJECTIVE-SUCCESSOR NORMALIZATION

The limitless cosmic Lefschetz coefficient and the native projective-cut mass
encode different information and should not be identified by an extra law.
For a one-weight cosmic jump the former is the universal path multiplicity
`choose 2 1 = 2`; the latter is the actual rational mass of the finite
exact-stratum successor presentation of the projective source point.

The correct bridge is intrinsic normalization.  Whenever the genuine
projective successor has nonzero mass, divide the actual native successor by
that mass.  The resulting native cycle has mass exactly one, hence its
limitless cosmic shadow is *definitionally the canonical next-weight basis
state*.  No assertion that the geometric successor count equals a universal
combinatorial coefficient is needed.

This removes the artificial `successorMass = successorScalar` requirement from
pointwise native/cosmic comparison.  The remaining geometric obligation is the
honest one: prove that the exact projective successor mass is nonzero whenever
the next codimension is geometrically live.
-/

set_option maxHeartbeats 50000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeIntrinsicSuccessorNormalization

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgePrincipalCutSuccessorOperator
open GSTClassicalHodgeNativeCycleCosmicShadow
open GSTClassicalHodgeLimitlessCosmicMatrixUnits
open GSTClassicalHodgeLimitlessTowerOrbitCrown

/-- The universal one-weight limitless Lefschetz coefficient is always two. -/
theorem successorScalar_eq_two (p : Nat) :
    successorScalar p = 2 := by
  unfold successorScalar GSTClassicalHodgeCrossWeightNativePropagation.limitlessLefschetzScalar
  norm_num

/-- Normalize one genuine point successor by its *actual* projective mass. -/
noncomputable def intrinsicNormalizedSuccessor
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p) :
    codimensionCycles V.X (p + 1) :=
  (successorMass V p x)⁻¹ •
    successorNativeOperator V p (codimensionPointCycle V.X p x)

/-- If the actual successor mass is nonzero, intrinsic normalization gives
native mass exactly one. -/
theorem nativeCycleMass_intrinsicNormalizedSuccessor
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hmass : successorMass V p x ≠ 0) :
    nativeCycleMass V (p + 1)
        (intrinsicNormalizedSuccessor V p x) = 1 := by
  unfold intrinsicNormalizedSuccessor
  rw [LinearMap.map_smul]
  rw [nativeCycleMass_successor_point]
  field_simp

/-- **INTRINSIC NATIVE/LIMITLESS BRIDGE.**
A nonzero geometry-built successor, normalized by its own mass, has exactly the
canonical limitless next-weight Hodge shadow. -/
theorem intrinsicNormalizedSuccessor_cosmicShadow
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hmass : successorMass V p x ≠ 0) :
    nativeCycleCosmicShadow V (p + 1)
        (intrinsicNormalizedSuccessor V p x) =
      rationalCosmicBasis (p + 1) := by
  rw [nativeCycleCosmicShadow_eq_mass_smul]
  rw [nativeCycleMass_intrinsicNormalizedSuccessor V p x hmass]
  simp

/-- The intrinsic normalization is itself nonzero whenever successor mass is
nonzero.  This is a native-cycle statement and does not appeal to cycle-class
surjectivity. -/
theorem intrinsicNormalizedSuccessor_ne_zero
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hmass : successorMass V p x ≠ 0) :
    intrinsicNormalizedSuccessor V p x ≠ 0 := by
  intro hz
  have hmassone := nativeCycleMass_intrinsicNormalizedSuccessor V p x hmass
  rw [hz, LinearMap.map_zero] at hmassone
  norm_num at hmassone

/-- The original scalar-matching law is strictly stronger than what is needed
for canonical cosmic alignment: it forces the actual projective successor mass
to equal two. -/
theorem old_successorScalar_law_forces_mass_two
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hold : successorMass V p x = successorScalar p) :
    successorMass V p x = 2 := by
  rw [hold, successorScalar_eq_two]

/-- Crown: intrinsic projective normalization needs only nonzero actual mass
and gives simultaneously unit native mass, nonzero native cycle, and the exact
canonical limitless next-weight state. -/
theorem intrinsic_successor_normalization_crown
    (V : SmoothProjectiveComplexScheme)
    (p : Nat)
    (x : CodimensionPoint V.X p)
    (hmass : successorMass V p x ≠ 0) :
    nativeCycleMass V (p + 1)
        (intrinsicNormalizedSuccessor V p x) = 1
      ∧ intrinsicNormalizedSuccessor V p x ≠ 0
      ∧ nativeCycleCosmicShadow V (p + 1)
          (intrinsicNormalizedSuccessor V p x) =
            rationalCosmicBasis (p + 1) := by
  exact ⟨nativeCycleMass_intrinsicNormalizedSuccessor V p x hmass,
    intrinsicNormalizedSuccessor_ne_zero V p x hmass,
    intrinsicNormalizedSuccessor_cosmicShadow V p x hmass⟩

#check successorScalar_eq_two
#check intrinsicNormalizedSuccessor
#check nativeCycleMass_intrinsicNormalizedSuccessor
#check intrinsicNormalizedSuccessor_cosmicShadow
#check intrinsicNormalizedSuccessor_ne_zero
#check old_successorScalar_law_forces_mass_two
#check intrinsic_successor_normalization_crown

#print axioms successorScalar_eq_two
#print axioms nativeCycleMass_intrinsicNormalizedSuccessor
#print axioms intrinsicNormalizedSuccessor_cosmicShadow
#print axioms intrinsicNormalizedSuccessor_ne_zero
#print axioms intrinsic_successor_normalization_crown

end GSTClassicalHodgeIntrinsicSuccessorNormalization
