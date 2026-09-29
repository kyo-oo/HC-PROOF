import GSTClassicalHodgeFirstFailureScalarDetectorCollision

/-!
# GST CLASSICAL HODGE — FIRST-FAILURE DETECTOR-TRANSVERSE RETURN

The first-failure scalar collision still carried one apparently geometric
number `lambda` and an exact scalar equality.  Neither is independent data.

For one nonzero target defect

    z = atomicDefect(beta),

the Hamel-polarization layer has already constructed a detector `ell_z` with
`ell_z z != 0`.  Hence a genuine cross-weight return only has to make the
principal-cut round trip *visible* to that same detector:

    ell_z (Lbar (Rbar z)) != 0.

Once this single transversality statement is known, define

    lambda := ell_z (Lbar (Rbar z)) / ell_z z.

Both numerator and denominator are nonzero, so `lambda != 0`, and the scalar
round-trip identity follows by field arithmetic.  Thus the scalar-reciprocity
frontier collapses to one incidence statement between an actual geometric
return and one canonically selected quotient detector.

This is deliberately weaker than a quotient retraction, a scaled coisometry,
a perfect-pairing adjoint law, or a matrix-unit realization.  The return is a
genuine `GradedCycleClassOperatorPair`, and only its action on the one failed
defect is constrained.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeFirstFailureDetectorTransverseReturn

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeAtomicDefectDuality
open GSTClassicalHodgeCrossWeightNativePropagation
open GSTClassicalHodgeCrossWeightAtomicDefectDescent
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeFirstPrimitiveProjectiveFailure
open GSTClassicalHodgeFirstFailureScalarDetectorCollision

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- One genuine return whose quotient round trip is detected nontrivially by
exactly the Hamel detector canonically selected from the failed defect. -/
structure FirstFailureDetectorTransverseReturn
    (G : GeometricCycleClassSpine V H)
    (p : Nat)
    (beta : GSTClassicalHodgeFiberedCosmology.ClassicalHodgeFiber V H (p + 1))
    (hbeta : atomicDefectLinearMap V H (p + 1) beta ≠ 0) where
  returnPair : GradedCycleClassOperatorPair V H (p + 1) p
  return_hodge :
    returnPair.cohomologyOperator beta.1 ∈
      rationalHodgeSubspace (H.hodgeBigrading p)
  detector_transverse :
    let z := atomicDefectLinearMap V H (p + 1) beta
    chosenDefectDetector z hbeta
      (principalCutDefectOperator G p
        (returnPair.defectOperator z)) ≠ 0

namespace FirstFailureDetectorTransverseReturn

/-- Nonzero numerator read supplied by the actual return geometry. -/
noncomputable def roundtripRead
    {G : GeometricCycleClassSpine V H}
    {beta : GSTClassicalHodgeFiberedCosmology.ClassicalHodgeFiber V H (p + 1)}
    {hbeta : atomicDefectLinearMap V H (p + 1) beta ≠ 0}
    (R : FirstFailureDetectorTransverseReturn G p beta hbeta) : ℚ :=
  let z := atomicDefectLinearMap V H (p + 1) beta
  chosenDefectDetector z hbeta
    (principalCutDefectOperator G p
      (R.returnPair.defectOperator z))

/-- The denominator is the detector's nonzero read on the failed defect. -/
noncomputable def defectRead
    {G : GeometricCycleClassSpine V H}
    {beta : GSTClassicalHodgeFiberedCosmology.ClassicalHodgeFiber V H (p + 1)}
    {hbeta : atomicDefectLinearMap V H (p + 1) beta ≠ 0}
    (_R : FirstFailureDetectorTransverseReturn G p beta hbeta) : ℚ :=
  let z := atomicDefectLinearMap V H (p + 1) beta
  chosenDefectDetector z hbeta z

/-- The reciprocity scalar is not geometric input: it is reconstructed from
the two nonzero detector reads. -/
noncomputable def inducedScalar
    {G : GeometricCycleClassSpine V H}
    {beta : GSTClassicalHodgeFiberedCosmology.ClassicalHodgeFiber V H (p + 1)}
    {hbeta : atomicDefectLinearMap V H (p + 1) beta ≠ 0}
    (R : FirstFailureDetectorTransverseReturn G p beta hbeta) : ℚ :=
  R.roundtripRead / R.defectRead

/-- The numerator read is nonzero by transversality. -/
theorem roundtripRead_ne_zero
    {G : GeometricCycleClassSpine V H}
    {beta : GSTClassicalHodgeFiberedCosmology.ClassicalHodgeFiber V H (p + 1)}
    {hbeta : atomicDefectLinearMap V H (p + 1) beta ≠ 0}
    (R : FirstFailureDetectorTransverseReturn G p beta hbeta) :
    R.roundtripRead ≠ 0 := by
  simpa [roundtripRead] using R.detector_transverse

/-- The denominator read is nonzero by construction of the Hamel detector. -/
theorem defectRead_ne_zero
    {G : GeometricCycleClassSpine V H}
    {beta : GSTClassicalHodgeFiberedCosmology.ClassicalHodgeFiber V H (p + 1)}
    {hbeta : atomicDefectLinearMap V H (p + 1) beta ≠ 0}
    (R : FirstFailureDetectorTransverseReturn G p beta hbeta) :
    R.defectRead ≠ 0 := by
  simpa [defectRead] using
    chosenDefectDetector_ne_zero_on
      (atomicDefectLinearMap V H (p + 1) beta) hbeta

/-- Therefore the reconstructed scalar is nonzero. -/
theorem inducedScalar_ne_zero
    {G : GeometricCycleClassSpine V H}
    {beta : GSTClassicalHodgeFiberedCosmology.ClassicalHodgeFiber V H (p + 1)}
    {hbeta : atomicDefectLinearMap V H (p + 1) beta ≠ 0}
    (R : FirstFailureDetectorTransverseReturn G p beta hbeta) :
    R.inducedScalar ≠ 0 := by
  exact div_ne_zero R.roundtripRead_ne_zero R.defectRead_ne_zero

/-- The exact scalar reciprocity identity is now a theorem of transversality,
not an independently supplied law. -/
theorem inducedScalar_roundtrip
    {G : GeometricCycleClassSpine V H}
    {beta : GSTClassicalHodgeFiberedCosmology.ClassicalHodgeFiber V H (p + 1)}
    {hbeta : atomicDefectLinearMap V H (p + 1) beta ≠ 0}
    (R : FirstFailureDetectorTransverseReturn G p beta hbeta) :
    let z := atomicDefectLinearMap V H (p + 1) beta
    chosenDefectDetector z hbeta
        (principalCutDefectOperator G p
          (R.returnPair.defectOperator z)) =
      R.inducedScalar * chosenDefectDetector z hbeta z := by
  dsimp only
  change R.roundtripRead = R.inducedScalar * R.defectRead
  rw [inducedScalar]
  field_simp [R.defectRead_ne_zero]

/-- Convert one detector-transverse return into the scalar-return packet used
by the first-failure collision theorem. -/
noncomputable def toScalarReturn
    {G : GeometricCycleClassSpine V H}
    {beta : GSTClassicalHodgeFiberedCosmology.ClassicalHodgeFiber V H (p + 1)}
    {hbeta : atomicDefectLinearMap V H (p + 1) beta ≠ 0}
    (R : FirstFailureDetectorTransverseReturn G p beta hbeta) :
    FirstFailureScalarReturn G p beta hbeta where
  returnPair := R.returnPair
  return_hodge := R.return_hodge
  scalar := R.inducedScalar
  scalar_ne_zero := R.inducedScalar_ne_zero
  scalar_roundtrip := R.inducedScalar_roundtrip

/-- At a globally least bad successor weight even the weaker one-detector
transverse return is impossible. -/
theorem firstFailure_forbids_detectorTransverseReturn
    {G : GeometricCycleClassSpine V H}
    (F : FirstAtomicDefectWeight V H)
    (hp : F.weight = p + 1)
    {beta : GSTClassicalHodgeFiberedCosmology.ClassicalHodgeFiber V H (p + 1)}
    {hbeta : atomicDefectLinearMap V H (p + 1) beta ≠ 0}
    (R : FirstFailureDetectorTransverseReturn G p beta hbeta) : False :=
  R.toScalarReturn.firstFailure_forbids_scalar_return F hp

end FirstFailureDetectorTransverseReturn

/-- **DETECTOR-TRANSVERSE RETURN HODGE CROWN.**
Weight-zero algebraicity plus one genuine detector-transverse cross-weight
return for every possible nonzero successor defect excludes the least failure
and proves the complete Stage-2G Hodge statement. -/
theorem bigradedBettiHodge_of_detectorTransverseReturnFamily
    (G : GeometricCycleClassSpine V H)
    (hzero : atomicDefectLinearMap V H 0 = 0)
    (R : ∀ p : Nat,
      ∀ beta : GSTClassicalHodgeFiberedCosmology.ClassicalHodgeFiber V H (p + 1),
      ∀ hbeta : atomicDefectLinearMap V H (p + 1) beta ≠ 0,
        Nonempty (FirstFailureDetectorTransverseReturn G p beta hbeta)) :
    BigradedBettiHodgeStatement V H := by
  apply bigradedBettiHodge_of_scalarReturnFamily G hzero
  intro q beta hbeta
  rcases R q beta hbeta with ⟨RR⟩
  exact ⟨RR.toScalarReturn⟩

#check FirstFailureDetectorTransverseReturn
#check FirstFailureDetectorTransverseReturn.roundtripRead
#check FirstFailureDetectorTransverseReturn.defectRead
#check FirstFailureDetectorTransverseReturn.inducedScalar
#check FirstFailureDetectorTransverseReturn.inducedScalar_ne_zero
#check FirstFailureDetectorTransverseReturn.inducedScalar_roundtrip
#check FirstFailureDetectorTransverseReturn.toScalarReturn
#check FirstFailureDetectorTransverseReturn.firstFailure_forbids_detectorTransverseReturn
#check bigradedBettiHodge_of_detectorTransverseReturnFamily

#print axioms FirstFailureDetectorTransverseReturn.inducedScalar_roundtrip
#print axioms FirstFailureDetectorTransverseReturn.toScalarReturn
#print axioms FirstFailureDetectorTransverseReturn.firstFailure_forbids_detectorTransverseReturn
#print axioms bigradedBettiHodge_of_detectorTransverseReturnFamily

end GSTClassicalHodgeFirstFailureDetectorTransverseReturn
