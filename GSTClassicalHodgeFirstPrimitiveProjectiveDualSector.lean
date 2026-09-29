import GSTClassicalHodgeFirstPrimitiveProjectiveSector
import GSTClassicalHodgeAtomicAnnihilator

/-!
# GST CLASSICAL HODGE — FIRST PRIMITIVE PROJECTIVE DUAL SECTOR

The earlier projective moment profile used the ghost detector on a chosen Hodge
representative.  Because that detector annihilates the complete atomic span,
it actually descends canonically to the atomic-defect quotient itself.

At the least bad weight, the realized defect sector equals the primitive defect
image and is invariant under every genuine projective word.  Restricting the
descended detector therefore produces a nonzero covector on the *entire*
canonical first primitive projective sector.

This removes representative choices from the residual object.  A first Hodge
failure now supplies, entirely inside the quotient:

* a nonzero canonical primitive defect submodule;
* an action of every genuine projective word on that submodule;
* a nonzero rational covector on the submodule;
* the induced contragredient projective action on covectors.

No matrix-unit realization or projective irreducibility is assumed.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeFirstPrimitiveProjectiveDualSector

open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeAtomicDefectDuality
open GSTClassicalHodgeAtomicAnnihilator
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgePrimitiveAtomicDefectReduction
open GSTClassicalHodgeTraceZeroPrimitiveTomographyGhost
open GSTClassicalHodgePrimitiveProjectiveDefectModule
open GSTClassicalHodgeHodgeFunctorialProjectiveDynamics
open GSTClassicalHodgeHodgeDefectImageFunctoriality
open GSTClassicalHodgeFirstPrimitiveProjectiveFailure
open GSTClassicalHodgeFirstFailurePrimitiveImage
open GSTClassicalHodgeFirstPrimitiveProjectiveSector

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- The primitive ghost separator descends canonically through the complete
atomic span to a functional on the atomic-defect quotient. -/
noncomputable def primitiveGhostDefectFunctional
    {G : GeometricCycleClassSpine V H}
    {D : LefschetzPrimitiveDecomposition G}
    {T : GSTClassicalHodgeProjectiveDegreeTrace.ProjectiveDegreeTraceSemantics V H}
    {A : GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor G T p}
    (E : TraceZeroPrimitiveTomographyGhost A D) :
    AtomicDefectSpace V H p →ₗ[ℚ] ℚ := by
  have hker :
      pointCycleClassSpan p (H.cycleClass p) ≤ LinearMap.ker E.source.detector :=
    (annihilatesPointCycles_iff_atomicSpan_le_ker
      p (H.cycleClass p) E.source.detector).mp
      E.source.annihilates_atoms
  exact Submodule.liftQ
    (pointCycleClassSpan p (H.cycleClass p)) E.source.detector hker

/-- Representative formula for the quotient-native ghost functional. -/
@[simp]
theorem primitiveGhostDefectFunctional_mk
    {G : GeometricCycleClassSpine V H}
    {D : LefschetzPrimitiveDecomposition G}
    {T : GSTClassicalHodgeProjectiveDegreeTrace.ProjectiveDegreeTraceSemantics V H}
    {A : GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor G T p}
    (E : TraceZeroPrimitiveTomographyGhost A D)
    (alpha : RationalSingularCohomology H.analytification (2 * p)) :
    primitiveGhostDefectFunctional E (Submodule.Quotient.mk alpha) =
      E.source.detector alpha := by
  rfl

/-- The quotient-native functional detects the distinguished nonzero ghost
defect state. -/
theorem primitiveGhostDefectFunctional_detects
    {G : GeometricCycleClassSpine V H}
    {D : LefschetzPrimitiveDecomposition G}
    {T : GSTClassicalHodgeProjectiveDegreeTrace.ProjectiveDegreeTraceSemantics V H}
    {A : GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor G T p}
    (E : TraceZeroPrimitiveTomographyGhost A D) :
    primitiveGhostDefectFunctional E E.defectState ≠ 0 := by
  change primitiveGhostDefectFunctional E
      (Submodule.Quotient.mk E.traceZeroClass.1) ≠ 0
  rw [primitiveGhostDefectFunctional_mk]
  exact E.separator_detects

/-- Hence the quotient-native ghost functional itself is nonzero. -/
theorem primitiveGhostDefectFunctional_ne_zero
    {G : GeometricCycleClassSpine V H}
    {D : LefschetzPrimitiveDecomposition G}
    {T : GSTClassicalHodgeProjectiveDegreeTrace.ProjectiveDegreeTraceSemantics V H}
    {A : GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor G T p}
    (E : TraceZeroPrimitiveTomographyGhost A D) :
    primitiveGhostDefectFunctional E ≠ 0 := by
  intro hzero
  apply primitiveGhostDefectFunctional_detects E
  rw [hzero]
  rfl

/-- Restriction of the quotient-native ghost detector to the canonical first
primitive residual sector. -/
noncomputable def firstPrimitiveSectorFunctional
    {R : HodgeFunctorialGeometricSemantics V H}
    {T : GSTClassicalHodgeProjectiveDegreeTrace.ProjectiveDegreeTraceSemantics V H}
    (F : FirstAtomicDefectWeight V H)
    {p : Nat}
    (hp : F.weight = p + 1)
    (D : LefschetzPrimitiveDecomposition R.spine)
    (A : GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor
      R.spine T (p + 1))
    (E : TraceZeroPrimitiveTomographyGhost A D) :
    PrimitiveDefectImage D (p + 1) →ₗ[ℚ] ℚ :=
  (primitiveGhostDefectFunctional E).comp
    (PrimitiveDefectImage D (p + 1)).subtype

/-- The sector functional is nonzero because the distinguished ghost state is
itself inside the first primitive residual sector. -/
theorem firstPrimitiveSectorFunctional_ne_zero
    {R : HodgeFunctorialGeometricSemantics V H}
    {T : GSTClassicalHodgeProjectiveDegreeTrace.ProjectiveDegreeTraceSemantics V H}
    (F : FirstAtomicDefectWeight V H)
    {p : Nat}
    (hp : F.weight = p + 1)
    (D : LefschetzPrimitiveDecomposition R.spine)
    (A : GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor
      R.spine T (p + 1))
    (E : TraceZeroPrimitiveTomographyGhost A D) :
    firstPrimitiveSectorFunctional F hp D A E ≠ 0 := by
  let z : PrimitiveDefectImage D (p + 1) :=
    ⟨E.defectState,
      firstFailure_ghost_defectState_mem_PrimitiveDefectImage F hp D A E⟩
  intro hzero
  have hz : firstPrimitiveSectorFunctional F hp D A E z = 0 := by
    rw [hzero]
    rfl
  exact primitiveGhostDefectFunctional_detects E hz

/-- Contragredient action of a genuine projective word on covectors of the
canonical first primitive sector. -/
noncomputable def firstPrimitiveSectorDualAction
    {R : HodgeFunctorialGeometricSemantics V H}
    (F : FirstAtomicDefectWeight V H)
    {p : Nat}
    (hp : F.weight = p + 1)
    (D : LefschetzPrimitiveDecomposition R.spine)
    (w : HodgeFunctorialGeometricSemantics.ProjectiveHodgeWord R (p + 1))
    (ell : PrimitiveDefectImage D (p + 1) →ₗ[ℚ] ℚ) :
    PrimitiveDefectImage D (p + 1) →ₗ[ℚ] ℚ :=
  ell.comp (firstPrimitiveProjectiveOperator F hp D w)

/-- The quotient-level projective matrix coefficient of a sector state and a
sector covector. -/
noncomputable def firstPrimitiveSectorMatrixCoefficient
    {R : HodgeFunctorialGeometricSemantics V H}
    (F : FirstAtomicDefectWeight V H)
    {p : Nat}
    (hp : F.weight = p + 1)
    (D : LefschetzPrimitiveDecomposition R.spine)
    (w : HodgeFunctorialGeometricSemantics.ProjectiveHodgeWord R (p + 1))
    (ell : PrimitiveDefectImage D (p + 1) →ₗ[ℚ] ℚ)
    (z : PrimitiveDefectImage D (p + 1)) : ℚ :=
  ell (firstPrimitiveProjectiveOperator F hp D w z)

/-- The ghost gives a nonzero identity matrix coefficient entirely in the
canonical quotient sector. -/
theorem firstPrimitiveSector_identity_coefficient_ne_zero
    {R : HodgeFunctorialGeometricSemantics V H}
    {T : GSTClassicalHodgeProjectiveDegreeTrace.ProjectiveDegreeTraceSemantics V H}
    (F : FirstAtomicDefectWeight V H)
    {p : Nat}
    (hp : F.weight = p + 1)
    (D : LefschetzPrimitiveDecomposition R.spine)
    (A : GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor
      R.spine T (p + 1))
    (E : TraceZeroPrimitiveTomographyGhost A D) :
    let z : PrimitiveDefectImage D (p + 1) :=
      ⟨E.defectState,
        firstFailure_ghost_defectState_mem_PrimitiveDefectImage F hp D A E⟩
    firstPrimitiveSectorMatrixCoefficient F hp D
      (HodgeFunctorialGeometricSemantics.ProjectiveHodgeWord.id)
      (firstPrimitiveSectorFunctional F hp D A E) z ≠ 0 := by
  dsimp [firstPrimitiveSectorMatrixCoefficient,
    firstPrimitiveSectorFunctional,
    firstPrimitiveProjectiveOperator]
  exact primitiveGhostDefectFunctional_detects E

/-- Complete quotient-native dual residual packet. -/
structure FirstPrimitiveProjectiveDualSectorPacket
    (R : HodgeFunctorialGeometricSemantics V H)
    (T : GSTClassicalHodgeProjectiveDegreeTrace.ProjectiveDegreeTraceSemantics V H)
    (F : FirstAtomicDefectWeight V H)
    (p : Nat)
    (hp : F.weight = p + 1)
    (D : LefschetzPrimitiveDecomposition R.spine)
    (A : GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor
      R.spine T (p + 1)) where
  ghost : TraceZeroPrimitiveTomographyGhost A D
  sector_nonzero : PrimitiveDefectImage D (p + 1) ≠ ⊥
  covector : PrimitiveDefectImage D (p + 1) →ₗ[ℚ] ℚ
  covector_eq : covector = firstPrimitiveSectorFunctional F hp D A ghost
  covector_nonzero : covector ≠ 0

/-- Every trace-zero primitive ghost at the first failure canonically supplies
the quotient-native primal/dual sector packet. -/
noncomputable def toFirstPrimitiveProjectiveDualSectorPacket
    {R : HodgeFunctorialGeometricSemantics V H}
    {T : GSTClassicalHodgeProjectiveDegreeTrace.ProjectiveDegreeTraceSemantics V H}
    (F : FirstAtomicDefectWeight V H)
    {p : Nat}
    (hp : F.weight = p + 1)
    (D : LefschetzPrimitiveDecomposition R.spine)
    (A : GSTClassicalHodgeAtomicDefectTraceNormalization.TraceAnchor
      R.spine T (p + 1))
    (E : TraceZeroPrimitiveTomographyGhost A D) :
    FirstPrimitiveProjectiveDualSectorPacket R T F p hp D A := by
  refine {
    ghost := E
    sector_nonzero := firstFailure_PrimitiveDefectImage_ne_bot F hp D
    covector := firstPrimitiveSectorFunctional F hp D A E
    covector_eq := rfl
    covector_nonzero := firstPrimitiveSectorFunctional_ne_zero F hp D A E
  }

#check primitiveGhostDefectFunctional
#check primitiveGhostDefectFunctional_detects
#check firstPrimitiveSectorFunctional
#check firstPrimitiveSectorFunctional_ne_zero
#check firstPrimitiveSectorDualAction
#check firstPrimitiveSectorMatrixCoefficient
#check firstPrimitiveSector_identity_coefficient_ne_zero
#check FirstPrimitiveProjectiveDualSectorPacket
#check toFirstPrimitiveProjectiveDualSectorPacket

#print axioms primitiveGhostDefectFunctional_detects
#print axioms firstPrimitiveSectorFunctional_ne_zero
#print axioms firstPrimitiveSector_identity_coefficient_ne_zero
#print axioms toFirstPrimitiveProjectiveDualSectorPacket

end GSTClassicalHodgeFirstPrimitiveProjectiveDualSector
