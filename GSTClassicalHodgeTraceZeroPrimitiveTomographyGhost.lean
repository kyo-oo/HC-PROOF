import GSTClassicalHodgeAtomicDefectTraceNormalization
import GSTClassicalHodgePrimitiveDefectTomographyGhost

/-!
# GST CLASSICAL HODGE — TRACE-ZERO PRIMITIVE TOMOGRAPHY GHOST

A surviving primitive atomic defect already produces a multiplicity-faithful
fibered tomography ghost.  The projective-degree normalization theorem lets us
remove the geometric trace direction from that ghost without changing its
atomic defect.

More is true: the original atomic separator still detects the normalized
trace-zero representative.  The correction term is algebraic, and the
separator annihilates the entire atomic cycle-class span.

Thus every surviving primitive defect, in the presence of one genuine
nonzero-trace algebraic anchor, produces a class with all of the following at
once:

* genuine rational Hodge;
* projective trace zero;
* nonzero atomic defect;
* nonzero atomic-separator read;
* nonzero full fibered multiplicity address;
* nonzero completed fibered tomography moment.

This is a strictly sharper residual object than the earlier primitive ghost.
The base projective-degree direction has been quotiented away while no Hodge
multiplicity information has been forgotten.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeTraceZeroPrimitiveTomographyGhost

open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeAtomicDefectDuality
open GSTClassicalHodgeAtomicAnnihilator
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeProjectiveDegreeTrace
open GSTClassicalHodgePrimitiveAtomicDefectReduction
open GSTClassicalHodgePrimitiveDefectTomographyGhost
open GSTClassicalHodgeAtomicDefectTraceNormalization

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {G : GeometricCycleClassSpine V H}
variable {D : LefschetzPrimitiveDecomposition G}
variable {T : ProjectiveDegreeTraceSemantics V H}
variable {p : Nat}

/-- Trace-zero Hodge representative of one primitive atomic separator. -/
noncomputable def traceZeroPrimitiveRepresentative
    (A : TraceAnchor G T p)
    (E : PrimitiveAtomicSeparator D p) :
    ClassicalHodgeFiber V H p :=
  A.traceZeroRepresentative E.primitiveClass.1

/-- The normalized primitive representative has projective trace zero. -/
theorem traceZeroPrimitiveRepresentative_trace
    (A : TraceAnchor G T p)
    (E : PrimitiveAtomicSeparator D p) :
    T.trace p (traceZeroPrimitiveRepresentative A E).1 = 0 := by
  exact A.trace_traceZeroRepresentative E.primitiveClass.1

/-- The normalized representative has exactly the same nonzero atomic defect
as the original primitive class. -/
theorem traceZeroPrimitiveRepresentative_defect
    (A : TraceAnchor G T p)
    (E : PrimitiveAtomicSeparator D p) :
    atomicDefectLinearMap V H p (traceZeroPrimitiveRepresentative A E) =
      atomicDefectLinearMap V H p E.primitiveClass.1 := by
  exact A.atomicDefect_traceZeroRepresentative E.primitiveClass.1

/-- The normalized representative still carries nonzero defect. -/
theorem traceZeroPrimitiveRepresentative_defect_ne_zero
    (A : TraceAnchor G T p)
    (E : PrimitiveAtomicSeparator D p) :
    atomicDefectLinearMap V H p (traceZeroPrimitiveRepresentative A E) ≠ 0 := by
  rw [traceZeroPrimitiveRepresentative_defect A E]
  exact E.defect_ne_zero

/-- The separator annihilates the normalized algebraic trace anchor. -/
theorem separator_kills_normalizedAnchor
    (A : TraceAnchor G T p)
    (E : PrimitiveAtomicSeparator D p) :
    E.detector A.normalizedHodgeClass.1 = 0 := by
  have hker :
      pointCycleClassSpan p (H.cycleClass p) ≤ LinearMap.ker E.detector :=
    (annihilatesPointCycles_iff_atomicSpan_le_ker
      p (H.cycleClass p) E.detector).mp E.annihilates_atoms
  apply hker
  have hzero := A.atomicDefect_normalizedHodgeClass_zero
  change Submodule.Quotient.mk A.normalizedHodgeClass.1 = 0 at hzero
  exact (Submodule.Quotient.mk_eq_zero
    (pointCycleClassSpan p (H.cycleClass p))).mp hzero

/-- **THE ORIGINAL SEPARATOR SURVIVES TRACE NORMALIZATION.** -/
theorem separator_detects_traceZeroPrimitiveRepresentative
    (A : TraceAnchor G T p)
    (E : PrimitiveAtomicSeparator D p) :
    E.detector (traceZeroPrimitiveRepresentative A E).1 ≠ 0 := by
  unfold traceZeroPrimitiveRepresentative
  rw [TraceAnchor.traceZeroRepresentative]
  simp only [map_sub, map_smul]
  rw [separator_kills_normalizedAnchor A E]
  simp
  exact E.detects_primitive

/-- The trace-zero representative is itself nonzero. -/
theorem traceZeroPrimitiveRepresentative_ne_zero
    (A : TraceAnchor G T p)
    (E : PrimitiveAtomicSeparator D p) :
    traceZeroPrimitiveRepresentative A E ≠ 0 := by
  intro hz
  apply separator_detects_traceZeroPrimitiveRepresentative A E
  rw [hz]
  exact E.detector.map_zero

/-- Its full fibered multiplicity address remains nonzero. -/
theorem traceZeroPrimitive_fiberedAddress_ne_zero
    (A : TraceAnchor G T p)
    (E : PrimitiveAtomicSeparator D p) :
    fiberedWeightCoordinates V H p (traceZeroPrimitiveRepresentative A E) ≠ 0 := by
  intro hz
  have h0 :
      fiberedWeightCoordinates V H p
          (0 : ClassicalHodgeFiber V H p) = 0 := by
    simp [fiberedWeightCoordinates]
  have heq : traceZeroPrimitiveRepresentative A E = 0 :=
    fiberedWeightCoordinates_injective V H p (hz.trans h0.symm)
  exact traceZeroPrimitiveRepresentative_ne_zero A E heq

/-- The trace-zero primitive residual still has an explicit nonzero completed
tomography read in the full fibered universe. -/
theorem exists_traceZero_fiberedProbe_detecting
    (A : TraceAnchor G T p)
    (E : PrimitiveAtomicSeparator D p) :
    ∃ s : FiberedHodgeIndex V H,
      fiberedPairing
          (fiberedWeightCoordinates V H p
            (traceZeroPrimitiveRepresentative A E))
          (fiberedProbe s) ≠ 0 := by
  let a := fiberedWeightCoordinates V H p
    (traceZeroPrimitiveRepresentative A E)
  have ha : a ≠ 0 := traceZeroPrimitive_fiberedAddress_ne_zero A E
  have hsupp : a.support.Nonempty := Finsupp.support_nonempty_iff.mpr ha
  let s := hsupp.choose
  have hs : a s ≠ 0 := Finsupp.mem_support_iff.mp hsupp.choose_spec
  refine ⟨s, ?_⟩
  simpa [a] using hs

/-- Complete residual packet after trace normalization. -/
structure TraceZeroPrimitiveTomographyGhost
    (A : TraceAnchor G T p)
    (D : LefschetzPrimitiveDecomposition G) where
  source : PrimitiveAtomicSeparator D p
  traceZeroClass : ClassicalHodgeFiber V H p
  class_eq : traceZeroClass = traceZeroPrimitiveRepresentative A source
  trace_zero : T.trace p traceZeroClass.1 = 0
  defect_ne_zero : atomicDefectLinearMap V H p traceZeroClass ≠ 0
  separator_detects : source.detector traceZeroClass.1 ≠ 0
  probe : FiberedCompletedAddress V H
  tomography_nonzero :
    fiberedPairing (fiberedWeightCoordinates V H p traceZeroClass) probe ≠ 0

/-- Every primitive separator canonically upgrades to the trace-zero packet. -/
noncomputable def PrimitiveAtomicSeparator.toTraceZeroTomographyGhost
    (A : TraceAnchor G T p)
    (E : PrimitiveAtomicSeparator D p) :
    TraceZeroPrimitiveTomographyGhost A D := by
  rcases exists_traceZero_fiberedProbe_detecting A E with ⟨s, hs⟩
  refine {
    source := E
    traceZeroClass := traceZeroPrimitiveRepresentative A E
    class_eq := rfl
    trace_zero := traceZeroPrimitiveRepresentative_trace A E
    defect_ne_zero := traceZeroPrimitiveRepresentative_defect_ne_zero A E
    separator_detects := separator_detects_traceZeroPrimitiveRepresentative A E
    probe := fiberedProbe s
    tomography_nonzero := hs
  }

/-- **PRIMITIVE FAILURE -> TRACE-ZERO MULTIPLICITY-FAITHFUL GHOST.** -/
theorem primitiveDefect_yields_traceZeroTomographyGhost
    (A : TraceAnchor G T p)
    (hdef : D.primitiveDefectMap p ≠ 0) :
    Nonempty (TraceZeroPrimitiveTomographyGhost A D) := by
  let E := Classical.choice
    (exists_primitiveAtomicSeparator_of_defect_ne_zero
      (D := D) (p := p) hdef)
  exact ⟨E.toTraceZeroTomographyGhost A⟩

#check traceZeroPrimitiveRepresentative
#check traceZeroPrimitiveRepresentative_trace
#check traceZeroPrimitiveRepresentative_defect
#check separator_detects_traceZeroPrimitiveRepresentative
#check traceZeroPrimitive_fiberedAddress_ne_zero
#check TraceZeroPrimitiveTomographyGhost
#check PrimitiveAtomicSeparator.toTraceZeroTomographyGhost
#check primitiveDefect_yields_traceZeroTomographyGhost

#print axioms traceZeroPrimitiveRepresentative_trace
#print axioms separator_detects_traceZeroPrimitiveRepresentative
#print axioms traceZeroPrimitive_fiberedAddress_ne_zero
#print axioms PrimitiveAtomicSeparator.toTraceZeroTomographyGhost
#print axioms primitiveDefect_yields_traceZeroTomographyGhost

end GSTClassicalHodgeTraceZeroPrimitiveTomographyGhost
