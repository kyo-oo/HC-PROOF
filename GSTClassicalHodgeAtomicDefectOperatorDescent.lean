import GSTClassicalHodgeAtomicDefectDuality
import GSTClassicalHodgeAtomicDefectTomographySynchronization
import GSTClassicalHodgeNativeGeneratorNaturality
import GSTClassicalHodgeProjectiveCorrespondenceCosmicRealization

/-!
# GST CLASSICAL HODGE — ATOMIC DEFECT OPERATOR DESCENT

The genuine algebraic obstruction is the quotient

  H^(2p)(X,Q) / span{ genuine codimension-p point-cycle classes }.

This file proves that every cohomological operator preserving the complete
atomic cycle-class span acts canonically on that quotient.  In particular every
genuine projective-correspondence operator supplied by the geometric
cycle-class spine descends automatically.

This is deliberately weaker than any Hodge closure statement.  The descended
operator is allowed to move a nonzero defect to another nonzero defect.  No
basis vector is declared algebraic and no GST matrix unit is asserted to be a
native correspondence.  The payoff is that native/projective geometry and the
synchronized GST tomography obstruction now live on the SAME quotient carrier.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeAtomicDefectOperatorDescent

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeAtomicDefectDuality
open GSTClassicalHodgeNativeGeneratorNaturality
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeProjectiveCorrespondenceAlgebra
open GSTClassicalHodgeProjectiveCorrespondenceCosmicRealization
open GSTClassicalHodgeAtomicDefectTomographyGhost
open GSTClassicalHodgeAtomicDefectTomographySynchronization
open GSTClassicalHodgeOmniversalSeparatorGhostCrown
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeGeneratorwiseAtomicStability

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

abbrev Coh := RationalSingularCohomology H.analytification (2 * p)
abbrev AtomicSpan := pointCycleClassSpan p (H.cycleClass p)
abbrev Defect := AtomicDefectSpace V H p

/-- The quotient-valued cohomological map obtained by applying `T` and then
forgetting the complete atomic span. -/
noncomputable def quotientAfter
    (T : Coh (H := H) p →ₗ[ℚ] Coh (H := H) p) :
    Coh (H := H) p →ₗ[ℚ] Defect (V := V) (H := H) p :=
  (Submodule.mkQ (AtomicSpan (H := H) p)).comp T

/-- Atomic-span preservation is exactly enough to make `quotientAfter T`
vanish on representatives of the quotienting submodule. -/
theorem atomicSpan_le_ker_quotientAfter
    (T : Coh (H := H) p →ₗ[ℚ] Coh (H := H) p)
    (hT : AtomicSpanStable (p := p) (cl := H.cycleClass p) T) :
    AtomicSpan (H := H) p ≤ LinearMap.ker (quotientAfter (V := V) T) := by
  intro alpha halpha
  change Submodule.Quotient.mk (T alpha) = 0
  exact (Submodule.Quotient.mk_eq_zero (AtomicSpan (H := H) p)).2
    (hT alpha halpha)

/-- **ATOMIC DEFECT OPERATOR DESCENT.**  Every atomic-natural cohomological
operator induces a canonical endomorphism of the genuine atomic defect space. -/
noncomputable def atomicDefectOperator
    (T : Coh (H := H) p →ₗ[ℚ] Coh (H := H) p)
    (hT : AtomicSpanStable (p := p) (cl := H.cycleClass p) T) :
    Defect (V := V) (H := H) p →ₗ[ℚ] Defect (V := V) (H := H) p :=
  Submodule.liftQ
    (AtomicSpan (H := H) p)
    (quotientAfter (V := V) T)
    (atomicSpan_le_ker_quotientAfter (V := V) T hT)

/-- On an actual representative the descended operator is literally `T`
followed by quotient projection. -/
@[simp]
theorem atomicDefectOperator_mk
    (T : Coh (H := H) p →ₗ[ℚ] Coh (H := H) p)
    (hT : AtomicSpanStable (p := p) (cl := H.cycleClass p) T)
    (alpha : Coh (H := H) p) :
    atomicDefectOperator (V := V) T hT (Submodule.Quotient.mk alpha) =
      Submodule.Quotient.mk (T alpha) := by
  rfl

/-- The descended identity is the identity of the defect quotient. -/
theorem atomicDefectOperator_id
    (hId : AtomicSpanStable (p := p) (cl := H.cycleClass p)
      (LinearMap.id : Coh (H := H) p →ₗ[ℚ] Coh (H := H) p)) :
    atomicDefectOperator (V := V)
      (LinearMap.id : Coh (H := H) p →ₗ[ℚ] Coh (H := H) p) hId =
      LinearMap.id := by
  apply LinearMap.ext
  intro z
  refine Submodule.Quotient.induction_on z ?_
  intro alpha
  rfl

/-- Descent respects composition.  This makes the quotient a genuine module
for every atomic-natural operator algebra. -/
theorem atomicDefectOperator_comp
    (T U : Coh (H := H) p →ₗ[ℚ] Coh (H := H) p)
    (hT : AtomicSpanStable (p := p) (cl := H.cycleClass p) T)
    (hU : AtomicSpanStable (p := p) (cl := H.cycleClass p) U)
    (hTU : AtomicSpanStable (p := p) (cl := H.cycleClass p) (T.comp U)) :
    atomicDefectOperator (V := V) (T.comp U) hTU =
      (atomicDefectOperator (V := V) T hT).comp
        (atomicDefectOperator (V := V) U hU) := by
  apply LinearMap.ext
  intro z
  refine Submodule.Quotient.induction_on z ?_
  intro alpha
  rfl

/-- Every genuine projective-correspondence cohomological operator is atomic
natural: on each point class its image is represented by the native
correspondence image of that point cycle. -/
theorem projectiveCorrespondence_atomicSpanStable
    (G : GeometricCycleClassSpine V H)
    (K : ProjectiveNativeKernel V p) :
    AtomicSpanStable (p := p) (cl := H.cycleClass p)
      (projectiveCorrespondencePair G K).cohomologyOperator := by
  rw [smoothProjective_atomicStable_iff_nativePointLifts]
  intro x
  refine ⟨
    (projectiveCorrespondencePair G K).cycleOperator
      (codimensionPointCycle V.X p x), ?_⟩
  exact (projectiveCorrespondencePair G K).cycleClass_cycleOperator
    (codimensionPointCycle V.X p x)

/-- Canonical quotient action of one genuine projective-correspondence kernel. -/
noncomputable def projectiveDefectOperator
    (G : GeometricCycleClassSpine V H)
    (K : ProjectiveNativeKernel V p) :
    Defect (V := V) (H := H) p →ₗ[ℚ] Defect (V := V) (H := H) p :=
  atomicDefectOperator (V := V)
    (projectiveCorrespondencePair G K).cohomologyOperator
    (projectiveCorrespondence_atomicSpanStable G K)

/-- Exact representative formula for genuine projective quotient transport. -/
@[simp]
theorem projectiveDefectOperator_mk
    (G : GeometricCycleClassSpine V H)
    (K : ProjectiveNativeKernel V p)
    (alpha : Coh (H := H) p) :
    projectiveDefectOperator G K (Submodule.Quotient.mk alpha) =
      Submodule.Quotient.mk
        ((projectiveCorrespondencePair G K).cohomologyOperator alpha) := by
  rfl

/-- A ghost defect can therefore be transported by genuine projective geometry
without ever choosing a cycle representative for the defect itself. -/
theorem projectiveDefectOperator_ghostAtomicDefect
    {G : GeometricCycleClassSpine V H}
    (E : OmniversalSeparatorGhost G)
    (K : ProjectiveNativeKernel V E.weight) :
    projectiveDefectOperator G K (ghostAtomicDefect E) =
      Submodule.Quotient.mk
        ((projectiveCorrespondencePair G K).cohomologyOperator
          (classicalHodgeBasis V H E.weight E.sheet).1) := by
  rw [ghostAtomicDefect, atomicDefectLinearMap_apply]
  exact projectiveDefectOperator_mk G K _

/-- Evaluation of the ghost's descended separator after projective defect
transport is exactly its ambient separator evaluated on the projective image of
the failed Hodge sheet.  This is the quotient-level horizontal observable that
remains meaningful even though every projective image of an ALGEBRAIC source
has zero separator reading. -/
theorem ghostDefectDetector_projectiveDefectOperator
    {G : GeometricCycleClassSpine V H}
    (E : OmniversalSeparatorGhost G)
    (K : ProjectiveNativeKernel V E.weight) :
    ghostDefectDetector E
      (projectiveDefectOperator G K (ghostAtomicDefect E)) =
      E.separator.detector
        ((projectiveCorrespondencePair G K).cohomologyOperator
          (classicalHodgeBasis V H E.weight E.sheet).1) := by
  rw [projectiveDefectOperator_ghostAtomicDefect E K]
  exact ghostDefectDetector_mk E _

#check quotientAfter
#check atomicSpan_le_ker_quotientAfter
#check atomicDefectOperator
#check atomicDefectOperator_mk
#check atomicDefectOperator_id
#check atomicDefectOperator_comp
#check projectiveCorrespondence_atomicSpanStable
#check projectiveDefectOperator
#check projectiveDefectOperator_mk
#check projectiveDefectOperator_ghostAtomicDefect
#check ghostDefectDetector_projectiveDefectOperator

#print axioms atomicDefectOperator_mk
#print axioms atomicDefectOperator_comp
#print axioms projectiveCorrespondence_atomicSpanStable
#print axioms projectiveDefectOperator_ghostAtomicDefect
#print axioms ghostDefectDetector_projectiveDefectOperator

end GSTClassicalHodgeAtomicDefectOperatorDescent
