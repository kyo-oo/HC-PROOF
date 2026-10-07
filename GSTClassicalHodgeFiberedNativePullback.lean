import GSTClassicalHodgeThreeUniverseSeedIdentification
import GSTClassicalHodgePointNormalForm
import GSTClassicalHodgeNativeCycleCosmicShadow

/-!
# GST CLASSICAL HODGE — FIBERED NATIVE PULLBACK UNIVERSE

The base-weight identification is not enough: a genuine classical `(p,p)`
Hodge fiber can have arbitrary multiplicity.  The correct common refinement
therefore remembers both pieces of information simultaneously.

At one fixed weight `p`, an atom is

    (classical multiplicity sheet i, genuine codimension-p point x).

A finite rational state on these atoms has two exact forgetful projections:

* forget the point `x`: recover the classical multiplicity address;
* forget the sheet `i`: recover the genuine finite native point presentation.

Both projections have the same total rational mass and, after passing to the
universal limitless address system, both land on the same scalar multiple of
`compactClMono p`.

This is the pullback object joining the classical multiplicity universe and
the actual projective-cycle universe over the pre-existing limitless GST base.
No cycle-class surjectivity or basis-cycle representative is assumed.
-/

set_option maxHeartbeats 50000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open scoped BigOperators

namespace GSTClassicalHodgeFiberedNativePullback

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeFiberedTransferCompletion
open GSTNativeCodimensionCyclePresentation
open GSTCompactNativeCyclePresentation
open GSTClassicalHodgePointNormalForm
open GSTClassicalHodgeNativeCycleCosmicShadow
open GSTClassicalHodgeNativeTransferAddressIdentification
open GSTClassicalHodgeThreeUniverseSeedIdentification
open GSTTransferBridgeV2

variable (V : SmoothProjectiveComplexScheme)
variable (H : HodgeBigradedBettiData V)
variable (p : Nat)

/-- One common-refinement atom: a genuine classical multiplicity sheet paired
with one genuine projective codimension-p point. -/
abbrev FiberedNativeAtom :=
  ClassicalHodgeBasisIndex V H p × CodimensionPoint V.X p

/-- Finite rational states on multiplicity-labelled native point atoms. -/
abbrev FiberedNativeAddress := FiberedNativeAtom V H p →₀ ℚ

/-- One unit common-refinement atom. -/
def atom
    (i : ClassicalHodgeBasisIndex V H p)
    (x : CodimensionPoint V.X p) :
    FiberedNativeAddress V H p :=
  Finsupp.single (i,x) 1

/-- Forget only the native point and retain the full classical multiplicity
coordinate at fixed weight p. -/
noncomputable def forgetPoint :
    FiberedNativeAddress V H p →ₗ[ℚ]
      (ClassicalHodgeBasisIndex V H p →₀ ℚ) where
  toFun φ := φ.sum fun ix q => Finsupp.single ix.1 q
  map_add' := by
    intro φ ψ
    classical
    simp [Finsupp.sum_add_index']
  map_smul' := by
    intro q φ
    classical
    ext k
    rw [Finsupp.sum_smul_index' (fun i => by simp)]
    simp [Finsupp.sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Finsupp.single_apply]
    by_cases h : k = i.1
    · simp [h]
    · simp [h]
      intro h1 h2
      exact absurd h2 h1

/-- Forget only the multiplicity sheet and retain the genuine native point
presentation. -/
noncomputable def forgetMultiplicity :
    FiberedNativeAddress V H p →ₗ[ℚ]
      FiniteCodimensionPresentation V.X p where
  toFun φ := φ.sum fun ix q => Finsupp.single ix.2 q
  map_add' := by
    intro φ ψ
    classical
    simp [Finsupp.sum_add_index']
  map_smul' := by
    intro q φ
    classical
    ext k
    rw [Finsupp.sum_smul_index' (fun i => by simp)]
    simp [Finsupp.sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Finsupp.single_apply]
    by_cases h : k = i.2
    · simp [h]
    · simp [h]
      intro h1 h2
      exact absurd h2 h1

/-- Embed the fixed-weight multiplicity address into the global fibered Hodge
universe. -/
noncomputable def toGlobalHodgeAddress :
    FiberedNativeAddress V H p →ₗ[ℚ] FiberedHodgeAddress V H where
  toFun φ := Finsupp.embDomain (weightFiberEmbedding V H p) (forgetPoint V H p φ)
  map_add' := by
    intro φ ψ
    simp
  map_smul' := by
    intro q φ
    show Finsupp.embDomain (weightFiberEmbedding V H p)
        (forgetPoint V H p (q • φ)) =
      q • Finsupp.embDomain (weightFiberEmbedding V H p)
        (forgetPoint V H p φ)
    rw [(forgetPoint V H p).map_smul]
    ext a
    simp [Finsupp.embDomain_apply, Finsupp.smul_apply, smul_eq_mul]

/-- Realize the native projection as an actual codimension-p algebraic cycle. -/
noncomputable def toNativeCycle :
    FiberedNativeAddress V H p →ₗ[ℚ] codimensionCycles V.X p where
  toFun φ := realizeFiniteCodimensionPresentation V.X p
    (forgetMultiplicity V H p φ)
  map_add' := by
    intro φ ψ
    show realizeFiniteCodimensionPresentation V.X p
        (forgetMultiplicity V H p (φ + ψ)) =
      realizeFiniteCodimensionPresentation V.X p
        (forgetMultiplicity V H p φ) +
      realizeFiniteCodimensionPresentation V.X p
        (forgetMultiplicity V H p ψ)
    rw [(forgetMultiplicity V H p).map_add,
      realizeFiniteCodimensionPresentation_add]
  map_smul' := by
    intro q φ
    show realizeFiniteCodimensionPresentation V.X p
        (forgetMultiplicity V H p (q • φ)) =
      q • realizeFiniteCodimensionPresentation V.X p
        (forgetMultiplicity V H p φ)
    rw [(forgetMultiplicity V H p).map_smul,
      realizeFiniteCodimensionPresentation_smul]

/-- Total rational mass of a common-refinement state. -/
noncomputable def totalMass : FiberedNativeAddress V H p →ₗ[ℚ] ℚ where
  toFun φ := φ.sum fun _ q => q
  map_add' := by
    intro φ ψ
    classical
    simp [Finsupp.sum_add_index']
  map_smul' := by
    intro q φ
    classical
    rw [Finsupp.sum_smul_index' (fun _ => by simp)]
    simp [smul_eq_mul, Finsupp.sum, Finset.mul_sum]

@[simp]
theorem forgetPoint_atom
    (i : ClassicalHodgeBasisIndex V H p)
    (x : CodimensionPoint V.X p) :
    forgetPoint V H p (atom V H p i x) = Finsupp.single i 1 := by
  classical
  simp [forgetPoint, atom]

@[simp]
theorem forgetMultiplicity_atom
    (i : ClassicalHodgeBasisIndex V H p)
    (x : CodimensionPoint V.X p) :
    forgetMultiplicity V H p (atom V H p i x) = Finsupp.single x 1 := by
  classical
  simp [forgetMultiplicity, atom]

@[simp]
theorem toGlobalHodgeAddress_atom
    (i : ClassicalHodgeBasisIndex V H p)
    (x : CodimensionPoint V.X p) :
    toGlobalHodgeAddress V H p (atom V H p i x) =
      fiberedSheetGenerator V H ⟨p,i⟩ := by
  simp only [toGlobalHodgeAddress]
  rw [forgetPoint_atom]
  simp [fiberedSheetGenerator, weightFiberEmbedding]

@[simp]
theorem toNativeCycle_atom
    (i : ClassicalHodgeBasisIndex V H p)
    (x : CodimensionPoint V.X p) :
    toNativeCycle V H p (atom V H p i x) =
      codimensionPointCycle V.X p x := by
  simp [toNativeCycle, forgetMultiplicity_atom,
    realizeFiniteCodimensionPresentation_single]

@[simp]
theorem totalMass_atom
    (i : ClassicalHodgeBasisIndex V H p)
    (x : CodimensionPoint V.X p) :
    totalMass V H p (atom V H p i x) = 1 := by
  classical
  simp [totalMass, atom]

/-- Realization and compact projective normal form are inverse in the missing
direction as well: every finite point presentation is recovered coefficient by
coefficient from its realized native cycle. -/
theorem presentationOfNativeCycle_realize
    (φ : FiniteCodimensionPresentation V.X p) :
    letI : CompactSpace V.X := smoothProjectiveCompactSpace V
    presentationOfNativeCycle V.X p
      (realizeFiniteCodimensionPresentation V.X p φ) = φ := by
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  classical
  ext y
  rw [presentationOfNativeCycle_apply,
    realizeFiniteCodimensionPresentation_apply V.X p φ y.1]
  simp only [Finsupp.sum]
  by_cases hy : y ∈ φ.support
  · refine (Finset.sum_eq_single y ?_ ?_).trans ?_
    · intro b _ hb
      have hne : y.1 ≠ b.1 := fun heq => hb (Subtype.ext heq.symm)
      simp [hne]
    · intro hout
      exact absurd hy hout
    · simp [hy]
  · rw [Finsupp.notMem_support_iff.mp hy]
    refine Finset.sum_eq_zero ?_
    intro x hx
    have hne : y.1 ≠ x.1 := by
      intro heq
      apply hy
      rw [Subtype.ext heq]
      exact hx
    simp [hne]

/-- Hence the finite point presentation and the native codimension-cycle space
are an exact linear normal form on the smooth projective carrier. -/
theorem nativeCycleMass_realize
    (φ : FiniteCodimensionPresentation V.X p) :
    nativeCycleMass V p
        (realizeFiniteCodimensionPresentation V.X p φ) =
      GSTClassicalHodgeNativeCycleCosmicShadow.presentationMass φ := by
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  simp [nativeCycleMass, presentationOfNativeCycle_realize,
    GSTClassicalHodgeNativeCycleCosmicShadow.presentationMass]

/-- Both forgetful projections preserve exactly the same total mass. -/
theorem presentationMass_forgetMultiplicity
    (φ : FiberedNativeAddress V H p) :
    GSTClassicalHodgeNativeCycleCosmicShadow.presentationMass
        (forgetMultiplicity V H p φ) =
      totalMass V H p φ := by
  classical
  induction φ using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | single ix q =>
    simp [forgetMultiplicity, totalMass,
      GSTClassicalHodgeNativeCycleCosmicShadow.presentationMass]

/-- Forgetting the point and then forgetting the classical multiplicity fiber
lands at total mass times the established limitless transfer generator. -/
theorem classicalProjection_to_limitless
    (φ : FiberedNativeAddress V H p) :
    forgetMultiplicityToGST (toGlobalHodgeAddress V H p φ) =
      totalMass V H p φ •
        rationalizeCompactAddress (compactClMono p) := by
  classical
  have hadd : ∀ ψ₁ ψ₂ : FiberedHodgeAddress V H,
      forgetMultiplicityToGST (ψ₁ + ψ₂) =
        forgetMultiplicityToGST ψ₁ + forgetMultiplicityToGST ψ₂ := by
    intro ψ₁ ψ₂
    classical
    simp [forgetMultiplicityToGST, Finsupp.sum_add_index']
  induction φ using Finsupp.induction_linear with
  | zero => simp [map_zero, zero_smul, forgetMultiplicityToGST]
  | add a b ha hb => simp [map_add, add_smul, hadd, ha, hb]
  | single ix q =>
    obtain ⟨i, x⟩ := ix
    have hto : toGlobalHodgeAddress V H p (Finsupp.single (i, x) q) =
        Finsupp.single (⟨p, i⟩ : FiberedHodgeIndex V H) q := by
      simp [toGlobalHodgeAddress, forgetPoint, Finsupp.embDomain_single,
        weightFiberEmbedding]
    rw [hto, forgetMultiplicityToGST_single, rationalize_compactClMono]
    simp [totalMass, atom, smul_eq_mul, pureWeightAddress, compactClCode,
      GSTUniversalAddressBridge.cosmicAddressEquiv]

/-- Forgetting multiplicity to an actual native cycle and then taking its
limitless cosmic shadow lands on the exact same transfer ray with the exact
same total mass. -/
theorem nativeProjection_to_limitless
    (φ : FiberedNativeAddress V H p) :
    pureWeightToUniversalAddress
        (nativeCycleCosmicShadow V p (toNativeCycle V H p φ)) =
      totalMass V H p φ •
        rationalizeCompactAddress (compactClMono p) := by
  rw [nativeCycle_shadow_eq_mass_transfer]
  congr 1
  simp only [toNativeCycle]
  rw [nativeCycleMass_realize]
  exact presentationMass_forgetMultiplicity V H p φ

/-- **THE FIBERED NATIVE PULLBACK SQUARE COMMUTES.**
The classical-multiplicity projection and the genuine-native-cycle projection
of every common-refinement state have exactly the same limitless universal
address. -/
theorem fibered_native_limitless_square
    (φ : FiberedNativeAddress V H p) :
    forgetMultiplicityToGST (toGlobalHodgeAddress V H p φ) =
      pureWeightToUniversalAddress
        (nativeCycleCosmicShadow V p (toNativeCycle V H p φ)) := by
  rw [classicalProjection_to_limitless]
  rw [nativeProjection_to_limitless]

/-- On a single atom the commuting square simultaneously recovers the genuine
classical sheet, the genuine native point cycle, and the existing limitless
transfer seed. -/
theorem atom_three_faces
    (i : ClassicalHodgeBasisIndex V H p)
    (x : CodimensionPoint V.X p) :
    toGlobalHodgeAddress V H p (atom V H p i x) =
      fiberedSheetGenerator V H ⟨p,i⟩
    ∧ toNativeCycle V H p (atom V H p i x) =
      codimensionPointCycle V.X p x
    ∧ forgetMultiplicityToGST
        (toGlobalHodgeAddress V H p (atom V H p i x)) =
      rationalizeCompactAddress (compactClMono p) := by
  refine ⟨toGlobalHodgeAddress_atom V H p i x,
    toNativeCycle_atom V H p i x, ?_⟩
  rw [toGlobalHodgeAddress_atom]
  exact classicalSheet_eq_rationalized_transfer V H p i

/-- Crown: arbitrary multiplicity is retained until the very last projection,
while the native and classical faces share one exact limitless base address. -/
theorem fibered_native_pullback_crown :
    (∀ i x,
      toGlobalHodgeAddress V H p (atom V H p i x) =
        fiberedSheetGenerator V H ⟨p,i⟩)
    ∧ (∀ i x,
      toNativeCycle V H p (atom V H p i x) =
        codimensionPointCycle V.X p x)
    ∧ (∀ φ,
      forgetMultiplicityToGST (toGlobalHodgeAddress V H p φ) =
        pureWeightToUniversalAddress
          (nativeCycleCosmicShadow V p (toNativeCycle V H p φ))) := by
  exact ⟨toGlobalHodgeAddress_atom V H p,
    toNativeCycle_atom V H p,
    fibered_native_limitless_square V H p⟩

#check FiberedNativeAtom
#check FiberedNativeAddress
#check atom
#check forgetPoint
#check forgetMultiplicity
#check toGlobalHodgeAddress
#check toNativeCycle
#check presentationOfNativeCycle_realize
#check fibered_native_limitless_square
#check atom_three_faces
#check fibered_native_pullback_crown

#print axioms presentationOfNativeCycle_realize
#print axioms nativeCycleMass_realize
#print axioms classicalProjection_to_limitless
#print axioms nativeProjection_to_limitless
#print axioms fibered_native_limitless_square
#print axioms atom_three_faces
#print axioms fibered_native_pullback_crown

/-! ## Explicit simultaneous lifting of the two finite marginals -/

/-- Augmentation of a full multiplicity address, before forgetting its labels. -/
noncomputable def multiplicityMass :
    (ClassicalHodgeBasisIndex V H p →₀ ℚ) →ₗ[ℚ] ℚ where
  toFun a := a.sum fun _ q => q
  map_add' := by
    intro a b
    classical
    simp [Finsupp.sum_add_index']
  map_smul' := by
    intro q a
    classical
    rw [Finsupp.sum_smul_index' (fun _ => by simp)]
    simp [smul_eq_mul, Finsupp.sum, Finset.mul_sum]

@[simp] theorem multiplicityMass_single
    (i : ClassicalHodgeBasisIndex V H p) (q : ℚ) :
    multiplicityMass V H p (Finsupp.single i q) = q := by
  classical
  simp [multiplicityMass]

/-- Attach one native point to every entry of a multiplicity address. -/
noncomputable def attachPoint (x : CodimensionPoint V.X p) :
    (ClassicalHodgeBasisIndex V H p →₀ ℚ) →ₗ[ℚ] FiberedNativeAddress V H p where
  toFun a := a.sum fun i q => q • atom V H p i x
  map_add' := by
    intro a b
    classical
    simp [Finsupp.sum_add_index']
  map_smul' := by
    intro q a
    classical
    rw [Finsupp.sum_smul_index' (fun _ => by simp)]
    simp [smul_eq_mul, Finsupp.sum, Finset.mul_sum]
    first
    | rw [Finset.smul_sum, ← smul_smul]
    | rw [Finset.smul_sum, smul_smul]
    | simp [smul_smul]

/-- Attach one multiplicity label to a genuine finite native presentation. -/
noncomputable def attachSheet (i : ClassicalHodgeBasisIndex V H p) :
    FiniteCodimensionPresentation V.X p →ₗ[ℚ] FiberedNativeAddress V H p where
  toFun b := b.sum fun x q => q • atom V H p i x
  map_add' := by
    intro a b
    classical
    simp [Finsupp.sum_add_index']
  map_smul' := by
    intro q a
    classical
    rw [Finsupp.sum_smul_index' (fun _ => by simp)]
    simp [smul_eq_mul, Finsupp.sum, Finset.mul_sum]
    first
    | rw [Finset.smul_sum, ← smul_smul]
    | rw [Finset.smul_sum, smul_smul]
    | simp [smul_smul]

@[simp] theorem forgetPoint_attachPoint (x : CodimensionPoint V.X p)
    (a : ClassicalHodgeBasisIndex V H p →₀ ℚ) :
    forgetPoint V H p (attachPoint V H p x a) = a := by
  classical
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | single i q => simp [attachPoint, atom, forgetPoint]

@[simp] theorem forgetMultiplicity_attachPoint (x : CodimensionPoint V.X p)
    (a : ClassicalHodgeBasisIndex V H p →₀ ℚ) :
    forgetMultiplicity V H p (attachPoint V H p x a) =
      multiplicityMass V H p a • Finsupp.single x 1 := by
  classical
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb, add_smul]
  | single i q => simp [attachPoint, atom, forgetMultiplicity]

@[simp] theorem forgetMultiplicity_attachSheet (i : ClassicalHodgeBasisIndex V H p)
    (b : FiniteCodimensionPresentation V.X p) :
    forgetMultiplicity V H p (attachSheet V H p i b) = b := by
  classical
  induction b using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | single x q => simp [attachSheet, atom, forgetMultiplicity]

@[simp] theorem forgetPoint_attachSheet (i : ClassicalHodgeBasisIndex V H p)
    (b : FiniteCodimensionPresentation V.X p) :
    forgetPoint V H p (attachSheet V H p i b) =
      presentationMass b • Finsupp.single i 1 := by
  classical
  induction b using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb, add_smul]
  | single x q => simp [attachSheet, atom, forgetPoint]

/-- Both marginals have the same augmentation for every finite atom state. -/
theorem marginal_mass_balance (Φ : FiberedNativeAddress V H p) :
    multiplicityMass V H p (forgetPoint V H p Φ) =
      presentationMass (forgetMultiplicity V H p Φ) := by
  classical
  induction Φ using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | single ix q =>
    simp [forgetPoint, forgetMultiplicity, multiplicityMass, presentationMass]

/-- An explicit gluing formula. The subtracted anchor removes the duplicated
mass; no basis-cycle or cycle-class surjectivity hypothesis is used. -/
noncomputable def glueMarginals
    (i₀ : ClassicalHodgeBasisIndex V H p) (x₀ : CodimensionPoint V.X p)
    (a : ClassicalHodgeBasisIndex V H p →₀ ℚ)
    (b : FiniteCodimensionPresentation V.X p) : FiberedNativeAddress V H p :=
  attachPoint V H p x₀ a + attachSheet V H p i₀ b -
    multiplicityMass V H p a • atom V H p i₀ x₀

theorem glueMarginals_forgetPoint
    (i₀ : ClassicalHodgeBasisIndex V H p) (x₀ : CodimensionPoint V.X p)
    (a : ClassicalHodgeBasisIndex V H p →₀ ℚ)
    (b : FiniteCodimensionPresentation V.X p)
    (hm : multiplicityMass V H p a = presentationMass b) :
    forgetPoint V H p (glueMarginals V H p i₀ x₀ a b) = a := by
  simp [glueMarginals, hm]

theorem glueMarginals_forgetMultiplicity
    (i₀ : ClassicalHodgeBasisIndex V H p) (x₀ : CodimensionPoint V.X p)
    (a : ClassicalHodgeBasisIndex V H p →₀ ℚ)
    (b : FiniteCodimensionPresentation V.X p) :
    forgetMultiplicity V H p (glueMarginals V H p i₀ x₀ a b) = b := by
  simp [glueMarginals, add_sub_cancel_left]

/-- Exact image of the two-marginal map, including arbitrary multiplicity:
equal mass is precisely enough to glue finite addresses. This theorem is
about the address projections, not an identification with `H.cycleClass`. -/
theorem exists_joint_marginals_iff
    (i₀ : ClassicalHodgeBasisIndex V H p) (x₀ : CodimensionPoint V.X p)
    (a : ClassicalHodgeBasisIndex V H p →₀ ℚ)
    (b : FiniteCodimensionPresentation V.X p) :
    (∃ Φ : FiberedNativeAddress V H p,
      forgetPoint V H p Φ = a ∧ forgetMultiplicity V H p Φ = b) ↔
      multiplicityMass V H p a = presentationMass b := by
  constructor
  · rintro ⟨Φ, rfl, rfl⟩
    exact marginal_mass_balance V H p Φ
  · intro hm
    exact ⟨glueMarginals V H p i₀ x₀ a b,
      glueMarginals_forgetPoint V H p i₀ x₀ a b hm,
      glueMarginals_forgetMultiplicity V H p i₀ x₀ a b⟩

#print axioms exists_joint_marginals_iff
#print axioms glueMarginals_forgetPoint
#print axioms glueMarginals_forgetMultiplicity

end GSTClassicalHodgeFiberedNativePullback
