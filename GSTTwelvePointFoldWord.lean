import GSTTwelvePointHodgeData
import GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra
import GSTClassicalHodgeFiniteClosedCorrespondence
import GSTClassicalHodgeFiniteClosedCorrespondenceOperator
import GSTNativeCodimensionCyclePresentation
import GSTClassicalHodgeProjectiveSelfCorrespondences
import GSTClassicalHodgeProjectivePointTransport
import Mathlib

/-!
# GST TWELVE-POINT — THE OWNER'S FOLD AS A GENUINE REALIZED CORRESPONDENCE WORD

This module lands Part 3 of the twelve-point native geometric world record
(`research/records/2026-11-14-gst-twelve-point-native-geometric-world.md`):
the fold matrix `T = U + J + M` is realized on the first genuine world
`(V₀, H₀)` as a `RealizedCorrespondenceWord` of 26 weighted point-pair
correspondences, and the word's cohomology operator is proved to BE the fold
matrix under the H⁰ cohomology iso.

Each letter is the closed point-pair subscheme `Spec ℂ ⟶ X ×_ℂ X` with left
leg the `c`-th point and right leg the `r`-th point:

* the ring map is the evaluation composite `ℂ¹² ⊗_ℂ ℂ¹² →ₐ[ℂ] ℂ`,
  `a ⊗ b ↦ (a c) * (b r)`, surjective, hence a closed immersion by
  `IsClosedImmersion.spec_of_surjective` composed with the `pullbackSpecIso`
  inverse;
* the left fibers are singletons or empty (`Spec ℂ` has one point);
* the right leg's residue degree at the unique carrier point is `1`
  (the residue-field extension is trivial, proved through the open-immersion
  instance for the evaluation `Spec` map).

The realization equation on the twelve point classes is the matrix column:
`matrixUnitOp r c` sends `e i ↦ (if c = i then e r else 0)`, and the word
operator sends `e c ↦ Σ_r Twave r c • e r`.  The full operator theorem uses
the point-class decomposition of `H⁰` (every class is the sum of its
coordinates times point classes).

External lemma names marked `AUDIT-n` are the author-wave uncertainty points
(this module is written before its unwritten upstream sibling modules are
compiled; the CI lane owns the kernel check).
-/

set_option maxHeartbeats 70000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicGeometry

namespace GSTTwelvePointFoldWord

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeProjectiveSelfCorrespondences
open GSTClassicalHodgeFiniteClosedCorrespondence
open GSTClassicalHodgeFiniteClosedCorrespondence.FiniteClosedCorrespondence
open GSTClassicalHodgeFiniteClosedCorrespondenceOperator
open GSTClassicalHodgeProjectivePointTransport
open GSTClassicalHodgeRealizedClosedCorrespondenceAlgebra
open GSTClassicalHodgeFiberedCosmology
open GSTTwelvePointWorldCarrier
open GSTTwelvePointCohomology
open GSTTwelvePointHodgeData

/-! ## The twelve points and their classes

The carrier module supplies `twelvePointWorld : SmoothProjectiveComplexScheme`
with `twelvePointWorld.X = Spec (.of (Fin 12 → ℂ))` and the point
classification `twelvePointEquiv : Fin 12 ≃ CodimensionPoint twelvePointWorld.X 0`
(the primes `ker (eval i)`); the Hodge-data module supplies
`twelvePointHodgeData`, `zeroCycleClass`, `zeroCycleClass_point`,
`zeroFiber_eq_top` and `twelvePointCohomologyIso`.
-/

/-- The `i`-th twelve-point as a genuine codimension-0 point. -/
abbrev twelvePointPt (i : Fin 12) : CodimensionPoint twelvePointWorld.X 0 :=
  ⟨(twelvePointEquiv i).1, (twelvePointEquiv i).2⟩

/-- The unit point cycle of the `i`-th twelve-point. -/
abbrev twelvePointPtCycle (i : Fin 12) : codimensionCycles twelvePointWorld.X 0 :=
  codimensionPointCycle twelvePointWorld.X 0 (twelvePointPt i)

/-- The rational point class of the `i`-th twelve-point. -/
abbrev twelvePointPtClass (i : Fin 12) :
    RationalSingularCohomology twelvePointHodgeData.analytification 0 :=
  twelvePointHodgeData.cycleClass 0 (twelvePointPtCycle i)

/-- **AUDIT-1 (carrier bridge).** The `i`-th twelve-point IS the prime
`ker (eval i)` of `ℂ¹²`.  This is definitional for the carrier's
`twelvePointEquiv` (built from `PrimeSpectrum.comap`); it is the single
adaptation point if the carrier's presentation differs. -/
theorem comap_evalRingHom_default (i : Fin 12) :
    PrimeSpectrum.comap (Pi.evalRingHom (fun _ : Fin 12 => ℂ) i)
      (default : Spec (CommRingCat.of ℂ)) = (twelvePointEquiv i).1 :=
  rfl

/-! ## The letter geometry: the point-pair subscheme -/

/-- The evaluation algebra map of the point pair: `a ⊗ b ↦ (a c) * (b r)`. -/
noncomputable def pointPairAlgHom (r c : Fin 12) :
    (Fin 12 → ℂ) ⊗[ℂ] (Fin 12 → ℂ) →ₐ[ℂ] ℂ :=
  (Algebra.TensorProduct.rid ℂ ℂ ℂ).toAlgHom.comp
    (Algebra.TensorProduct.map
      (Pi.evalAlgHom ℂ (fun _ : Fin 12 => ℂ) c)
      (Pi.evalAlgHom ℂ (fun _ : Fin 12 => ℂ) r))

/-- The point-pair ring map is surjective: preimage of `x` is
`Pi.single c x ⊗ₜ 1`. -/
theorem pointPairAlgHom_surjective (r c : Fin 12) :
    Function.Surjective (pointPairAlgHom r c) := by
  intro x
  refine ⟨Pi.single c x ⊗ₜ[ℂ] 1, ?_⟩
  show pointPairAlgHom r c (Pi.single c x ⊗ₜ[ℂ] 1) = x
  -- AUDIT-2 (tensor API): `map_tmul`/`rid_tmul`/`Pi.single_apply` names.
  simp [pointPairAlgHom, Algebra.TensorProduct.map_tmul,
    Algebra.TensorProduct.rid_tmul, Pi.single_apply, mul_one]

/-- The closed point-pair subscheme `Spec ℂ ⟶ X ×_ℂ X` selecting
`(point c, point r)`. -/
noncomputable def pointPairMap (r c : Fin 12) :
    Spec (CommRingCat.of ℂ) ⟶ selfProduct twelvePointWorld :=
  Spec.map (CommRingCat.ofHom (pointPairAlgHom r c).toRingHom) ≫
    (pullbackSpecIso ℂ (Fin 12 → ℂ) (Fin 12 → ℂ)).inv

/-- Ring-hom form of the left leg: evaluate at the column point. -/
theorem pointPair_left_hom (r c : Fin 12) :
    (algebraMap (Fin 12 → ℂ)
        ((Fin 12 → ℂ) ⊗[ℂ] (Fin 12 → ℂ))).comp (pointPairAlgHom r c).toRingHom =
      Pi.evalRingHom (fun _ : Fin 12 => ℂ) c := by
  apply RingHom.ext
  intro a
  show pointPairAlgHom r c
      (algebraMap (Fin 12 → ℂ) ((Fin 12 → ℂ) ⊗[ℂ] (Fin 12 → ℂ)) a) =
    Pi.evalRingHom (fun _ : Fin 12 => ℂ) c a
  have htm : algebraMap (Fin 12 → ℂ) ((Fin 12 → ℂ) ⊗[ℂ] (Fin 12 → ℂ)) a =
      a ⊗ₜ[ℂ] 1 := rfl -- AUDIT-3: left algebra structure on the tensor product
  rw [htm]
  -- AUDIT-2: tensor API names as above.
  simp [pointPairAlgHom, Algebra.TensorProduct.map_tmul,
    Algebra.TensorProduct.rid_tmul, Pi.evalAlgHom_apply, mul_one]

/-- Ring-hom form of the right leg: evaluate at the row point. -/
theorem pointPair_right_hom (r c : Fin 12) :
    (Algebra.TensorProduct.includeRight
        (R := ℂ) (A := Fin 12 → ℂ) (B := Fin 12 → ℂ)).toRingHom.comp
      (pointPairAlgHom r c).toRingHom =
    Pi.evalRingHom (fun _ : Fin 12 => ℂ) r := by
  apply RingHom.ext
  intro a
  show pointPairAlgHom r c
      (Algebra.TensorProduct.includeRight
        (R := ℂ) (A := Fin 12 → ℂ) (B := Fin 12 → ℂ) a) =
    Pi.evalRingHom (fun _ : Fin 12 => ℂ) r a
  have htm : Algebra.TensorProduct.includeRight
      (R := ℂ) (A := Fin 12 → ℂ) (B := Fin 12 → ℂ) a = 1 ⊗ₜ[ℂ] a := rfl -- AUDIT-3
  rw [htm]
  simp [pointPairAlgHom, Algebra.TensorProduct.map_tmul,
    Algebra.TensorProduct.rid_tmul, Pi.evalAlgHom_apply, one_mul]

/-- The left leg of the point pair is evaluation at the column point. -/
theorem pointPair_left (r c : Fin 12) :
    pointPairMap r c ≫ fst twelvePointWorld =
      Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin 12 => ℂ) c)) := by
  rw [pointPairMap, ← CategoryTheory.Category.assoc]
  rw [pullbackSpecIso_inv_fst'] -- AUDIT-2: leg lemma of `pullbackSpecIso`
  rw [← Spec.map_comp]
  refine congrArg Spec.map (congrArg CommRingCat.ofHom ?_)
  apply CommRingCat.hom_ext
  rw [CommRingCat.hom_comp] -- AUDIT-2: `ofHom` composition bookkeeping
  exact pointPair_left_hom r c

/-- The right leg of the point pair is evaluation at the row point. -/
theorem pointPair_right (r c : Fin 12) :
    pointPairMap r c ≫ snd twelvePointWorld =
      Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin 12 => ℂ) r)) := by
  rw [pointPairMap, ← CategoryTheory.Category.assoc]
  rw [pullbackSpecIso_inv_snd] -- AUDIT-2
  rw [← Spec.map_comp]
  refine congrArg Spec.map (congrArg CommRingCat.ofHom ?_)
  apply CommRingCat.hom_ext
  rw [CommRingCat.hom_comp]
  exact pointPair_right_hom r c

/-- Point-level action of the left leg: every carrier point lands on the
column point. -/
theorem pointPair_left_apply (r c : Fin 12) (z : Spec (CommRingCat.of ℂ)) :
    (pointPairMap r c ≫ fst twelvePointWorld) z = (twelvePointEquiv c).1 := by
  rw [pointPair_left]
  show PrimeSpectrum.comap (Pi.evalRingHom (fun _ : Fin 12 => ℂ) c) z = _
  rw [Subsingleton.elim z default]
  exact comap_evalRingHom_default c

/-- Point-level action of the right leg: the unique carrier point lands on
the row point. -/
theorem pointPair_right_apply (r c : Fin 12) (z : Spec (CommRingCat.of ℂ)) :
    (pointPairMap r c ≫ snd twelvePointWorld) z = (twelvePointEquiv r).1 := by
  rw [pointPair_right]
  show PrimeSpectrum.comap (Pi.evalRingHom (fun _ : Fin 12 => ℂ) r) z = _
  rw [Subsingleton.elim z default]
  exact comap_evalRingHom_default r

/-! ## The residue degree of the right leg -/

/-- Evaluation at one point of `ℂ¹²` is surjective. -/
theorem evalRingHom_surjective (r : Fin 12) :
    Function.Surjective (Pi.evalRingHom (fun _ : Fin 12 => ℂ) r) := by
  intro x
  exact ⟨Pi.single r x, by simp [Pi.single_apply]⟩

/-- `Spec` of a surjective evaluation map is an open immersion: the kernel is
generated by the idempotent `1 - Pi.single r 1`. -/
theorem isOpenImmersion_spec_map_eval (r : Fin 12) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (Pi.evalRingHom (fun _ : Fin 12 => ℂ) r))) := by
  rw [isOpenImmersion_SpecMap_iff_of_surjective _ (evalRingHom_surjective r)]
  refine ⟨1 - Pi.single r 1, ?_, ?_⟩
  · show (1 - Pi.single r 1) * (1 - Pi.single r 1) = 1 - Pi.single r 1
    funext i
    by_cases hi : i = r
    · simp [hi, Pi.single_apply]
    · simp [hi, Pi.single_apply]
  · show RingHom.ker (Pi.evalRingHom (fun _ : Fin 12 => ℂ) r) =
      Ideal.span {1 - Pi.single r 1}
    apply le_antisymm
    · intro f hf
      rw [RingHom.mem_ker] at hf -- AUDIT-4: `RingHom.mem_ker`
      refine (Ideal.mem_span_singleton f _).mpr ⟨f, ?_⟩ -- AUDIT-4: span API
      funext i
      by_cases hi : i = r
      · simp [hi, Pi.single_apply, hf]
      · simp [hi, Pi.single_apply]
    · rw [Ideal.span_le] -- AUDIT-4: `Ideal.span_le`
      intro f hf
      rw [Set.mem_singleton_iff] at hf
      subst hf
      rw [RingHom.mem_ker]
      show (1 - Pi.single r 1) r = 0
      simp [Pi.single_apply]

/-- **AUDIT-5 (residue degree).** The residue degree of the right leg at the
unique carrier point is `1`: the right leg is an open immersion, so its
residue field map is an iso, so the induced field extension is rank one. -/
theorem residueDegree_spec_map_eval (r : Fin 12) :
    Scheme.Hom.residueDegree
        (Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin 12 => ℂ) r)))
        (default : Spec (CommRingCat.of ℂ)) = 1 := by
  haveI hoi : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (Pi.evalRingHom (fun _ : Fin 12 => ℂ) r))) :=
    isOpenImmersion_spec_map_eval r
  have hsurj : Function.Surjective (Scheme.Hom.residueFieldMap
      (Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin 12 => ℂ) r)))
      (default : Spec (CommRingCat.of ℂ))) :=
    (ConcreteCategory.bijective_of_isIso _).2
  haveI : Algebra
      ((Spec (CommRingCat.of (Fin 12 → ℂ))).residueField
        (PrimeSpectrum.comap (Pi.evalRingHom (fun _ : Fin 12 => ℂ) r)
          (default : Spec (CommRingCat.of ℂ))))
      ((Spec (CommRingCat.of ℂ)).residueField
        (default : Spec (CommRingCat.of ℂ))) :=
    (Scheme.Hom.residueFieldMap
      (Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin 12 => ℂ) r)))
      (default : Spec (CommRingCat.of ℂ))).hom.toAlgebra
  have hfinrank : Module.finrank
      ((Spec (CommRingCat.of (Fin 12 → ℂ))).residueField
        (PrimeSpectrum.comap (Pi.evalRingHom (fun _ : Fin 12 => ℂ) r)
          (default : Spec (CommRingCat.of ℂ))))
      ((Spec (CommRingCat.of ℂ)).residueField
        (default : Spec (CommRingCat.of ℂ))) = 1 := by
    rw [finrank_eq_one_iff_of_nonzero' 1 one_ne_zero] -- AUDIT-5: lemma name
    intro w
    obtain ⟨a, ha⟩ := hsurj w
    refine ⟨a, ?_⟩
    calc a • (1 : (Spec (CommRingCat.of ℂ)).residueField
          (default : Spec (CommRingCat.of ℂ)))
        = Scheme.Hom.residueFieldMap
            (Spec.map (CommRingCat.ofHom
              (Pi.evalRingHom (fun _ : Fin 12 => ℂ) r)))
            (default : Spec (CommRingCat.of ℂ)) a := by
          rw [Algebra.smul_def, mul_one] -- AUDIT-5: `RingHom.toAlgebra` algebraMap
      _ = w := ha
  exact hfinrank

/-- The right-leg residue weight at the unique carrier point is `1`. -/
theorem pointPair_residueWeight (r c : Fin 12) :
    pointResidueWeight (pointPairMap r c ≫ snd twelvePointWorld)
        (default : Spec (CommRingCat.of ℂ)) = 1 := by
  show (Scheme.Hom.residueDegree
      (pointPairMap r c ≫ snd twelvePointWorld)
      (default : Spec (CommRingCat.of ℂ)) : ℚ) = 1
  rw [pointPair_right]
  rw [residueDegree_spec_map_eval]
  simp

/-! ## The finite closed correspondence of one point pair -/

/-- The finite left-fiber sets of the point pair. -/
theorem pointPair_leftFiberSet_eq (r c : Fin 12) (x : twelvePointWorld.X) :
    ({z : Spec (CommRingCat.of ℂ) |
        (pointPairMap r c ≫ fst twelvePointWorld) z = x} : Set _) =
      if (twelvePointEquiv c).1 = x then
        {default : Spec (CommRingCat.of ℂ)} else ∅ := by
  by_cases hx : (twelvePointEquiv c).1 = x
  · rw [if_pos hx]
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    exact iff_of_true (pointPair_left_apply r c z)
      (Subsingleton.elim z default)
  · rw [if_neg hx]
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false]
    intro hz
    exact hx ((pointPair_left_apply r c z).symm.trans hz)

/-- The genuine finite closed correspondence of the point pair:
`Spec ℂ` closed-immersed into `X ×_ℂ X` on `(point c, point r)`. -/
noncomputable def pointPairGeometry (r c : Fin 12) :
    FiniteClosedCorrespondence twelvePointWorld where
  carrier := Spec (CommRingCat.of ℂ)
  intoProduct := pointPairMap r c
  closedImmersion := by
    have h1 : IsClosedImmersion (Spec.map
        (CommRingCat.ofHom (pointPairAlgHom r c).toRingHom)) :=
      IsClosedImmersion.spec_of_surjective _
        (pointPairAlgHom_surjective r c)
    haveI h2 : IsClosedImmersion
        ((pullbackSpecIso ℂ (Fin 12 → ℂ) (Fin 12 → ℂ)).inv) := inferInstance
    exact IsClosedImmersion.comp h1 h2 -- AUDIT-2: composition instance name
  leftFiber_finite := by
    intro x
    rw [pointPair_leftFiberSet_eq r c x]
    by_cases hx : (twelvePointEquiv c).1 = x
    · rw [if_pos hx]; exact Set.finite_singleton _
    · rw [if_neg hx]; exact Set.finite_empty

/-- The left fiber of the point pair over a source point which IS the column
point is the singleton fiber of the unique carrier point. -/
theorem pointPair_leftFiberFinset_eq_singleton (r c : Fin 12)
    (x : CodimensionPoint twelvePointWorld.X 0)
    (h : (twelvePointEquiv c).1 = x.1) :
    (pointPairGeometry r c).leftFiberFinset x.1 =
      {default : Spec (CommRingCat.of ℂ)} := by
  ext z
  simp only [mem_leftFiberFinset, Finset.mem_singleton]
  rw [← h]
  exact iff_of_true (pointPair_left_apply r c z)
    (Subsingleton.elim z default)

/-- The left fiber over any other source point is empty. -/
theorem pointPair_leftFiberFinset_eq_empty (r c : Fin 12)
    (x : CodimensionPoint twelvePointWorld.X 0)
    (h : (twelvePointEquiv c).1 ≠ x.1) :
    (pointPairGeometry r c).leftFiberFinset x.1 = ∅ := by
  ext z
  simp only [mem_leftFiberFinset, Finset.notMem_empty]
  intro hz
  exact h ((pointPair_left_apply r c z).symm.trans hz)

/-- The coheight of the right image of the unique carrier point is zero. -/
theorem pointPair_right_coheight (r c : Fin 12) :
    Order.coheight
        ((pointPairMap r c ≫ snd twelvePointWorld)
          (default : Spec (CommRingCat.of ℂ))) = 0 := by
  rw [pointPair_right_apply]
  exact (twelvePointEquiv r).2

/-- Over the column point, the transition is the single atom at the row
point with residue weight one. -/
theorem pointPair_transition_eq (r c : Fin 12)
    (x : CodimensionPoint twelvePointWorld.X 0)
    (h : (twelvePointEquiv c).1 = x.1) :
    (pointPairGeometry r c).transition 0 x =
      Finsupp.single (twelvePointPt r) 1 := by
  have hfin : (pointPairGeometry r c).leftFiberFinset x.1 =
      {default : Spec (CommRingCat.of ℂ)} :=
    pointPair_leftFiberFinset_eq_singleton r c x h
  have hz : Order.coheight
      ((pointPairGeometry r c).right (default : Spec (CommRingCat.of ℂ))) = 0 :=
    pointPair_right_coheight r c
  show ((pointPairGeometry r c).leftFiberFinset x.1).sum
      ((pointPairGeometry r c).targetAtomPresentation 0) = _
  rw [hfin, Finset.sum_singleton]
  rw [FiniteClosedCorrespondence.targetAtomPresentation_eq_single
    (pointPairGeometry r c) 0 default hz]
  rw [pointPair_residueWeight r c]
  -- the atom point is the row twelve-point
  have hr : (pointPairGeometry r c).right
      (default : Spec (CommRingCat.of ℂ)) = (twelvePointEquiv r).1 :=
    pointPair_right_apply r c default
  rw [hr]
  rfl

/-- Over the column point, the native image is exactly the row point cycle. -/
theorem pointPair_nativePointImage_eq (r c : Fin 12)
    (x : CodimensionPoint twelvePointWorld.X 0)
    (h : (twelvePointEquiv c).1 = x.1) :
    (pointPairGeometry r c).nativePointImage 0 x =
      codimensionPointCycle twelvePointWorld.X 0 (twelvePointPt r) := by
  show realizeFiniteCodimensionPresentation twelvePointWorld.X 0
      ((pointPairGeometry r c).transition 0 x) = _
  rw [pointPair_transition_eq r c x h]
  rw [realizeFiniteCodimensionPresentation_single]
  exact one_smul _ _

/-- Over any other source point, the native image is the zero cycle. -/
theorem pointPair_nativePointImage_eq_zero (r c : Fin 12)
    (x : CodimensionPoint twelvePointWorld.X 0)
    (h : (twelvePointEquiv c).1 ≠ x.1) :
    (pointPairGeometry r c).nativePointImage 0 x = 0 := by
  have hfin : (pointPairGeometry r c).leftFiberFinset x.1 = ∅ :=
    pointPair_leftFiberFinset_eq_empty r c x h
  show realizeFiniteCodimensionPresentation twelvePointWorld.X 0
      ((pointPairGeometry r c).transition 0 x) = _
  have htr : (pointPairGeometry r c).transition 0 x = 0 := by
    show ((pointPairGeometry r c).leftFiberFinset x.1).sum
        ((pointPairGeometry r c).targetAtomPresentation 0) = _
    rw [hfin, Finset.sum_empty]
  rw [htr]
  exact realizeFiniteCodimensionPresentation_zero twelvePointWorld.X 0

/-! ## The letter operator: the matrix unit -/

/-- The `r`-th indicator map on the twelve coordinate vectors. -/
noncomputable def matrixUnitIndicator (r c : Fin 12) :
    (Fin 12 → ℚ) →ₗ[ℚ] (Fin 12 → ℚ) where
  toFun v k := if k = r then v c else 0
  map_add' := by
    intro v w
    funext k
    by_cases hk : k = r <;> simp [hk]
  map_smul' := by
    intro q v
    funext k
    by_cases hk : k = r <;> simp [hk, Pi.smul_apply, smul_eq_mul]

/-- The matrix unit `(r, c)` operator on H⁰, transported through the
cohomology iso. -/
noncomputable def matrixUnitOp (r c : Fin 12) :
    RationalSingularCohomology twelvePointHodgeData.analytification 0 →ₗ[ℚ]
      RationalSingularCohomology twelvePointHodgeData.analytification 0 :=
  LinearMap.comp (twelvePointCohomologyIso.symm.toLinearMap)
    (LinearMap.comp (matrixUnitIndicator r c)
      twelvePointCohomologyIso.toLinearMap)

theorem matrixUnitOp_apply (r c : Fin 12)
    (u : RationalSingularCohomology twelvePointHodgeData.analytification 0) :
    twelvePointCohomologyIso (matrixUnitOp r c u) =
      fun k => if k = r then twelvePointCohomologyIso u c else 0 := by
  show twelvePointCohomologyIso
      (twelvePointCohomologyIso.symm
        (matrixUnitIndicator r c (twelvePointCohomologyIso u))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

/-- The matrix unit sends the `i`-th point class to the `r`-th indicator when
`i` is the column, and to zero otherwise. -/
theorem matrixUnitOp_pointClass (r c i : Fin 12) :
    twelvePointCohomologyIso (matrixUnitOp r c
        (zeroCycleClass (codimensionPointCycle twelvePointWorld.X 0
          (twelvePointPt i)))) =
      if c = i then Pi.single r (1 : ℚ) else 0 := by
  rw [matrixUnitOp_apply]
  rw [zeroCycleClass_point] -- AUDIT-6: contract lemma, defeq to the
  -- `twelvePointHodgeData.cycleClass 0` view of the argument
  funext k
  by_cases hk : k = r <;> by_cases hi : c = i <;>
    simp [hk, hi, Pi.single_apply]

/-! ## The realization theorem -/

/-- The point pair realizes exactly its matrix unit on all point classes. -/
theorem pointPairGeometry_realizes (r c : Fin 12) :
    (pointPairGeometry r c).RealizesAmbientOnPoints
        (H := twelvePointHodgeData) (matrixUnitOp r c) := by
  intro x
  -- every codimension-0 point is one of the twelve
  obtain ⟨i, hi⟩ := twelvePointEquiv.surjective x -- AUDIT-7: `twelvePointEquiv`
  subst hi
  by_cases hic : i = c
  · subst hic
    have hc : (twelvePointEquiv c).1 = (twelvePointEquiv c).1 := rfl
    have himg := pointPair_nativePointImage_eq r c (twelvePointEquiv c) hc
    show twelvePointHodgeData.cycleClass 0
        ((pointPairGeometry r c).nativePointImage 0 (twelvePointEquiv c)) = _
    rw [himg]
    have key : twelvePointCohomologyIso
        (matrixUnitOp r c (zeroCycleClass
          (codimensionPointCycle twelvePointWorld.X 0 (twelvePointPt c)))) =
        twelvePointCohomologyIso (zeroCycleClass
          (codimensionPointCycle twelvePointWorld.X 0 (twelvePointPt r))) := by
      rw [matrixUnitOp_pointClass r c c]
      rw [if_pos rfl]
      rw [zeroCycleClass_point]
    calc twelvePointHodgeData.cycleClass 0
        (codimensionPointCycle twelvePointWorld.X 0 (twelvePointPt r))
        = twelvePointCohomologyIso.symm (twelvePointCohomologyIso
            (twelvePointHodgeData.cycleClass 0
              (codimensionPointCycle twelvePointWorld.X 0 (twelvePointPt r)))) :=
          (LinearEquiv.symm_apply_apply _ _).symm
      _ = twelvePointCohomologyIso.symm (twelvePointCohomologyIso
            (matrixUnitOp r c (zeroCycleClass
              (codimensionPointCycle twelvePointWorld.X 0 (twelvePointPt c))))) :=
          by rw [key]
      _ = matrixUnitOp r c (zeroCycleClass
            (codimensionPointCycle twelvePointWorld.X 0 (twelvePointPt c))) :=
          LinearEquiv.symm_apply_apply _ _
  · have hne : (twelvePointEquiv c).1 ≠ (twelvePointEquiv i).1 := by
      intro h
      exact hic (twelvePointEquiv.injective (Subtype.ext h)).symm
    have himg := pointPair_nativePointImage_eq_zero r c (twelvePointEquiv i) hne
    show twelvePointHodgeData.cycleClass 0
        ((pointPairGeometry r c).nativePointImage 0 (twelvePointEquiv i)) = _
    rw [himg, map_zero]
    have hzero : matrixUnitOp r c (zeroCycleClass
        (codimensionPointCycle twelvePointWorld.X 0 (twelvePointPt i))) = 0 := by
      calc matrixUnitOp r c (zeroCycleClass
            (codimensionPointCycle twelvePointWorld.X 0 (twelvePointPt i)))
          = twelvePointCohomologyIso.symm (twelvePointCohomologyIso
              (matrixUnitOp r c (zeroCycleClass
                (codimensionPointCycle twelvePointWorld.X 0 (twelvePointPt i))))) :=
            (LinearEquiv.symm_apply_apply _ _).symm
        _ = twelvePointCohomologyIso.symm
              (if c = i then Pi.single r (1 : ℚ) else 0) := by
            rw [matrixUnitOp_pointClass r c i]
        _ = twelvePointCohomologyIso.symm 0 := by
            rw [if_neg (fun h => hic h.symm)]
        _ = 0 := by simp
    rw [hzero]

/-! ## The letter and the 26-letter fold word -/

/-- One weighted point-pair letter: the genuine geometry plus its matrix-unit
operator plus the pointwise realization theorem. -/
noncomputable def pointPairLetter (r c : Fin 12) :
    RealizedFiniteClosedCorrespondence twelvePointWorld twelvePointHodgeData 0 where
  geometry := pointPairGeometry r c
  cohomologyOperator := matrixUnitOp r c
  realizes_on_points := pointPairGeometry_realizes r c

/-- The 26 nonzero entries of the owner's fold matrix, as
`(row, column, weight)` letter data. -/
def foldWordData : List (Fin 12 × Fin 12 × ℚ) :=
  [(0, 0, 1), (0, 11, 1), (1, 4, 1), (1, 10, 1), (2, 8, 1), (2, 9, -1),
   (3, 1, 1), (3, 8, 1), (4, 4, 1), (4, 5, 1), (4, 7, 1), (5, 6, 1),
   (5, 9, 1), (6, 2, 1), (6, 5, -1), (7, 4, -1), (7, 6, 1), (8, 3, -1),
   (8, 8, 1), (8, 10, 1), (9, 2, 1), (9, 3, 1), (10, 1, -1), (10, 7, 1),
   (11, 0, -1), (11, 11, 3)]

/-- The realized correspondence word induced by letter data. -/
noncomputable def lettersOf (L : List (Fin 12 × Fin 12 × ℚ)) :
    RealizedCorrespondenceWord twelvePointWorld twelvePointHodgeData 0 :=
  L.map (fun d => (d.2.2, pointPairLetter d.1 d.2.1))

/-- **THE FOLD WORD**: the owner's fold as a genuine realized correspondence
word of 26 weighted point-pair letters. -/
noncomputable def twelvePointFoldWord :
    RealizedCorrespondenceWord twelvePointWorld twelvePointHodgeData 0 :=
  lettersOf foldWordData

/-- The fold matrix assembled from the same letter data: the entry `(r, c)`
is the sum of the weights of the letters with right point `r` and left
point `c`. -/
def twelvePointFoldMatrix : Matrix (Fin 12) (Fin 12) ℚ :=
  fun r c => (foldWordData.map
    (fun d => if d.2.1 = c then (if d.1 = r then d.2.2 else 0) else 0)).sum

/-! ## The word operator equals the fold matrix -/

/-- Nil-case operator unfolding of the word pair. -/
theorem realizedWordPair_cohomologyOperator_nil :
    (realizedWordPair
        (lettersOf ([] : List (Fin 12 × Fin 12 × ℚ)))).cohomologyOperator =
      0 := rfl

/-- Cons-case operator unfolding of the word pair. -/
theorem realizedWordPair_cohomologyOperator_cons (q : ℚ)
    (R : RealizedFiniteClosedCorrespondence twelvePointWorld twelvePointHodgeData 0)
    (W : RealizedCorrespondenceWord twelvePointWorld twelvePointHodgeData 0) :
    (realizedWordPair ((q, R) :: W)).cohomologyOperator =
      q • R.cohomologyOperator +
        (realizedWordPair W).cohomologyOperator := rfl

/-- **AUDIT-8 (iso linearity).** Linearity of the cohomology iso through its
linear-map structure. -/
theorem cohomologyIso_sum {ι : Type*} (s : Finset ι)
    (g : ι → RationalSingularCohomology
      twelvePointHodgeData.analytification 0) :
    twelvePointCohomologyIso (∑ i ∈ s, g i) =
      ∑ i ∈ s, twelvePointCohomologyIso (g i) :=
    map_sum twelvePointCohomologyIso.toLinearMap g s

theorem cohomologyIso_smul (t : ℚ)
    (v : RationalSingularCohomology twelvePointHodgeData.analytification 0) :
    twelvePointCohomologyIso (t • v) = t • twelvePointCohomologyIso v :=
  map_smul twelvePointCohomologyIso.toLinearMap t v

theorem cohomologyIso_zero :
    twelvePointCohomologyIso (0 :
      RationalSingularCohomology twelvePointHodgeData.analytification 0) = 0 :=
  map_zero twelvePointCohomologyIso.toLinearMap

/-- Additivity of the cohomology iso through its linear-map structure. -/
theorem cohomologyIso_add (v w : RationalSingularCohomology
      twelvePointHodgeData.analytification 0) :
    twelvePointCohomologyIso (v + w) =
      twelvePointCohomologyIso v + twelvePointCohomologyIso w :=
  map_add twelvePointCohomologyIso.toLinearMap v w

/-- The word operator acts on point classes by the letter data matrix. -/
theorem wordOp_pointClass (L : List (Fin 12 × Fin 12 × ℚ)) (i : Fin 12) :
    twelvePointCohomologyIso ((realizedWordPair (lettersOf L)).cohomologyOperator
        (zeroCycleClass (codimensionPointCycle twelvePointWorld.X 0
          (twelvePointPt i)))) =
      fun j => (L.map
        (fun d => if d.2.1 = i then (if j = d.1 then d.2.2 else 0) else 0)).sum := by
  induction L with
  | nil =>
    simp only [lettersOf, List.map_nil, List.sum_nil]
    show twelvePointCohomologyIso
        ((0 : RationalSingularCohomology
            twelvePointHodgeData.analytification 0 →ₗ[ℚ] _)
          (zeroCycleClass (codimensionPointCycle twelvePointWorld.X 0
            (twelvePointPt i)))) = _
    rw [LinearMap.zero_apply, cohomologyIso_zero]
    rfl
  | cons d L ih =>
    have hword : lettersOf (d :: L) =
        (d.2.2, pointPairLetter d.1 d.2.1) :: lettersOf L := rfl
    rw [hword, realizedWordPair_cohomologyOperator_cons]
    rw [LinearMap.add_apply, LinearMap.smul_apply] -- AUDIT-8: apply lemmas
    rw [cohomologyIso_add, cohomologyIso_smul]
    rw [show (pointPairLetter d.1 d.2.1).cohomologyOperator =
      matrixUnitOp d.1 d.2.1 from rfl]
    rw [matrixUnitOp_pointClass]
    rw [ih]
    funext j
    simp only [List.map_cons, List.sum_cons]
    by_cases hd : d.2.1 = i
    · by_cases hj : j = d.1 <;>
        simp [hd, hj, Pi.single_apply, Pi.smul_apply, smul_eq_mul]
    · by_cases hj : j = d.1 <;>
        simp [hd, hj, Pi.single_apply, Pi.smul_apply, smul_eq_mul]

/-- On point classes, the fold word operator is the fold matrix column. -/
theorem foldWord_op_pointClass (c : Fin 12) :
    twelvePointCohomologyIso ((realizedWordPair twelvePointFoldWord).cohomologyOperator
        (zeroCycleClass (codimensionPointCycle twelvePointWorld.X 0
          (twelvePointPt c)))) =
      fun j => twelvePointFoldMatrix j c := by
  rw [show realizedWordPair twelvePointFoldWord
      = realizedWordPair (lettersOf foldWordData) from rfl]
  rw [wordOp_pointClass foldWordData c]
  funext j
  -- AUDIT (guard orientation): the word lemma's inner guard is `j = d.1`,
  -- the fold matrix's is `d.1 = j`; `eq_comm` normalizes both sides.
  simp only [twelvePointFoldMatrix, eq_comm]

/-- Every H⁰ class is the sum of its coordinates times point classes. -/
theorem module_decomp (u : RationalSingularCohomology
    twelvePointHodgeData.analytification 0) :
    u = ∑ k : Fin 12, (twelvePointCohomologyIso u k) •
      (zeroCycleClass (codimensionPointCycle twelvePointWorld.X 0
        (twelvePointPt k))) := by
  have hsum : twelvePointCohomologyIso
      (∑ k : Fin 12, (twelvePointCohomologyIso u k) •
        (zeroCycleClass (codimensionPointCycle twelvePointWorld.X 0
          (twelvePointPt k)))) = twelvePointCohomologyIso u := by
    rw [cohomologyIso_sum]
    simp only [cohomologyIso_smul]
    simp only [zeroCycleClass_point] -- AUDIT-6: contract lemma rewriting
    funext j
    rw [Finset.sum_apply] -- AUDIT-8
    simp [Pi.single_apply]
  calc u = twelvePointCohomologyIso.symm (twelvePointCohomologyIso u) :=
        (LinearEquiv.symm_apply_apply _ _).symm
    _ = twelvePointCohomologyIso.symm (twelvePointCohomologyIso
          (∑ k : Fin 12, (twelvePointCohomologyIso u k) •
            (zeroCycleClass (codimensionPointCycle twelvePointWorld.X 0
              (twelvePointPt k))))) := by rw [hsum]
    _ = ∑ k : Fin 12, (twelvePointCohomologyIso u k) •
          (zeroCycleClass (codimensionPointCycle twelvePointWorld.X 0
            (twelvePointPt k))) := LinearEquiv.symm_apply_apply _ _

/-- **THE OPERATOR THEOREM**: under the H⁰ cohomology iso, the fold word's
cohomology operator IS the fold matrix. -/
theorem twelvePointFoldWord_op (u : RationalSingularCohomology
    twelvePointHodgeData.analytification 0) :
    twelvePointCohomologyIso
        ((realizedWordPair twelvePointFoldWord).cohomologyOperator u) =
      twelvePointFoldMatrix.mulVec (twelvePointCohomologyIso u) := by
  rw [module_decomp u]
  rw [map_sum]
  simp only [map_smul]
  simp only [foldWord_op_pointClass]
  funext j
  rw [Finset.sum_apply]
  simp [Matrix.mulVec, dotProduct, mul_comm] -- AUDIT-8: matrix API

/-- The fold word preserves the rational Hodge fiber at weight zero (the
fiber is maximal on the twelve-point world). -/
theorem twelvePointFoldWord_hodge
    (alpha : ClassicalHodgeFiber twelvePointWorld twelvePointHodgeData 0) :
    (realizedWordPair twelvePointFoldWord).cohomologyOperator alpha.1 ∈
      rationalHodgeSubspace (twelvePointHodgeData.hodgeBigrading 0) := by
  have htop : rationalHodgeSubspace
      (twelvePointHodgeData.hodgeBigrading 0) = ⊤ :=
    zeroFiber_eq_top -- AUDIT-6: contract lemma (`ClassicalHodgeFiber` is the
  -- `rationalHodgeSubspace` abbreviation at weight zero)
  rw [htop]
  exact Submodule.mem_top _

#check twelvePointFoldWord
#check twelvePointFoldMatrix
#check twelvePointFoldWord_op
#check twelvePointFoldWord_hodge

end GSTTwelvePointFoldWord

end -- noncomputable section
