import GSTTwelvePointAnalytification
import GSTGeometricRealizationStage2F

/-!
# GST TWELVE-POINT COHOMOLOGY

The rational singular cohomology of the twelve-point discrete world, computed
from Mathlib's genuine singular cochain machinery rather than postulated:

  `RationalSingularCohomology twelvePointAnalytification 0 ≃ₗ[ℚ] (Fin 12 → ℚ)`

with vanishing in every nonzero degree.  The computation runs through the
pinned Mathlib isomorphism `singularChainComplexFunctorIsoOfTotallyDisconnectedSpace`
(identifying the singular chain complex of a totally disconnected space with
`ChainComplex.alternatingConst.obj (∐ fun _ : X ↦ R)`), followed by the
corpus-verified linear-Yoneda dualization of that chain isomorphism, and a
direct computation of the resulting alternating dual cochain complex
(differential pattern `0, 𝟙, 0, 𝟙, ...`).

Steps flagged `-- AUDIT(n):` rest on pinned-Mathlib lemma names that could not
be byte-verified against the local partial checkout (no `Mathlib/CategoryTheory`
or `Mathlib/Algebra/Homology` source available here); they are the designated
repair points if CI reports a name mismatch.  No `sorry`, no fake axioms.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicTopology
open GSTGeometricRealizationStage2F
-- AUDIT(1): the upstream W4-B module is assumed to follow the campaign
-- module-matching namespace convention, and
-- `twelvePointAnalytification.space` is assumed definitionally equal to the
-- contract constant `twelvePointSpace` (with `↥twelvePointSpace ≡ Fin 12`).
open GSTTwelvePointAnalytification

namespace GSTTwelvePointCohomology

/-! ## §1. The linear-Yoneda dualization machinery (corpus-verified pattern) -/

section Dualization

variable {K L : ChainComplex (ModuleCat ℚ) ℕ}

/-- Contravariant cochain dual of a chain map, with exactly the corpus
construction (`GSTClassicalHodgeAmbientBettiSelfProduct`). -/
noncomputable def dualChainHom (f : K ⟶ L) :
    L.linearYonedaObj ℚ rationalCoefficient ⟶
      K.linearYonedaObj ℚ rationalCoefficient :=
  (HomologicalComplex.unopFunctor (ModuleCat ℚ) (ComplexShape.down ℕ)).map
    (Quiver.Hom.op
      ((((CategoryTheory.linearYoneda ℚ (ModuleCat ℚ)).obj rationalCoefficient).rightOp
        |>.mapHomologicalComplex (ComplexShape.down ℕ)).map
        (f)))

/-- The cochain dual isomorphism of a chain isomorphism.  Both iso laws are
proved with the same op-arithmetic `rfl` steps the corpus used for
`swapCohomology_involutive`. -/
noncomputable def dualChainIso (e : K ≅ L) :
    K.linearYonedaObj ℚ rationalCoefficient ≅
      L.linearYonedaObj ℚ rationalCoefficient where
  hom := dualChainHom e.inv
  inv := dualChainHom e.hom
  hom_inv_id := by
    let F := (HomologicalComplex.unopFunctor (ModuleCat ℚ) (ComplexShape.down ℕ))
    let G := (((CategoryTheory.linearYoneda ℚ (ModuleCat ℚ)).obj rationalCoefficient).rightOp
      |>.mapHomologicalComplex (ComplexShape.down ℕ))
    change F.map (Quiver.Hom.op (G.map e.inv)) ≫
      F.map (Quiver.Hom.op (G.map e.hom)) = 𝟙 _
    rw [← F.map_comp,
      show (G.map e.inv).op ≫ (G.map e.hom).op
          = (G.map e.hom ≫ G.map e.inv).op from rfl,
      ← G.map_comp, e.hom_inv_id, G.map_id,
      show (𝟙 (G.obj L)).op = 𝟙 (Opposite.op (G.obj L)) from rfl,
      F.map_id]
  inv_hom_id := by
    let F := (HomologicalComplex.unopFunctor (ModuleCat ℚ) (ComplexShape.down ℕ))
    let G := (((CategoryTheory.linearYoneda ℚ (ModuleCat ℚ)).obj rationalCoefficient).rightOp
      |>.mapHomologicalComplex (ComplexShape.down ℕ))
    change F.map (Quiver.Hom.op (G.map e.hom)) ≫
      F.map (Quiver.Hom.op (G.map e.inv)) = 𝟙 _
    rw [← F.map_comp,
      show (G.map e.hom).op ≫ (G.map e.inv).op
          = (G.map e.inv ≫ G.map e.hom).op from rfl,
      ← G.map_comp, e.inv_hom_id, G.map_id,
      show (𝟙 (G.obj K)).op = 𝟙 (Opposite.op (G.obj K)) from rfl,
      F.map_id]

/-- Homology transport along an isomorphism of cochain complexes, via the
corpus-verified `homologyMap_comp` / `homologyMap_id` lemmas. -/
noncomputable def homologyIsoOfIso {C D : CochainComplex (ModuleCat ℚ) ℕ}
    (e : C ≅ D) (n : ℕ) : C.homology n ≅ D.homology n where
  hom := HomologicalComplex.homologyMap e.hom n
  inv := HomologicalComplex.homologyMap e.inv n
  hom_inv_id := by
    have h : HomologicalComplex.homologyMap e.hom n ≫
        HomologicalComplex.homologyMap e.inv n =
        HomologicalComplex.homologyMap (e.hom ≫ e.inv) n := by
      rw [HomologicalComplex.homologyMap_comp]
    rw [h, e.hom_inv_id, HomologicalComplex.homologyMap_id]
  inv_hom_id := by
    have h : HomologicalComplex.homologyMap e.inv n ≫
        HomologicalComplex.homologyMap e.hom n =
        HomologicalComplex.homologyMap (e.inv ≫ e.hom) n := by
      rw [HomologicalComplex.homologyMap_comp]
    rw [h, e.inv_hom_id, HomologicalComplex.homologyMap_id]

end Dualization

/-! ## §2. The twelve-point chain complex and its alternating form -/

/-- The coproduct of twelve copies of the rational coefficient object. -/
noncomputable def twelvePointE : ModuleCat ℚ :=
  ∐ fun _ : ↥twelvePointSpace ↦ rationalCoefficient

/-- Mathlib's pinned isomorphism: the singular chain complex of the totally
disconnected twelve-point space is the alternating constant complex on
`twelvePointE`. -/
noncomputable def twelvePointChainIso :
    rationalSingularChains twelvePointAnalytification ≅
      ChainComplex.alternatingConst.obj twelvePointE :=
  singularChainComplexFunctorIsoOfTotallyDisconnectedSpace (ModuleCat ℚ)
    rationalCoefficient twelvePointSpace

/-- The dual alternating cochain complex of the twelve-point world. -/
noncomputable def twelvePointDualCochains : CochainComplex (ModuleCat ℚ) ℕ :=
  (ChainComplex.alternatingConst.obj twelvePointE).linearYonedaObj
    ℚ rationalCoefficient

/-- The corpus definition unfolds definitionally to the linear-Yoneda dual. -/
theorem rationalSingularCochains_eq :
    rationalSingularCochains twelvePointAnalytification =
      (rationalSingularChains twelvePointAnalytification).linearYonedaObj
        ℚ rationalCoefficient := rfl

/-- The dualized chain isomorphism. -/
noncomputable def twelvePointDualIso :
    rationalSingularCochains twelvePointAnalytification ≅
      twelvePointDualCochains :=
  dualChainIso twelvePointChainIso

/-! ## §3. The alternating differential pattern -/

/-- The alternating constant complex has `d (2*k+1) (2*k) = 0`.
-- AUDIT(2): pinned `alternatingConst_obj_d` simps lemma and branch shape. -/
theorem altChain_d_odd (k : ℕ) :
    (ChainComplex.alternatingConst.obj twelvePointE).d (2*k+1) (2*k) = 0 := by
  have heven : ¬ Even (2*k+1) := by
    rw [Nat.even_iff]
    omega
  simp only [ChainComplex.alternatingConst_obj, HomologicalComplex.alternatingConst_d]
  split_ifs with hij hi
  · exact absurd hi heven
  · rfl
  · rfl

/-- The alternating constant complex has `d (2*k+2) (2*k+1) = 𝟙`.
-- AUDIT(2): pinned `alternatingConst_obj_d` simps lemma and branch shape. -/
theorem altChain_d_even (k : ℕ) :
    (ChainComplex.alternatingConst.obj twelvePointE).d (2*k+2) (2*k+1) =
      𝟙 twelvePointE := by
  have heven : Even (2*k+2) := ⟨k+1, by omega⟩
  simp only [ChainComplex.alternatingConst_obj, HomologicalComplex.alternatingConst_d]
  split_ifs with hij hi
  · rfl
  · exact absurd heven hi
  · exact absurd (rfl : (ComplexShape.down ℕ).Rel (2*k+2) (2*k+1)) hij

/-- The dual differential on even indices is zero.
-- AUDIT(3): pinned `linearYonedaObj_d` simps lemma, `Linear.leftComp_apply`,
-- and module hom extensionality. -/
theorem dualCochains_d_even (k : ℕ) :
    twelvePointDualCochains.d (2*k) (2*k+1) = 0 := by
  ext g
  unfold twelvePointDualCochains
  rw [ChainComplex.linearYonedaObj_d]
  rw [altChain_d_odd k]
  simp [Linear.leftComp_apply, zero_comp]

/-- The dual differential on odd indices is the identity.
-- AUDIT(3): pinned `linearYonedaObj_d` simps lemma, `Linear.leftComp_apply`,
-- and module hom extensionality. -/
theorem dualCochains_d_odd (k : ℕ) :
    twelvePointDualCochains.d (2*k+1) (2*k+2) =
      𝟙 (twelvePointDualCochains.X (2*k+1)) := by
  ext g
  unfold twelvePointDualCochains
  rw [ChainComplex.linearYonedaObj_d]
  rw [altChain_d_even k]
  simp [Linear.leftComp_apply, id_comp]

/-- Degree zero differential of the dual complex. -/
theorem dualCochains_d_zero_one : twelvePointDualCochains.d 0 1 = 0 :=
  dualCochains_d_even 0

/-! ## §4. The zeroth homology of the dual alternating complex -/

-- AUDIT(4): cochain shape facts for `up ℕ` at index zero.
theorem upNext_zero : (ComplexShape.up ℕ).next 0 = 1 := by
  exact CochainComplex.next ℕ 0

theorem upPrev_zero : (ComplexShape.up ℕ).prev 0 = 0 := by
  exact CochainComplex.prev_nat_zero

theorem upNotRel_zero_zero : ¬ (ComplexShape.up ℕ).Rel 0 0 := by
  simp [ComplexShape.up_Rel]

/-- The shape zero differential. -/
theorem dualCochains_d_zero_zero : twelvePointDualCochains.d 0 0 = 0 :=
  twelvePointDualCochains.shape 0 0 upNotRel_zero_zero

/-- The zeroth homology of the dual alternating complex is its degree-zero
term. -- AUDIT(5): `isoHomologyι` / `pOpcyclesIso` names and argument shapes. -/
noncomputable def twelvePointHomologyZero :
    twelvePointDualCochains.homology 0 ≅ twelvePointDualCochains.X 0 :=
  twelvePointDualCochains.isoHomologyι upNext_zero dualCochains_d_zero_one ≪≫
    (twelvePointDualCochains.pOpcyclesIso upPrev_zero
      dualCochains_d_zero_zero).symm

/-! ## §5. The object-level identification with `Fin 12 → ℚ` -/

/-- The coproduct of twelve rational coefficients is the function space.
-- AUDIT(6): `biproduct.isoCoproduct` / `ModuleCat.biproductIsoPi` names; also
-- relies on the upstream defeq `↥twelvePointSpace ≡ Fin 12`. -/
noncomputable def twelvePointEIso :
    twelvePointE ≅ ModuleCat.of ℚ (Fin 12 → ℚ) :=
  (Limits.biproduct.isoCoproduct
      (fun _ : Fin 12 ↦ ModuleCat.of ℚ ℚ)).symm ≪≫
    ModuleCat.biproductIsoPi (fun _ : Fin 12 ↦ ModuleCat.of ℚ ℚ)

/-- The canonical coordinate identification of the dual of `Fin 12 → ℚ`:
a functional is its list of values on the standard single-point vectors.
-- AUDIT(7): the `Pi.single` / `Finset.sum_ite` simp set. -/
noncomputable def fin12DualEquiv :
    ((Fin 12 → ℚ) →ₗ[ℚ] ℚ) ≃ₗ[ℚ] (Fin 12 → ℚ) where
  toFun φ := fun i => φ (Pi.single i 1)
  map_add' φ ψ := by funext i; simp
  map_smul' r φ := by funext i; simp
  invFun c :=
    ⟨fun x => ∑ i, c i * x i,
      by
        intro x y
        simp [Pi.add_apply, mul_add, Finset.sum_add_distrib,
          add_mul, Finset.sum_mul],
      by
        intro r x
        simp [Pi.smul_apply, smul_eq_mul, mul_comm, mul_assoc,
          mul_left_comm, Finset.sum_mul]⟩
  left_inv φ := by
    ext x
    have hx : x = ∑ i, x i • (Pi.single i 1 : Fin 12 → ℚ) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply, Pi.smul_apply,
        smul_eq_mul, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']
    show ∑ i, φ (Pi.single i 1 : Fin 12 → ℚ) * x i = φ x
    calc ∑ i, φ (Pi.single i 1 : Fin 12 → ℚ) * x i
        = ∑ i, x i * φ (Pi.single i 1 : Fin 12 → ℚ) :=
            Finset.sum_congr rfl (fun i _ => mul_comm _ _)
      _ = ∑ i, φ (x i • (Pi.single i 1 : Fin 12 → ℚ)) := by
            simp [map_smul, smul_eq_mul]
      _ = φ (∑ i, x i • (Pi.single i 1 : Fin 12 → ℚ)) :=
            (map_sum φ
              (fun i => x i • (Pi.single i 1 : Fin 12 → ℚ))
              Finset.univ).symm
      _ = φ x := by rw [hx]
  right_inv c := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply, Finset.sum_ite_eq,
      Finset.sum_ite_eq']

/-- The degree-zero term of the dual complex, i.e. the internal Hom from
`twelvePointE`, as the function space `Fin 12 → ℚ`. -- AUDIT(8):
`Linear.homCongr`, `LinearEquiv.toModuleIso`, and the defeq
`twelvePointDualCochains.X 0 ≡ ModuleCat.of ℚ (E ⟶ R)`. -/
noncomputable def twelvePointXZeroIso :
    twelvePointDualCochains.X 0 ≅ ModuleCat.of ℚ (Fin 12 → ℚ) :=
  LinearEquiv.toModuleIso
    (CategoryTheory.Linear.homCongr ℚ twelvePointEIso
        (Iso.refl rationalCoefficient) |>.trans fin12DualEquiv)

/-! ## §6. Assembly: the degree-zero rational cohomology -/

/-- The full module-level isomorphism. -/
noncomputable def twelvePointCohomologyZeroObj :
    rationalSingularCohomologyObj twelvePointAnalytification 0 ≅
      ModuleCat.of ℚ (Fin 12 → ℚ) :=
  homologyIsoOfIso twelvePointDualIso 0 ≪≫
    twelvePointHomologyZero ≪≫ twelvePointXZeroIso

/-- **THE TARGET**: the zeroth rational singular cohomology of the twelve-point
world is the rational function space on twelve points. -- AUDIT(9):
`Iso.toLinearEquiv` name. -/
noncomputable def twelvePointCohomologyIso :
    RationalSingularCohomology twelvePointAnalytification 0 ≃ₗ[ℚ]
      (Fin 12 → ℚ) :=
  twelvePointCohomologyZeroObj.toLinearEquiv

/-! ## §7. Vanishing in nonzero degree -/

/-- Exactness of the dual alternating short complex at an odd index.
-- AUDIT(10): `ShortComplex.ModuleCat.exact_iff`, the `sc` field simps lemmas,
-- and the `up` shape simp lemmas are the three pinned bridges. -/
theorem dualSc_exact_odd (k : ℕ) :
    ShortComplex.Exact (twelvePointDualCochains.sc (2*k+1)) := by
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  simp only [HomologicalComplex.shortComplexFunctor_obj_f,
    HomologicalComplex.shortComplexFunctor_obj_g]
  have hprev : (ComplexShape.up ℕ).prev (2*k+1) = 2*k :=
    CochainComplex.prev_nat_succ (2*k)
  have hnext : (ComplexShape.up ℕ).next (2*k+1) = 2*k+2 :=
    CochainComplex.next ℕ (2*k+1)
  rw [hprev, hnext, dualCochains_d_even k, dualCochains_d_odd k]
  simp [LinearMap.ker_id, LinearMap.range_zero]

/-- Exactness of the dual alternating short complex at a positive even index.
-- AUDIT(10): same three pinned bridges as `dualSc_exact_odd`. -/
theorem dualSc_exact_even (k : ℕ) :
    ShortComplex.Exact (twelvePointDualCochains.sc (2*k+2)) := by
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  simp only [HomologicalComplex.shortComplexFunctor_obj_f,
    HomologicalComplex.shortComplexFunctor_obj_g]
  have hprev : (ComplexShape.up ℕ).prev (2*k+2) = 2*k+1 :=
    CochainComplex.prev_nat_succ (2*k+1)
  have hnext : (ComplexShape.up ℕ).next (2*k+2) = 2*k+3 :=
    CochainComplex.next ℕ (2*k+2)
  have hg : twelvePointDualCochains.d (2*k+2) (2*k+3) = 0 :=
    dualCochains_d_even (k+1)
  rw [hprev, hnext, dualCochains_d_odd k, hg]
  simp [LinearMap.ker_zero, LinearMap.range_id]

/-- Parity splitting of nonzero naturals. -/
theorem parity_split (n : ℕ) (hn : n ≠ 0) :
    (∃ k, n = 2*k + 1) ∨ (∃ k, n = 2*k + 2) := by omega

/-- The dual alternating complex is exact in every positive degree.
-- AUDIT(11): `ExactAt n` is definitionally `(C.sc n).Exact` in pinned
-- Mathlib (it is consumed there via `.of_iso` / `.isZero_homology` in
-- `Mathlib/AlgebraicTopology/SingularHomology/Basic.lean`). -/
theorem twelvePointDualCochains_exactAt (n : ℕ) (hn : n ≠ 0) :
    twelvePointDualCochains.ExactAt n := by
  show ShortComplex.Exact (twelvePointDualCochains.sc n)
  rcases parity_split n hn with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [hk]; exact dualSc_exact_odd k
  · rw [hk]; exact dualSc_exact_even k

/-- The dual alternating cohomology objects vanish in positive degree.
`ExactAt.isZero_homology` is the name verified in the pinned
`SingularHomology/Basic.lean` (line 131). -/
theorem twelvePointDualCochomology_isZero (n : ℕ) (hn : n ≠ 0) :
    IsZero (twelvePointDualCochains.homology n) :=
  (twelvePointDualCochains_exactAt n hn).isZero_homology

/-- **THE VANISHING TARGET**: rational singular cohomology of the twelve-point
world is trivial in every nonzero degree. -- AUDIT(12): `IsZero.eq`. -/
theorem twelvePointCohomology_subsingleton (n : ℕ) (hn : n ≠ 0) :
    Subsingleton (RationalSingularCohomology twelvePointAnalytification n) := by
  let e := (homologyIsoOfIso twelvePointDualIso n).toLinearEquiv
  have hD : IsZero (twelvePointDualCochains.homology n) :=
    twelvePointDualCochomology_isZero n hn
  refine ⟨fun a b => ?_⟩
  calc a = e.symm (e a) := (e.symm_apply_apply a).symm
    _ = e.symm (e b) := by
      congr 1
      haveI : Subsingleton (twelvePointDualCochains.homology n) :=
        ModuleCat.subsingleton_of_isZero hD
      exact Subsingleton.elim (e a) (e b)
    _ = b := e.symm_apply_apply b

end GSTTwelvePointCohomology

#check GSTTwelvePointCohomology.twelvePointCohomologyIso
#check GSTTwelvePointCohomology.twelvePointCohomology_subsingleton

#print axioms GSTTwelvePointCohomology.twelvePointCohomologyIso
#print axioms GSTTwelvePointCohomology.twelvePointCohomology_subsingleton
