import HamSandwich.SphereOddDegree.AlgebraicTopology.SphereHomologyMVStepQ
import HamSandwich.SphereOddDegree.AlgebraicTopology.SphereHomologyS1BaseMV
import HamSandwich.SphereOddDegree.AlgebraicTopology.SingularH0Q
import HamSandwich.SphereOddDegree.AlgebraicTopology.MayerVietoris
import Mathlib

/-!
# Mayer–Vietoris base case at ℚ: `H₁(S¹; ℚ) ≅ ℚ`

The ℚ duplication of `SphereHomologyS1BaseMV.lean`, supplying the `base` field
of `SphereSuspensionTowerQ`.  The cover (`circleTop`, `circU`, `circV`,
`circBand`, `circUV_top`) and the two-point-sphere helpers
(`instNonemptySphere0`, `sphere0_equiv_fin2`) are coefficient-free and are
*reused* from the vendored file.

Around degree `1` the rational Mayer–Vietoris sequence of the two-punctured
cover of `S¹` reads
`H₁(U; ℚ) ⊕ H₁(V; ℚ) → H₁(S¹; ℚ) → H₀(U ∩ V; ℚ) → H₀(U; ℚ) ⊕ H₀(V; ℚ)`;
the left term vanishes (contractibility at ℚ), so the connecting map identifies
`H₁(S¹; ℚ) ≅ ker(H₀(U ∩ V; ℚ) → H₀(U; ℚ) ⊕ H₀(V; ℚ))` (`sphereH1_iso_kerF0Q`),
that kernel coincides with the kernel of the rational band augmentation
(`kerF0_iso_kerBandQ`), and the latter is `ℚ` (`kerBand_isoQ`) via the homotopy
equivalence `U ∩ V ≃ S⁰` and the reduced-`H₀` computation of `S⁰` at ℚ
(`reducedH0_sphere0_isoQ`).

The finrank helpers of the ℤ original
(`linearEquiv_int_of_finrank_one` / `ker_linearEquiv_int_of_finrank_two`) are
ℤ-specific (`Module.finBasis ℤ`, the ℤ-module instance diamond on `↥(ker _)`);
over the field `ℚ` the replacement `ker_linearEquiv_rat_of_finrank_two` uses
`Submodule.finrank_quotient_add_finrank` and `LinearEquiv.ofFinrankEq` — no
diamond exists at a field.
-/

set_option maxHeartbeats 8000000

open CategoryTheory AlgebraicTopology Limits TopologicalSpace
open SphereOddDegree.AffineBarycentricSubdivision

noncomputable section
namespace SphereOddDegree

/-! ## The rational MV left map on `H₀` -/

/-- The Mayer–Vietoris left map on rational `H₀`,
`H₀(U ∩ V; ℚ) → H₀(U; ℚ) ⊕ H₀(V; ℚ)`.  (Mirror of `circF0`.) -/
abbrev circF0Q :
    (subChainComplex ℚ circleTop circBand).homology 0 ⟶
      ((mvShortComplex ℚ circU circV circUV_top).X₂).homology 0 :=
  HomologicalComplex.homologyMap (mvShortComplex ℚ circU circV circUV_top).f 0

/-! ## Field-flavored finrank helpers -/

/-- **Algebra helper at ℚ.** The kernel of a surjection from a rank-`2`
finite-dimensional ℚ-vector space onto `ℚ` is isomorphic to `ℚ`.  (Field
replacement for the ℤ-specific `ker_linearEquiv_int_of_finrank_two`: over a
field there is no module-instance diamond, and
`Submodule.finrank_quotient_add_finrank` +
`LinearMap.quotKerEquivOfSurjective` compute the rank of the kernel directly.) -/
theorem ker_linearEquiv_rat_of_finrank_two {M : Type} [AddCommGroup M] [Module ℚ M]
    [Module.Finite ℚ M] (hM : Module.finrank ℚ M = 2)
    (g : M →ₗ[ℚ] ℚ) (hg : Function.Surjective g) :
    Nonempty (↥(LinearMap.ker g) ≃ₗ[ℚ] ℚ) := by
  have key : Module.finrank ℚ ↥(LinearMap.ker g) = 1 := by
    have h1 := Submodule.finrank_quotient_add_finrank (LinearMap.ker g)
    have hq := (g.quotKerEquivOfSurjective hg).finrank_eq
    rw [Module.finrank_self] at hq
    rw [hq, hM] at h1
    omega
  exact ⟨LinearEquiv.ofFinrankEq _ _ (by rw [key, Module.finrank_self])⟩

/-! ## Reduced `H₀(S⁰; ℚ) ≅ ℚ` -/

/-- **`H₀(S⁰; ℚ)` is a finite-dimensional ℚ-vector space of rank `2`.**
(Mirror of the `Finite`/finrank components of `h0_sphere0_free_finrank`; the
`Module.Free` component is automatic over the field `ℚ`.) -/
theorem h0_sphere0Q_finite_finrank :
    Module.Finite ℚ ((singularChainComplex ℚ (TopCat.of (Sphere 0))).homology 0) ∧
    Module.finrank ℚ ((singularChainComplex ℚ (TopCat.of (Sphere 0))).homology 0) = 2 := by
  constructor
  · have := AlgebraicTopology.singularHomologyFunctorZeroOfTotallyDisconnectedSpace ( ModuleCat ℚ ) ( ModuleCat.of ℚ ℚ ) ( TopCat.of ( Sphere 0 ) );
    have := this.toLinearEquiv;
    convert Module.Finite.of_surjective this.symm.toLinearMap this.symm.surjective;
  · obtain ⟨ e ⟩ := sphere0_equiv_fin2;
    have h_iso : (singularChainComplex ℚ (TopCat.of (Sphere 0))).homology 0 ≅ ModuleCat.of ℚ (DirectSum (Sphere 0) (fun _ => ℚ)) := by
      convert singularHomologyFunctorZeroOfTotallyDisconnectedSpace ( ModuleCat ℚ ) ( ModuleCat.of ℚ ℚ ) ( TopCat.of ( Sphere 0 ) ) |> CategoryTheory.Iso.trans <| ModuleCat.coprodIsoDirectSum _;
    convert LinearEquiv.finrank_eq ( h_iso.toLinearEquiv ) using 1;
    simp +decide [ Module.finrank ];
    rw [ Cardinal.mk_congr e ] ; norm_num

/-- **Reduced zeroth rational homology of `S⁰`.** The kernel of the rational
augmentation `H₀(S⁰; ℚ) → ℚ` is isomorphic to `ℚ`.  (Mirror of
`reducedH0_sphere0_iso`; over the field `ℚ` the ℤ-original's
`Subsingleton.elim` instance-diamond fix is unnecessary.) -/
theorem reducedH0_sphere0_isoQ :
    Nonempty (kernel (H0augQ (TopCat.of (Sphere 0))) ≅ ModuleCat.of ℚ ℚ) := by
  obtain ⟨hFin, hrank⟩ := h0_sphere0Q_finite_finrank
  haveI := hFin
  obtain ⟨e⟩ := ker_linearEquiv_rat_of_finrank_two hrank
    (ModuleCat.Hom.hom (H0augQ (TopCat.of (Sphere 0)))) (surjective_H0augQ _)
  apply Nonempty.intro
  refine' CategoryTheory.Iso.trans _ ( LinearEquiv.toModuleIso e )
  exact ModuleCat.kernelIsoKer _

/-! ## The kernel of the rational band augmentation is `ℚ` -/

/-- The kernel of the rational band augmentation `H₀(U ∩ V; ℚ) → ℚ` is
isomorphic to `ℚ`, using the homotopy equivalence `U ∩ V ≃ S⁰` and
`reducedH0_sphere0_isoQ`.  (Mirror of `kerBand_iso`.) -/
theorem kerBand_isoQ :
    Nonempty (kernel (subH0augQ circleTop circBand) ≅ ModuleCat.of ℚ ℚ) := by
  have hnat : (singularHomologyQ_isoOfHomotopyEquivSpace 0 (sphereBandHomotopyEquiv 0)).hom
      ≫ H0augQ (TopCat.of (Sphere 0)) = H0augQ (TopCat.of ↑(sphereBand 0)) :=
    H0augQ_natural (TopCat.ofHom (sphereBandHomotopyEquiv 0).toFun)
  refine ⟨?_⟩
  refine kernelIsIsoComp (subspaceHomologyIsoQ circleTop circBand 0).hom
    (H0augQ (TopCat.of circBand)) ≪≫ ?_
  refine kernelIsoOfEq hnat.symm ≪≫ ?_
  exact kernelIsIsoComp (singularHomologyQ_isoOfHomotopyEquivSpace 0 (sphereBandHomotopyEquiv 0)).hom
    (H0augQ (TopCat.of (Sphere 0))) ≪≫ reducedH0_sphere0_isoQ.some

/-! ## The Mayer–Vietoris kernel identity at ℚ -/

/-- The rational MV left map's first component is the inclusion
`U ∩ V ↪ U`.  (Mirror of `circF_comp_fst`.) -/
theorem circF0Q_comp_fst :
    (mvShortComplex ℚ circU circV circUV_top).f ≫ biprod.fst
      = mvInclUV_U ℚ circU circV := by
  convert biprod.lift_fst _ _ using 1

/-- The rational MV left map's second component is minus the inclusion
`U ∩ V ↪ V`.  (Mirror of `circF_comp_snd`.) -/
theorem circF0Q_comp_snd :
    (mvShortComplex ℚ circU circV circUV_top).f ≫ biprod.snd
      = -(mvInclUV_V ℚ circU circV) := by
  convert biprod.lift_snd _ _

/-- **Joint monomorphism of the rational homology biproduct projections.** An
element of `H₀(X₂; ℚ)` is zero iff both of its biproduct components vanish.
(Mirror of `biprod_homology_zero_iff`.) -/
theorem biprod_homology_zero_iffQ
    (y : ((mvShortComplex ℚ circU circV circUV_top).X₂).homology 0) :
    y = 0 ↔
      (HomologicalComplex.homologyMap (biprod.fst :
          (subChainComplex ℚ circleTop ↑circU ⊞ subChainComplex ℚ circleTop ↑circV) ⟶ _) 0) y = 0
        ∧ (HomologicalComplex.homologyMap (biprod.snd :
          (subChainComplex ℚ circleTop ↑circU ⊞ subChainComplex ℚ circleTop ↑circV) ⟶ _) 0) y = 0 := by
  constructor
  · rintro rfl; simp
  · rintro ⟨h1, h2⟩
    have htot :
        (biprod.fst : (subChainComplex ℚ circleTop (circU : Set circleTop)
            ⊞ subChainComplex ℚ circleTop (circV : Set circleTop)) ⟶ _) ≫ biprod.inl
          + (biprod.snd : _ ⟶ _) ≫ biprod.inr
          = 𝟙 (subChainComplex ℚ circleTop (circU : Set circleTop)
            ⊞ subChainComplex ℚ circleTop (circV : Set circleTop)) := biprod.total
    have hmap := congrArg (fun φ => HomologicalComplex.homologyMap φ 0) htot
    simp only [HomologicalComplex.homologyMap_add, HomologicalComplex.homologyMap_comp,
      HomologicalComplex.homologyMap_id] at hmap
    have hy := congrArg (fun ψ => ψ y) hmap
    simp only [ModuleCat.hom_add, ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.add_apply,
      LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq, h1, h2,
      map_zero, add_zero] at hy
    exact hy.symm

/-- **The rational Mayer–Vietoris kernel coincides with the reduced-`H₀`
kernel.** `ker(H₀(U ∩ V; ℚ) → H₀(U; ℚ) ⊕ H₀(V; ℚ)) ≅
ker(H₀(U ∩ V; ℚ) → ℚ)`.  (Mirror of `kerF0_iso_kerBand`.) -/
theorem kerF0_iso_kerBandQ :
    Nonempty (kernel circF0Q ≅ kernel (subH0augQ circleTop circBand)) := by
  haveI := isIso_subH0augQ circleTop (circU : Set circleTop)
  haveI := isIso_subH0augQ circleTop (circV : Set circleTop)
  have hUeq : HomologicalComplex.homologyMap (mvInclUV_U ℚ circU circV) 0
      ≫ subH0augQ circleTop (circU : Set circleTop) = subH0augQ circleTop circBand :=
    subH0augQ_natural_inclusion circleTop circBand (circU : Set circleTop) Set.inter_subset_left
  have hVeq : HomologicalComplex.homologyMap (mvInclUV_V ℚ circU circV) 0
      ≫ subH0augQ circleTop (circV : Set circleTop) = subH0augQ circleTop circBand :=
    subH0augQ_natural_inclusion circleTop circBand (circV : Set circleTop) Set.inter_subset_right
  have hfst : circF0Q ≫ HomologicalComplex.homologyMap
      (biprod.fst : (subChainComplex ℚ circleTop ↑circU ⊞ subChainComplex ℚ circleTop ↑circV) ⟶ _) 0
      = HomologicalComplex.homologyMap (mvInclUV_U ℚ circU circV) 0 := by
    rw [← HomologicalComplex.homologyMap_comp, circF0Q_comp_fst]
  have hsnd : circF0Q ≫ HomologicalComplex.homologyMap
      (biprod.snd : (subChainComplex ℚ circleTop ↑circU ⊞ subChainComplex ℚ circleTop ↑circV) ⟶ _) 0
      = -(HomologicalComplex.homologyMap (mvInclUV_V ℚ circU circV) 0) := by
    rw [← HomologicalComplex.homologyMap_comp, circF0Q_comp_snd, HomologicalComplex.homologyMap_neg]
  have hinjU : Function.Injective (ModuleCat.Hom.hom (subH0augQ circleTop (circU : Set circleTop))) :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  have hinjV : Function.Injective (ModuleCat.Hom.hom (subH0augQ circleTop (circV : Set circleTop))) :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  have hUx : ∀ z, (subH0augQ circleTop (circU : Set circleTop))
      ((HomologicalComplex.homologyMap (mvInclUV_U ℚ circU circV) 0) z)
      = subH0augQ circleTop circBand z := by
    intro z
    have h : (HomologicalComplex.homologyMap (mvInclUV_U ℚ circU circV) 0
        ≫ subH0augQ circleTop (circU : Set circleTop)) z = subH0augQ circleTop circBand z :=
      congrArg (fun ψ => ψ z) hUeq
    rwa [CategoryTheory.comp_apply] at h
  have hVx : ∀ z, (subH0augQ circleTop (circV : Set circleTop))
      ((HomologicalComplex.homologyMap (mvInclUV_V ℚ circU circV) 0) z)
      = subH0augQ circleTop circBand z := by
    intro z
    have h : (HomologicalComplex.homologyMap (mvInclUV_V ℚ circU circV) 0
        ≫ subH0augQ circleTop (circV : Set circleTop)) z = subH0augQ circleTop circBand z :=
      congrArg (fun ψ => ψ z) hVeq
    rwa [CategoryTheory.comp_apply] at h
  have hfx : ∀ z, (HomologicalComplex.homologyMap (biprod.fst :
      (subChainComplex ℚ circleTop ↑circU ⊞ subChainComplex ℚ circleTop ↑circV) ⟶ _) 0)
      (circF0Q z) = (HomologicalComplex.homologyMap (mvInclUV_U ℚ circU circV) 0) z := by
    intro z
    have h : (circF0Q ≫ HomologicalComplex.homologyMap (biprod.fst :
        (subChainComplex ℚ circleTop ↑circU ⊞ subChainComplex ℚ circleTop ↑circV) ⟶ _) 0) z
        = (HomologicalComplex.homologyMap (mvInclUV_U ℚ circU circV) 0) z :=
      congrArg (fun ψ => ψ z) hfst
    rwa [CategoryTheory.comp_apply] at h
  have hsx : ∀ z, (HomologicalComplex.homologyMap (biprod.snd :
      (subChainComplex ℚ circleTop ↑circU ⊞ subChainComplex ℚ circleTop ↑circV) ⟶ _) 0)
      (circF0Q z) = -((HomologicalComplex.homologyMap (mvInclUV_V ℚ circU circV) 0) z) := by
    intro z
    have h : (circF0Q ≫ HomologicalComplex.homologyMap (biprod.snd :
        (subChainComplex ℚ circleTop ↑circU ⊞ subChainComplex ℚ circleTop ↑circV) ⟶ _) 0) z
        = (-(HomologicalComplex.homologyMap (mvInclUV_V ℚ circU circV) 0)) z :=
      congrArg (fun ψ => ψ z) hsnd
    rw [CategoryTheory.comp_apply] at h
    refine h.trans ?_
    simp
  have hker : LinearMap.ker (ModuleCat.Hom.hom circF0Q)
      = LinearMap.ker (ModuleCat.Hom.hom (subH0augQ circleTop circBand)) := by
    apply le_antisymm
    · intro x hx
      rw [LinearMap.mem_ker] at hx ⊢
      have hcx : circF0Q x = 0 := hx
      show subH0augQ circleTop circBand x = 0
      rw [← hUx x, ← hfx x, hcx, map_zero, map_zero]
    · intro x hx
      rw [LinearMap.mem_ker] at hx ⊢
      have hbandx : subH0augQ circleTop circBand x = 0 := hx
      have hax : (HomologicalComplex.homologyMap (mvInclUV_U ℚ circU circV) 0) x = 0 := by
        apply hinjU; rw [map_zero, hUx x, hbandx]
      have hbx : (HomologicalComplex.homologyMap (mvInclUV_V ℚ circU circV) 0) x = 0 := by
        apply hinjV; rw [map_zero, hVx x, hbandx]
      show circF0Q x = 0
      refine (biprod_homology_zero_iffQ (circF0Q x)).mpr ⟨?_, ?_⟩
      · rw [hfx x, hax]
      · rw [hsx x, hbx, neg_zero]
  exact ⟨ModuleCat.kernelIsoKer circF0Q ≪≫ eqToIso (by rw [hker]) ≪≫
    (ModuleCat.kernelIsoKer (subH0augQ circleTop circBand)).symm⟩

/-! ## Assembling the rational Mayer–Vietoris connecting isomorphism -/

/-- `H₁(S¹; ℚ) ≅ ker(H₀(U ∩ V; ℚ) → H₀(U; ℚ) ⊕ H₀(V; ℚ))`, the connecting
isomorphism onto the kernel (the connecting map is mono since
`H₁(U; ℚ) ⊕ H₁(V; ℚ) = 0`, and its image is the kernel by exactness).
(Mirror of `sphereH1_iso_kerF0`.) -/
theorem sphereH1_iso_kerF0Q :
    Nonempty (sphereTopHomologyQ 1 ≅ kernel circF0Q) := by
  refine' ⟨ _ ⟩;
  refine' ( sphereModelHomologyIsoQ 1 1 ).trans _;
  convert ( smallChains_homologyIso ℚ ( TopCat.of ( Sphere 1 ) ) ( twoSetCover circU circV circUV_top ) 1 ).symm.trans _ using 1;
  have hδ_mono : Mono ( (mvShortExact ℚ circU circV circUV_top).δ 1 0 (by simp [ComplexShape.down_Rel]) ) := by
    have hδ_mono : IsZero ( (mvShortComplex ℚ circU circV circUV_top).X₂.homology 1 ) := by
      apply isZero_mvX₂_homology;
      · convert isZero_subChainComplex_homology_of_contractibleQ circleTop ( ↑circU ) 1 ( by norm_num ) using 1;
      · apply isZero_subChainComplex_homology_of_contractibleQ circleTop (lowerOpens 0) 1 (by norm_num);
    have := ( mvShortExact ℚ circU circV circUV_top ).homology_exact₃ 1 0 ( by simp [ ComplexShape.down_Rel ] );
    convert this.mono_g;
    simp +decide [ hδ_mono.eq_of_src ];
    exact Or.inl ( hδ_mono.eq_of_src _ _ );
  have := (mvShortExact ℚ circU circV circUV_top).homology_exact₁ 1 0 (by simp [ComplexShape.down_Rel]);
  convert this.fIsKernel.conePointUniqueUpToIso ( kernelIsKernel circF0Q ) using 1

/-! ## The base case -/

/-- **`H₁(S¹; ℚ) ≅ ℚ`** (as a `Nonempty` package). -/
theorem sphereTopHomologyQ_one_iso_nonempty :
    Nonempty (sphereTopHomologyQ 1 ≅ ModuleCat.of ℚ ℚ) :=
  ⟨(sphereH1_iso_kerF0Q).some ≪≫ (kerF0_iso_kerBandQ).some ≪≫ (kerBand_isoQ).some⟩

/-- **The base case of the rational sphere suspension tower:**
`H₁(S¹; ℚ) ≅ ℚ`. -/
def sphereTopHomologyIsoQ_one : SphereTopHomologyIsoQ 1 :=
  (sphereTopHomologyQ_one_iso_nonempty).some

end SphereOddDegree

/-! ## PORT NOTES (the commander's CI-repair map)

Seams adapted in this file (ℚ duplication of the S¹ base case):

1. **Reused coefficient-free carriers** from the vendored
   `SphereHomologyS1BaseMV.lean` / `SphereHomologyMVStep.lean`:
   `circleTop`, `circU`, `circV`, `circUV_top`, `circBand`,
   `instNonemptySphere0`, `sphere0_equiv_fin2`, `sphereBand`,
   `sphereBandHomotopyEquiv`, `lowerOpens`, `contractible_upperOpens` /
   `contractible_lowerOpens` instances.
2. **Finrank helpers replaced.** `linearEquiv_int_of_finrank_one` and
   `ker_linearEquiv_int_of_finrank_two` (ℤ-specific: `Module.finBasis ℤ`, and
   the `Subsingleton.elim` fix for the ℤ-module diamond `Submodule.module` vs
   `AddCommGroup.toIntModule` on `↥(ker _)`) are replaced by the single field
   helper `ker_linearEquiv_rat_of_finrank_two`, proved with
   `Submodule.finrank_quotient_add_finrank` (valid at any
   `[HasRankNullity R]`, instance `DivisionRing.hasRankNullity` at `ℚ`) +
   `LinearMap.quotKerEquivOfSurjective.finrank_eq` + `omega`, and
   `LinearEquiv.ofFinrankEq` (needs `Module.Finite ℚ` on both sides: the
   hypothesis for `M`, `Module.Finite.self` for `ℚ`; `Module.Free ℚ` is the
   automatic `Module.Free.of_divisionRing`).  `Module.Finite ℚ ↥(ker _)` is
   found by TC via `FiniteDimensional.finiteDimensional_submodule`.
3. `h0_sphere0Q_finite_finrank` drops the ℤ `Module.Free` component (automatic
   at a field); the `Module.Finite` and finrank bullets are verbatim mirrors of
   `h0_sphere0_free_finrank` at `ModuleCat ℚ / ModuleCat.of ℚ ℚ`.
4. `reducedH0_sphere0_isoQ` drops the ℤ `Subsingleton.elim _ _` diamond fix
   (no ℤ-module diamond exists at `ℚ`); if CI still reports an instance
   mismatch between `ModuleCat.kernelIsoKer`'s codomain and
   `LinearEquiv.toModuleIso`'s domain, insert the ℤ original's
   `convert ModuleCat.kernelIsoKer _; exact …` shape with an `eqToIso` bridge.
5. All MV machinery (`mvShortComplex ℚ`, `mvShortExact ℚ`, `twoSetCover`,
   `smallChains_homologyIso ℚ`, `isZero_mvX₂_homology`, `homology_exact₃/₁`,
   `kernelIsKernel`, `conePointUniqueUpToIso`) is `[CommRing R]`-generic or
   category-generic and instantiated at `ℚ`.
6. The vanishing inputs of `sphereH1_iso_kerF0Q` use
   `isZero_subChainComplex_homology_of_contractibleQ` (the ℚ bridge) in place
   of the ℤ `isZero_subChainComplex_homology_of_contractible`.
-/
