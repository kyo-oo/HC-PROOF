import GSTGeneralSpaceCohomology

/-!
# GST causal word defect, with exact cancellation

The ring equations apply to actual operators after a realization is supplied.
In weight one use complex-structure operators. In higher degree use the full
Hodge-charge or filtration data, not a weight-one operator substituted for it.
No assertion of original-X algebraic source existence is an input or conclusion.
-/

namespace GSTCausalFoldDefect

variable {R : Type*} [Ring R]

def defect (J K T : R) : R := K*T-T*J

theorem defect_comp (J K L S T : R) :
    defect J L (S*T) = defect K L S*T + S*defect J K T := by
  simp only [defect]
  noncomm_ring

theorem defect_identity (J : R) : defect J J 1 = 0 := by simp [defect]

theorem safe_comp (J K L S T : R)
    (hS : defect K L S = 0) (hT : defect J K T = 0) :
    defect J L (S*T) = 0 := by rw [defect_comp, hS, hT]; simp

/-- Chronological list: the newest operator multiplies on the left. -/
def transportWord : List R → R
  | [] => 1
  | T :: ts => transportWord ts * T

/-- The exact sum of propagated edge defects, not merely a bound. -/
def accumulatedDefect (J : R) : List R → R
  | [] => 0
  | T :: ts => accumulatedDefect J ts * T + transportWord ts * defect J J T

theorem word_defect_exact (J : R) (ts : List R) :
    defect J J (transportWord ts) = accumulatedDefect J ts := by
  induction ts with
  | nil => simp [transportWord, accumulatedDefect, defect]
  | cons T ts ih =>
      simp only [transportWord, accumulatedDefect, defect_comp, ih]

theorem every_edge_safe_word_safe (J : R) (ts : List R)
    (h : ∀ T ∈ ts, defect J J T = 0) :
    defect J J (transportWord ts) = 0 := by
  induction ts with
  | nil => exact defect_identity J
  | cons T ts ih =>
      apply safe_comp J J J (transportWord ts) T
      · exact ih (by intro U hU; exact h U (List.mem_cons_of_mem T hU))
      · exact h T (List.mem_cons_self)

/-- A nonzero endpoint defect certifies an offending causal edge. -/
theorem endpoint_break_has_bad_edge (J : R) (ts : List R)
    (h : defect J J (transportWord ts) ≠ 0) :
    ∃ T ∈ ts, defect J J T ≠ 0 := by
  classical
  by_contra hh
  apply h
  apply every_edge_safe_word_safe
  intro T hT
  by_contra hBad
  exact hh ⟨T,hT,hBad⟩

section GeneralSpace
open GSTGeneralSpace
variable {G : GeneralSpace}

/-- A genuinely realized causal operator functor. No Hodge-safety field is assumed. -/
structure OperatorRealization (G : GeneralSpace) (R : Type*) [Ring R] where
  operator : ∀ {x y : G.Point}, G.Path x y → R
  identity : ∀ x, operator (G.idPath x) = 1
  composition : ∀ {x y z} (a : G.Path x y) (b : G.Path y z),
    operator (G.compPath a b) = operator b * operator a

theorem causal_path_defect (P : OperatorRealization G R)
    {x y z : G.Point} (a : G.Path x y) (b : G.Path y z) (J K L : R) :
    defect J L (P.operator (G.compPath a b)) =
      defect K L (P.operator b) * P.operator a +
        P.operator b * defect J K (P.operator a) := by
  rw [P.composition, defect_comp]

end GeneralSpace

section NativeTower
open GSTGeneralSpace
open GSTGeneralSpace.NativeCycleRecoordination
variable {G : GeneralSpace} {N H : Type*}
  [AddCommGroup N] [Module ℚ N] [AddCommGroup H] [Module ℚ H]

/-- The cycle itself, recursively built from genuine native transports. -/
def nativeCycleTower (P : CyclePathRealization G N H)
    (world : ℕ → G.Point)
    (step : ∀ n, G.Path (world n) (world (n+1))) : ℕ → N → N
  | 0, seed => seed
  | n+1, seed => P.nativeTransport (step n) (nativeCycleTower P world step n seed)

/-- Compatibility at every finite depth is derived from naturality, rather
than supplied as an unrelated proposition-valued hypothesis. -/
theorem nativeCycleTower_class (P : CyclePathRealization G N H)
    (world : ℕ → G.Point) (step : ∀ n, G.Path (world n) (world (n+1)))
    (n : ℕ) (seed : N) :
    P.cycleClass (nativeCycleTower P world step n seed) =
      causalTowerHodgeState P world step n (P.cycleClass seed) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change P.cycleClass (P.nativeTransport (step n)
        (nativeCycleTower P world step n seed)) =
        P.hodgeTransport (step n) (causalTowerHodgeState P world step n (P.cycleClass seed))
      rw [P.naturality, ih]

end NativeTower

/-! ## Rational branching with the cycle itself retained

Terms may have different seeds and depths. They share the same realized
cycle carrier; a geometric instance must respect the intended grading and
world summands. A sum equality to alpha is checked data, never assumed from
the common causal address.
-/
section NativeBranching
open GSTGeneralSpace GSTGeneralSpace.NativeCycleRecoordination
variable {G : GeneralSpace} {N H : Type*}
  [AddCommGroup N] [Module ℚ N] [AddCommGroup H] [Module ℚ H]

def nativeCycleCombination (P : CyclePathRealization G N H)
    (world : ℕ → G.Point) (step : ∀ n, G.Path (world n) (world (n+1))) :
    List (ℚ × (ℕ × N)) → N
  | [] => 0
  | (a,n,z) :: ts => a • nativeCycleTower P world step n z +
      nativeCycleCombination P world step ts

def hodgeCombination (P : CyclePathRealization G N H)
    (world : ℕ → G.Point) (step : ∀ n, G.Path (world n) (world (n+1))) :
    List (ℚ × (ℕ × N)) → H
  | [] => 0
  | (a,n,z) :: ts => a • causalTowerHodgeState P world step n (P.cycleClass z) +
      hodgeCombination P world step ts

theorem nativeCycleCombination_class (P : CyclePathRealization G N H)
    (world : ℕ → G.Point) (step : ∀ n, G.Path (world n) (world (n+1)))
    (ts : List (ℚ × (ℕ × N))) :
    P.cycleClass (nativeCycleCombination P world step ts) =
      hodgeCombination P world step ts := by
  induction ts with
  | nil => simp [nativeCycleCombination, hodgeCombination]
  | cons t ts ih =>
      rcases t with ⟨a,n,z⟩
      simp only [nativeCycleCombination, hodgeCombination, map_add,
        map_smul, nativeCycleTower_class, ih]

theorem prescribed_class_from_branching (P : CyclePathRealization G N H)
    (world : ℕ → G.Point) (step : ∀ n, G.Path (world n) (world (n+1)))
    (ts : List (ℚ × (ℕ × N))) (alpha : H)
    (hexact : hodgeCombination P world step ts = alpha) :
    P.cycleClass (nativeCycleCombination P world step ts) = alpha :=
  (nativeCycleCombination_class P world step ts).trans hexact

/-- A nonzero scale is explicitly inverted in the native cycle carrier. -/
theorem normalized_cycle_class (cl : N →ₗ[ℚ] H)
    (z : N) (alpha : H) (m : ℚ) (hm : m ≠ 0)
    (hz : cl z=m • alpha) : cl (m⁻¹ • z)=alpha := by
  rw [map_smul, hz, smul_smul, inv_mul_cancel₀ hm, one_smul]

theorem rational_range_saturated (cl : N →ₗ[ℚ] H)
    (alpha : H) (m : ℚ) (hm : m ≠ 0) :
    m • alpha ∈ LinearMap.range cl ↔ alpha ∈ LinearMap.range cl := by
  constructor
  · rintro ⟨z,hz⟩
    exact ⟨m⁻¹ • z, normalized_cycle_class cl z alpha m hm hz⟩
  · rintro ⟨z,hz⟩
    exact ⟨m • z, by rw [map_smul, hz]⟩

#print axioms nativeCycleCombination_class
#print axioms prescribed_class_from_branching
#print axioms rational_range_saturated
end NativeBranching

#print axioms word_defect_exact
#print axioms endpoint_break_has_bad_edge
#print axioms causal_path_defect
#print axioms nativeCycleTower_class
/-! ## Whole-space opposedness: explicit missing-mode decomposition

L is instantiated by the actual curvature transpose, not a cycle-class map.
The manifold proof identifies ker L as the closed vertical holomorphic modes.
-/
section WholeSpaceOpposedness
variable {V W : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

def centralPlus (u v : V) : V := (1/2 : ℂ) • (u-Complex.I • v)
def centralMinus (u v : V) : V := (1/2 : ℂ) • (u+Complex.I • v)

theorem central_parts_sum (u v : V) : centralPlus u v+centralMinus u v=u := by
  unfold centralPlus centralMinus
  module

theorem central_parts_difference (u v : V) :
    Complex.I • (centralPlus u v-centralMinus u v)=v := by
  calc
    Complex.I • (centralPlus u v-centralMinus u v)=
        (-Complex.I*Complex.I) • v := by
          unfold centralPlus centralMinus
          module
    _ = v := by simp [neg_mul,Complex.I_mul_I]

theorem closed_parts_of_zero_missing_mode (L : V →ₗ[ℂ] W) (u v : V)
    (hu : L u=0) (hv : L v=0) :
    L (centralPlus u v)=0 ∧ L (centralMinus u v)=0 := by
  simp [centralPlus,centralMinus,map_smul,map_sub,map_add,hu,hv]

theorem pure_split_iff_missing_mode_zero (L : V →ₗ[ℂ] W) (u v : V)
    (hu : L u=0) :
    (∃ a b : V,L a=0 ∧ L b=0 ∧ u=a+b ∧ v=Complex.I • (a-b)) ↔ L v=0 := by
  constructor
  · rintro ⟨a,b,ha,hb,_,rfl⟩
    simp [map_smul,map_sub,ha,hb]
  · intro hv
    have h := closed_parts_of_zero_missing_mode L u v hu hv
    exact ⟨centralPlus u v,centralMinus u v,h.1,h.2,
      (central_parts_sum u v).symm,(central_parts_difference u v).symm⟩

theorem nonzero_missing_mode_refuses_pure_split (L : V →ₗ[ℂ] W) (u v : V)
    (hu : L u=0) (hv : L v ≠ 0) :
    ¬ ∃ a b : V,L a=0 ∧ L b=0 ∧ u=a+b ∧ v=Complex.I • (a-b) := by
  rw [pure_split_iff_missing_mode_zero L u v hu]
  exact hv

#print axioms pure_split_iff_missing_mode_zero
end WholeSpaceOpposedness

/-! ## Universal relation factorization for base-coupled quotient folds

For geometry, C sends a vertical handle to its actual Chern class. A
quotient's pullback on vertical coefficients is I. Every restoring I has
one and only one factorization through ker C. No cycle selector is involved.
-/
section RestoringRelations
variable {𝕜 U V W : Type*} [Field 𝕜]
  [AddCommGroup U] [Module 𝕜 U] [AddCommGroup V] [Module 𝕜 V]
  [AddCommGroup W] [Module 𝕜 W]

def restoringLift (C : V →ₗ[𝕜] W) (I : U →ₗ[𝕜] V)
    (h : C.comp I=0) : U →ₗ[𝕜] C.ker where
  toFun u := ⟨I u, by
    have hu := congrArg (fun T : U →ₗ[𝕜] W => T u) h
    simpa using hu⟩
  map_add' u v := by apply Subtype.ext; exact I.map_add u v
  map_smul' a u := by apply Subtype.ext; exact I.map_smul a u

theorem restoringLift_underlying (C : V →ₗ[𝕜] W) (I : U →ₗ[𝕜] V)
    (h : C.comp I=0) : C.ker.subtype.comp (restoringLift C I h)=I := by
  ext u
  rfl

theorem restoring_iff_factors_through_relations
    (C : V →ₗ[𝕜] W) (I : U →ₗ[𝕜] V) :
    C.comp I=0 ↔ ∃ J : U →ₗ[𝕜] C.ker, C.ker.subtype.comp J=I := by
  constructor
  · intro h
    exact ⟨restoringLift C I h,restoringLift_underlying C I h⟩
  · rintro ⟨J,rfl⟩
    ext u
    exact (J u).property

theorem restoring_factorization_unique (C : V →ₗ[𝕜] W)
    (I : U →ₗ[𝕜] V) (h : C.comp I=0) :
    ∃! J : U →ₗ[𝕜] C.ker, C.ker.subtype.comp J=I := by
  refine ⟨restoringLift C I h,restoringLift_underlying C I h,?_⟩
  intro J hJ
  apply LinearMap.ext
  intro u
  apply Subtype.ext
  exact congrArg (fun T : U →ₗ[𝕜] V => T u) hJ

theorem restoringLift_injective (C : V →ₗ[𝕜] W)
    (I : U →ₗ[𝕜] V) (h : C.comp I=0) (hinj : Function.Injective I) :
    Function.Injective (restoringLift C I h) := by
  intro u v huv
  apply hinj
  exact congrArg Subtype.val huv

theorem relation_inclusion_restores (C : V →ₗ[𝕜] W) :
    C.comp C.ker.subtype=0 := by
  ext u
  exact u.property

#print axioms restoring_factorization_unique
end RestoringRelations

end GSTCausalFoldDefect
