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

#print axioms word_defect_exact
#print axioms endpoint_break_has_bad_edge
#print axioms causal_path_defect
#print axioms nativeCycleTower_class
end GSTCausalFoldDefect
