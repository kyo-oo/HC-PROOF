import GSTInfiniteWorldClassification

/-!
# Exact renormalization of coherent GST infinity

Every finite observation cylinder contains an entire independent coherent
world. Splitting and grafting are explicit inverses; forgetting k layers
is surjective and loses exactly a k-trit prefix. No catalogue exhausts even
one finite-observation cylinder.
-/
namespace GSTInfiniteWorldRenormalization
open GSTCoherentCosmology GSTInfiniteWorldClassification

/-- Retained innovation information in the first k layers. -/
def worldPrefix (k : ℕ) (X : WindowTower) : Fin k → Fin 3 :=
  fun i => innovationStream X i.val

/-- Renormalize by discarding the first k innovation layers. -/
def tail (k : ℕ) (X : WindowTower) : WindowTower :=
  streamTower (fun p => innovationStream X (k+p))

/-- Attach an arbitrary finite prefix to an independent infinite continuation. -/
def graft (k : ℕ) (u : Fin k → Fin 3) (Y : WindowTower) : WindowTower :=
  streamTower (fun p => if h : p < k then u ⟨p,h⟩ else innovationStream Y (p-k))

@[simp] theorem innovation_tail (k p : ℕ) (X : WindowTower) :
    innovationStream (tail k X) p = innovationStream X (k+p) := by
  simp [tail, innovationStream_streamTower]

@[simp] theorem innovation_graft (k p : ℕ) (u : Fin k → Fin 3) (Y : WindowTower) :
    innovationStream (graft k u Y) p =
      if h : p < k then u ⟨p,h⟩ else innovationStream Y (p-k) := by
  simp [graft, innovationStream_streamTower]

@[simp] theorem prefix_graft (k : ℕ) (u : Fin k → Fin 3) (Y : WindowTower) :
    worldPrefix k (graft k u Y) = u := by
  funext i
  simp [worldPrefix, i.isLt]

@[simp] theorem tail_graft (k : ℕ) (u : Fin k → Fin 3) (Y : WindowTower) :
    tail k (graft k u Y) = Y := by
  apply windowTowerEquivStream.injective
  funext p
  change innovationStream (tail k (graft k u Y)) p = innovationStream Y p
  simp [show ¬ k+p < k by omega]

/-- Reconstruction across an arbitrary cut is exact, for every coherent world. -/
@[simp] theorem graft_prefix_tail (k : ℕ) (X : WindowTower) :
    graft k (worldPrefix k X) (tail k X) = X := by
  apply windowTowerEquivStream.injective
  funext p
  change innovationStream (graft k (worldPrefix k X) (tail k X)) p = innovationStream X p
  rw [innovation_graft]
  split_ifs with h
  · rfl
  · rw [innovation_tail, Nat.add_sub_of_le (Nat.le_of_not_gt h)]

/-- Complete self-similarity: a coherent infinity is exactly a finite prefix
and an independent coherent infinity. -/
def splitEquiv (k : ℕ) : WindowTower ≃ (Fin k → Fin 3) × WindowTower where
  toFun X := (worldPrefix k X, tail k X)
  invFun z := graft k z.1 z.2
  left_inv := graft_prefix_tail k
  right_inv z := by simp

@[simp] theorem tail_zero (X : WindowTower) : tail 0 X = X := by
  apply windowTowerEquivStream.injective
  funext p
  change innovationStream (tail 0 X) p = innovationStream X p
  simp

/-- Arbitrary-depth renormalization is an exact additive semigroup action. -/
theorem tail_add (k l : ℕ) (X : WindowTower) :
    tail l (tail k X) = tail (k+l) X := by
  apply windowTowerEquivStream.injective
  funext p
  change innovationStream (tail l (tail k X)) p = innovationStream (tail (k+l) X) p
  simp [Nat.add_assoc]

/-- Every future world has all finite-prefix realizations. -/
theorem tail_surjective (k : ℕ) : Function.Surjective (tail k) := by
  intro Y
  exact ⟨graft k (fun _ => 0) Y, tail_graft k _ Y⟩

theorem graft_injective (k : ℕ) (u : Fin k → Fin 3) :
    Function.Injective (graft k u) := by
  intro X Y h
  simpa only [tail_graft] using congrArg (tail k) h

/-- Equality at one resolution is precisely equality of the retained prefix. -/
theorem level_eq_iff_prefix (X Y : WindowTower) (k : ℕ) :
    X.level k = Y.level k ↔ worldPrefix k X = worldPrefix k Y := by
  rw [level_eq_iff_stream_prefix]
  constructor
  · intro h
    funext i
    exact h i.val i.isLt
  · intro h p hp
    exact congrFun h ⟨p,hp⟩

/-- Worlds sharing one finite observation. -/
abbrev Cylinder (X : WindowTower) (k : ℕ) := {Y : WindowTower // Y.level k = X.level k}

/-- Every finite observation cylinder is exactly the full coherent universe. -/
def cylinderEquiv (X : WindowTower) (k : ℕ) : Cylinder X k ≃ WindowTower where
  toFun Y := tail k Y.val
  invFun Z := ⟨graft k (worldPrefix k X) Z, by
    apply (level_eq_iff_prefix _ _ k).mpr
    exact prefix_graft k _ Z⟩
  left_inv Y := by
    apply Subtype.ext
    have hp : worldPrefix k Y.val = worldPrefix k X := (level_eq_iff_prefix _ _ k).mp Y.property
    rw [← hp, graft_prefix_tail]
  right_inv Z := tail_graft k _ Z

/-- A fixed future has exactly one world for each k-trit prefix. -/
def fiberEquiv (Y : WindowTower) (k : ℕ) :
    {X : WindowTower // tail k X = Y} ≃ (Fin k → Fin 3) where
  toFun X := worldPrefix k X.val
  invFun u := ⟨graft k u Y, tail_graft k u Y⟩
  left_inv X := by
    apply Subtype.ext
    rw [← X.property, graft_prefix_tail]
  right_inv u := prefix_graft k u Y

/-- Renormalization loses exactly 3^k possible prefixes, not an unspecified
amount of information. -/
theorem fiber_card (Y : WindowTower) (k : ℕ) :
    Nat.card {X : WindowTower // tail k X = Y} = 3^k := by
  rw [Nat.card_congr (fiberEquiv Y k)]
  simp [Nat.card_eq_fintype_card]

/-- Matching one finite current trace still leaves a full coherent infinity. -/
theorem cylinder_current (X : WindowTower) (k : ℕ) (Y : Cylinder X k) :
    ∀ t p, p < k → towerCurrent Y.val t p = towerCurrent X t p :=
  (finite_observation_equivalence Y.val X k).mp Y.property

/-- No countable catalogue exhausts even a single finite-observation cylinder. -/
theorem cylinder_no_countable_catalogue (X : WindowTower) (k : ℕ)
    (worlds : ℕ → Cylinder X k) :
    ∃ Y : Cylinder X k, ∀ n, Y ≠ worlds n := by
  obtain ⟨Z, hZ⟩ := no_countable_catalogue (fun n => cylinderEquiv X k (worlds n))
  refine ⟨(cylinderEquiv X k).symm Z, ?_⟩
  intro n he
  apply hZ n
  have hh := congrArg (cylinderEquiv X k) he
  have hz : Z = cylinderEquiv X k (worlds n) := by simpa using hh
  exact congrArg WindowTower.level hz

#print axioms cylinder_no_countable_catalogue

#print axioms splitEquiv
#print axioms tail_add
#print axioms cylinderEquiv
#print axioms fiber_card
#print axioms cylinder_current
end GSTInfiniteWorldRenormalization
