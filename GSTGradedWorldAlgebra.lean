import Mathlib
import GSTWorldCosmology

/-!
# GST GRADED WORLD ALGEBRA

The six Kunneth sectors of the original 4 x 3 chart are one specialization
of a grading carried by every rectangular GST world.

For a cell (C,d), degree is C+d.  The resulting degree projectors are
idempotent, pairwise orthogonal and complete.  Arbitrary digit/carry shifts
raise degree by exactly their shift depth.

The fixed six-degree Kunneth polynomial is likewise one instance of an
arbitrary finite-world spectral projector polynomial.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

namespace GSTGradedWorldAlgebra

open GSTWorldCosmology

/-- Native total degree on an arbitrary rectangular GST world. -/
def worldDegree {A B : Nat} (c : WorldCell A B) : Nat :=
  c.1.1 + c.2.1

/-- Project an amplitude onto one total-degree sector. -/
def worldSectorProj {A B : Nat} (k : Nat)
    (g : WorldCoef A B) : WorldCoef A B :=
  fun c => if worldDegree c = k then g c else 0

/-- Sector projectors are idempotent in every rectangular world. -/
theorem worldSectorProj_idempotent
    {A B : Nat} (k : Nat) (g : WorldCoef A B) :
    worldSectorProj k (worldSectorProj k g) = worldSectorProj k g := by
  funext c
  by_cases h : worldDegree c = k <;>
    simp [worldSectorProj, h]

/-- Distinct sectors are exactly orthogonal. -/
theorem worldSectorProj_orthogonal
    {A B : Nat} (k j : Nat) (hkj : k ≠ j)
    (g : WorldCoef A B) :
    worldSectorProj k (worldSectorProj j g) = fun _ => 0 := by
  funext c
  by_cases hj : worldDegree c = j
  · have hjk : j ≠ k := by
      intro h
      exact hkj h.symm
    simp [worldSectorProj, hj, hjk]
  · simp [worldSectorProj, hj]

/-- Every live cell has degree strictly below A+B. -/
theorem worldDegree_lt
    {A B : Nat} (c : WorldCell A B) :
    worldDegree c < A + B := by
  unfold worldDegree
  omega

/-- **DIMENSION-FREE KUNNETH DECOMPOSITION.**
All degree projectors below A+B sum to the identity. -/
theorem worldSectorProj_sum
    {A B : Nat} (g : WorldCoef A B) :
    (fun c => ∑ k ∈ Finset.range (A+B), worldSectorProj k g c) = g := by
  funext c
  classical
  have hmem : worldDegree c ∈ Finset.range (A+B) :=
    Finset.mem_range.mpr (worldDegree_lt c)
  rw [Finset.sum_eq_single (worldDegree c)]
  · simp [worldSectorProj]
  · intro b hb hne
    have hne' : worldDegree c ≠ b := hne.symm
    simp [worldSectorProj, hne']
  · intro hnot
    exact (hnot hmem).elim

/-- Projection distributes over addition. -/
theorem worldSectorProj_add
    {A B : Nat} (k : Nat) (f g : WorldCoef A B) :
    worldSectorProj k (fun c => f c + g c) =
      (fun c => worldSectorProj k f c + worldSectorProj k g c) := by
  funext c
  by_cases h : worldDegree c = k <;>
    simp [worldSectorProj, h]

/-- Arbitrary digit transport raises total degree by exactly n. -/
theorem digitShiftN_respects_degree
    {A B : Nat} (n k : Nat) (g : WorldCoef A B) :
    digitShiftN n (worldSectorProj k g) =
      worldSectorProj (k+n) (digitShiftN n g) := by
  funext c
  by_cases hn : n ≤ c.2.1
  · have hiff :
        (c.1.1 + (c.2.1 - n) = k) ↔
          (c.1.1 + c.2.1 = k+n) := by
      omega
    simp [digitShiftN, worldSectorProj, worldDegree, hn, hiff]
  · simp [digitShiftN, worldSectorProj, worldDegree, hn]

/-- Arbitrary carry transport raises total degree by exactly n. -/
theorem carryShiftN_respects_degree
    {A B : Nat} (n k : Nat) (g : WorldCoef A B) :
    carryShiftN n (worldSectorProj k g) =
      worldSectorProj (k+n) (carryShiftN n g) := by
  funext c
  by_cases hn : n ≤ c.1.1
  · have hiff :
        ((c.1.1 - n) + c.2.1 = k) ↔
          (c.1.1 + c.2.1 = k+n) := by
      omega
    simp [carryShiftN, worldSectorProj, worldDegree, hn, hiff]
  · simp [carryShiftN, worldSectorProj, worldDegree, hn]

/-- Native degree correspondence on arbitrary worlds. -/
def worldDegreeOp {A B : Nat}
    (g : WorldCoef A B) : WorldCoef A B :=
  fun c => ((worldDegree c : Nat) : Int) * g c

/-- Polynomial functional calculus of the native degree correspondence. -/
def worldPolyOp {A B : Nat}
    (p : Polynomial Int) (g : WorldCoef A B) : WorldCoef A B :=
  fun c => p.eval ((worldDegree c : Nat) : Int) * g c

/-- Universal finite-degree spectral polynomial. -/
noncomputable def worldKunnethPoly
    (bound k : Nat) : Polynomial Int :=
  ((List.range bound).filter (fun j => j ≠ k)).foldr
    (fun (j : Nat) (p : Polynomial Int) =>
      (Polynomial.X - Polynomial.C (j : Int)) * p)
    (1 : Polynomial Int)

private theorem eval_worldKunneth_foldr
    (js : List Nat) (x : Int) :
    ((js.foldr
      (fun (j : Nat) (p : Polynomial Int) =>
        (Polynomial.X - Polynomial.C (j : Int)) * p)
      (1 : Polynomial Int)).eval x)
      =
    js.foldr (fun (j : Nat) (v : Int) => (x - (j : Int)) * v) 1 := by
  induction js with
  | nil => simp
  | cons j js ih =>
      simp only [List.foldr]
      rw [Polynomial.eval_mul, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C, ih]

private theorem worldKunneth_foldr_zero
    (js : List Nat) (x : Nat) (hx : x ∈ js) :
    js.foldr (fun (j : Nat) (v : Int) => ((x : Int) - (j : Int)) * v) 1 = 0 := by
  induction js with
  | nil => exact absurd hx (by simp)
  | cons j js ih =>
      rcases List.mem_cons.mp hx with h | h
      · subst j
        simp
      · simp [ih h]

private theorem worldKunneth_foldr_ne_zero
    (js : List Nat) (k : Nat)
    (hk : ∀ j ∈ js, j ≠ k) :
    js.foldr (fun (j : Nat) (v : Int) => ((k : Int) - (j : Int)) * v) 1 ≠ 0 := by
  induction js with
  | nil => simp
  | cons j js ih =>
      have hjk : j ≠ k := hk j (by simp)
      exact mul_ne_zero (by omega)
        (ih (fun j' hj' => hk j' (by
          exact List.mem_cons_of_mem j hj')))

/-- The universal Kunneth polynomial vanishes on every other degree below
the chosen finite bound. -/
theorem worldKunnethPoly_eval_zero
    (bound k x : Nat) (hx : x < bound) (hxk : x ≠ k) :
    (worldKunnethPoly bound k).eval (x : Int) = 0 := by
  unfold worldKunnethPoly
  rw [eval_worldKunneth_foldr]
  exact worldKunneth_foldr_zero
    ((List.range bound).filter (fun j => j ≠ k)) x
    (List.mem_filter.mpr
      ⟨List.mem_range.mpr hx, decide_eq_true hxk⟩)

/-- At its own degree the universal spectral polynomial is nonzero. -/
theorem worldKunnethPoly_eval_self_ne_zero
    (bound k : Nat) (hk : k < bound) :
    (worldKunnethPoly bound k).eval (k : Int) ≠ 0 := by
  unfold worldKunnethPoly
  rw [eval_worldKunneth_foldr]
  exact worldKunneth_foldr_ne_zero
    ((List.range bound).filter (fun j => j ≠ k)) k
    (fun j hj => of_decide_eq_true (List.mem_filter.mp hj).2)

/-- **DIMENSION-FREE KUNNETH POLYNOMIAL THEOREM.**

Every degree-k projector in every A x B GST world is an explicit integer
polynomial in the degree correspondence, up to a nonzero integer scalar. -/
theorem worldKunneth_projector_polynomial
    {A B : Nat} (k : Nat) (hk : k < A+B) :
    ∃ (p : Polynomial Int) (c : Int), c ≠ 0 ∧
      ∀ (g : WorldCoef A B) (x : WorldCell A B),
        worldPolyOp p g x = c * worldSectorProj k g x := by
  refine ⟨worldKunnethPoly (A+B) k,
    (worldKunnethPoly (A+B) k).eval (k : Int),
    worldKunnethPoly_eval_self_ne_zero (A+B) k hk, ?_⟩
  intro g x
  unfold worldPolyOp worldSectorProj
  by_cases hdeg : worldDegree x = k
  · simp [hdeg]
  · have hlt : worldDegree x < A+B := worldDegree_lt x
    have hz :=
      worldKunnethPoly_eval_zero (A+B) k (worldDegree x) hlt hdeg
    simp [hdeg, hz]

/-- One capstone for the dimension-free graded world algebra. -/
theorem graded_world_crown :
    (∀ A B k (g : WorldCoef A B),
      worldSectorProj k (worldSectorProj k g) = worldSectorProj k g)
    ∧ (∀ A B k j, k ≠ j → ∀ (g : WorldCoef A B),
      worldSectorProj k (worldSectorProj j g) = fun _ => 0)
    ∧ (∀ A B (g : WorldCoef A B),
      (fun c => ∑ k ∈ Finset.range (A+B), worldSectorProj k g c) = g)
    ∧ (∀ A B n k (g : WorldCoef A B),
      digitShiftN n (worldSectorProj k g) =
        worldSectorProj (k+n) (digitShiftN n g))
    ∧ (∀ A B n k (g : WorldCoef A B),
      carryShiftN n (worldSectorProj k g) =
        worldSectorProj (k+n) (carryShiftN n g)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro A B k g
    exact worldSectorProj_idempotent k g
  · intro A B k j hkj g
    exact worldSectorProj_orthogonal k j hkj g
  · intro A B g
    exact worldSectorProj_sum g
  · intro A B n k g
    exact digitShiftN_respects_degree n k g
  · intro A B n k g
    exact carryShiftN_respects_degree n k g

#check worldSectorProj_idempotent
#check worldSectorProj_orthogonal
#check worldSectorProj_sum
#check digitShiftN_respects_degree
#check carryShiftN_respects_degree
#check worldKunneth_projector_polynomial
#check graded_world_crown

#print axioms worldSectorProj_sum
#print axioms digitShiftN_respects_degree
#print axioms carryShiftN_respects_degree
#print axioms worldKunneth_projector_polynomial
#print axioms graded_world_crown


/-! ## Unbounded grading, independent of a window -/
def cosmicDegree (c : CosmicCell) : ℕ := c.1+c.2

def cosmicCharge (c : CosmicCell) : ℤ := (c.1 : ℤ)-c.2

/-- Degree and signed charge jointly determine the two native coordinates. -/
theorem cosmic_degree_charge_injective :
    Function.Injective (fun c : CosmicCell => (cosmicDegree c, cosmicCharge c)) := by
  intro c d h
  have ht := congrArg Prod.fst h
  have hc := congrArg Prod.snd h
  simp only [cosmicDegree, cosmicCharge] at ht hc
  apply Prod.ext <;> omega

def cosmicSector (k : ℕ) (f : CompletedCosmos) : CompletedCosmos :=
  fun c => if cosmicDegree c=k then f c else 0

@[simp] theorem observe_cosmicSector (A B k : ℕ) (f : CompletedCosmos) :
    observe A B (cosmicSector k f) = worldSectorProj k (observe A B f) := rfl

theorem cosmicSector_idempotent (k : ℕ) (f : CompletedCosmos) :
    cosmicSector k (cosmicSector k f) = cosmicSector k f := by
  funext c
  change (if cosmicDegree c = k then
      (if cosmicDegree c = k then f c else 0) else 0) =
    (if cosmicDegree c = k then f c else 0)
  by_cases hk : cosmicDegree c = k
  · simp only [if_pos hk]
  · simp only [if_neg hk]

theorem cosmicSector_orthogonal (k j : ℕ) (h : k ≠ j) (f : CompletedCosmos) :
    cosmicSector k (cosmicSector j f) = 0 := by
  funext c
  change (if cosmicDegree c = k then
      (if cosmicDegree c = j then f c else 0) else 0) = 0
  by_cases hk : cosmicDegree c = k
  · have hj : cosmicDegree c ≠ j := by
      intro hcj
      apply h
      exact hk.symm.trans hcj
    simp only [if_pos hk, if_neg hj]
  · simp only [if_neg hk]

theorem cosmic_digit_grading (n k : ℕ) (f : CompletedCosmos) :
    cosmicDigitShift n (cosmicSector k f) =
      cosmicSector (k+n) (cosmicDigitShift n f) := by
  apply observations_separate
  intro A B
  simpa using digitShiftN_respects_degree (A:=A) (B:=B) n k (observe A B f)

theorem cosmic_carry_grading (n k : ℕ) (f : CompletedCosmos) :
    cosmicCarryShift n (cosmicSector k f) =
      cosmicSector (k+n) (cosmicCarryShift n f) := by
  apply observations_separate
  intro A B
  simpa using carryShiftN_respects_degree (A:=A) (B:=B) n k (observe A B f)


/-! ## GST EMERGENT-DIMENSION CAUSAL TATE FOLD

A dimension in GeneralSpace is NOT intrinsic to the carrier.  Once the
unbounded CosmicCell grading is chosen, simultaneous increments on both
coordinates have exact total-degree and signed-charge laws.  The latter
is the algebraic prerequisite for a genuine Hodge (p,p) interpretation.
It does NOT, on its own, supply such a geometric realization or a Chow
cycle representing an arbitrary rational Hodge class.

The actual projective-bundle/Chern--Segre realization and a topological
non-holomorphic Hodge-breaking discriminator are derived separately in
research/derivations/GST_emergent_dimension_causal_hodge_fold_2026_10_21.tex.
-/

/-- Simultaneous shift on the two UNBOUNDED world coordinates.
This is a coordinate-level Tate fold, NOT an assumed algebraic map. -/
def cosmicTateFold (j : ℕ) (c : CosmicCell) : CosmicCell :=
  (c.1 + j, c.2 + j)

/-- Both native coordinates move, so emergent total degree grows by 2j. -/
theorem cosmicTateFold_degree (j : ℕ) (c : CosmicCell) :
    cosmicDegree (cosmicTateFold j c) = cosmicDegree c + 2*j := by
  rcases c with ⟨a, b⟩
  simp only [cosmicDegree, cosmicTateFold]
  omega

/-- A symmetric dimensional fold CANNOT change signed grading charge. -/
theorem cosmicTateFold_charge (j : ℕ) (c : CosmicCell) :
    cosmicCharge (cosmicTateFold j c) = cosmicCharge c := by
  rcases c with ⟨a, b⟩
  simp only [cosmicCharge, cosmicTateFold]
  omega

/-- Folding sequentially is exactly a single fold by the sum of depths. -/
theorem cosmicTateFold_comp (j k : ℕ) (c : CosmicCell) :
    cosmicTateFold k (cosmicTateFold j c) =
      cosmicTateFold (j+k) c := by
  rcases c with ⟨a, b⟩
  simp only [cosmicTateFold]
  congr 1 <;> omega

/-- The abstract GST charge-zero sector is stable under all Tate folds.
Only a typed Hodge realization may interpret it as algebraic Hodge type. -/
theorem cosmicTateFold_charge_zero_iff (j : ℕ) (c : CosmicCell) :
    cosmicCharge (cosmicTateFold j c) = 0 ↔ cosmicCharge c = 0 := by
  rw [cosmicTateFold_charge]

/-- Finite GST causal histories of successive Tate folds. -/
def cosmicTatePath : List ℕ → CosmicCell → CosmicCell
  | [], c => c
  | j :: rest, c => cosmicTatePath rest (cosmicTateFold j c)

/-- Signed charge is conserved by an arbitrarily long FINITE causal fold. -/
theorem cosmicTatePath_charge (steps : List ℕ) (c : CosmicCell) :
    cosmicCharge (cosmicTatePath steps c) = cosmicCharge c := by
  induction steps generalizing c with
  | nil => rfl
  | cons j rest ih =>
      calc
        cosmicCharge (cosmicTatePath (j :: rest) c) =
            cosmicCharge (cosmicTatePath rest (cosmicTateFold j c)) := rfl
        _ = cosmicCharge (cosmicTateFold j c) := ih _
        _ = cosmicCharge c := cosmicTateFold_charge j c

#check cosmicTateFold_degree
#check cosmicTateFold_charge
#check cosmicTateFold_comp
#check cosmicTateFold_charge_zero_iff
#check cosmicTatePath_charge
#print axioms cosmicTatePath_charge


/-! ## GST CAUSAL HODGE GENESIS — grading born from a causal realization

The primitive universe is not a pre-existing fixed Hodge decomposition.
A certified causal graph realization can acquire new cohomological degrees,
weights and Hodge coordinates.  We retain ALL of those coordinates together
rather than collapsing them onto a rank-one cosmic diagonal.

The arithmetic here is the universal grading law of the geometric causal
incidence / smoothing computation in
research/derivations/GST_causal_graph_double_fold_weight_emergence_2026-10-22.tex.

Actual algebraic geometric realization and the canonical Chow class map remain
separate typed tasks; no output of these degree laws asserts the existence
of an algebraic representative of an arbitrary class on original X.
-/

/-- A single emergent cohomology cell; Hodge coordinates and degree are outputs
of the SAME causal geometric realization, not given as an old fixed Hodge map. -/
structure CausalHodgeCell where
  cohomologicalDegree : ℕ
  leftWeight : ℕ
  rightWeight : ℕ
  deriving DecidableEq

/-- The original infinite GST cosmic address is the emergent Hodge bidegree. -/
def CausalHodgeCell.cosmicAddress (x : CausalHodgeCell) : CosmicCell :=
  (x.leftWeight, x.rightWeight)

/-- Signed Hodge charge generated in the realized causal cell. -/
def CausalHodgeCell.charge (x : CausalHodgeCell) : ℤ :=
  cosmicCharge x.cosmicAddress

/-- Weight is derived by the GST dimension-free degree operation. -/
def CausalHodgeCell.weight (x : CausalHodgeCell) : ℕ :=
  cosmicDegree x.cosmicAddress

/-- A causal realization may have weight different from cohomological degree.
This signed defect is ZERO for each pure piece of a smooth projective world. -/
def CausalHodgeCell.purityGap (x : CausalHodgeCell) : ℤ :=
  (x.weight : ℤ) - (x.cohomologicalDegree : ℤ)

/-- Symmetric Tate-dimensional extension of one already born cohomology cell. -/
def CausalHodgeCell.tate (j : ℕ) (x : CausalHodgeCell) : CausalHodgeCell :=
  ⟨x.cohomologicalDegree + 2*j, x.leftWeight+j, x.rightWeight+j⟩

/-- The infinite cosmic address commutes EXACTLY with the causal Tate fold. -/
theorem CausalHodgeCell.cosmicAddress_tate (j : ℕ) (x : CausalHodgeCell) :
    (x.tate j).cosmicAddress = cosmicTateFold j x.cosmicAddress := by
  cases x
  rfl

/-- The full graded causal fold preserves signed Hodge charge. -/
theorem CausalHodgeCell.charge_tate (j : ℕ) (x : CausalHodgeCell) :
    (x.tate j).charge = x.charge := by
  unfold CausalHodgeCell.charge
  rw [CausalHodgeCell.cosmicAddress_tate, cosmicTateFold_charge]

/-- The full graded causal fold preserves the purity gap as well.
This is stronger than signed-charge conservation by itself. -/
theorem CausalHodgeCell.purityGap_tate (j : ℕ) (x : CausalHodgeCell) :
    (x.tate j).purityGap = x.purityGap := by
  cases x with
  | mk k a b =>
    simp only [CausalHodgeCell.tate, CausalHodgeCell.purityGap,
      CausalHodgeCell.weight, CausalHodgeCell.cosmicAddress,
      cosmicDegree]
    push_cast
    ring

/-- Causal gluing of a nodal rational graph LOOP creates a cohomology class
in degree one with Hodge type (0,0), transported to every Tate depth. -/
def causalNodalLoopBirth (j : ℕ) : CausalHodgeCell :=
  ⟨2*j+1, j, j⟩

/-- Two independent causal graph loops create an EVEN-degree diagonal cell
whose realized weight is two BELOW its cohomological degree. -/
def causalDoubleLoopBirth (j : ℕ) : CausalHodgeCell :=
  ⟨2*j+2, j, j⟩

/-- Genuine smoothing of a genus-g causal graph realization creates a
holomorphic H^(1,0) direction, followed by any Tate dimension depth. -/
def causalSmoothLeftBirth (j : ℕ) : CausalHodgeCell :=
  ⟨2*j+1, j+1, j⟩

/-- Genuine smoothing simultaneously births its conjugate H^(0,1) sector. -/
def causalSmoothRightBirth (j : ℕ) : CausalHodgeCell :=
  ⟨2*j+1, j, j+1⟩

/-- Nodal loop incidence gives a diagonal charge but IMPURE degree-one class. -/
theorem causalNodalLoopBirth_signature (j : ℕ) :
    (causalNodalLoopBirth j).charge = 0 ∧
    (causalNodalLoopBirth j).purityGap = -1 := by
  constructor <;>
    simp [causalNodalLoopBirth, CausalHodgeCell.charge,
      CausalHodgeCell.purityGap, CausalHodgeCell.cosmicAddress,
      CausalHodgeCell.weight, cosmicCharge, cosmicDegree] <;>
    omega

/-- Multiplication of two independent loop directions creates a diagonal
even-degree cohomological cell with PURITY GAP -2 at every depth. -/
theorem causalDoubleLoopBirth_signature (j : ℕ) :
    (causalDoubleLoopBirth j).charge = 0 ∧
    (causalDoubleLoopBirth j).purityGap = -2 := by
  constructor <;>
    simp [causalDoubleLoopBirth, CausalHodgeCell.charge,
      CausalHodgeCell.purityGap, CausalHodgeCell.cosmicAddress,
      CausalHodgeCell.weight, cosmicCharge, cosmicDegree] <;>
    omega

/-- The two genuinely born smoothing sectors are PURE with opposite charge.
The new Hodge bidegrees follow from the genus of the smooth realization. -/
theorem causalSmoothBirth_signatures (j : ℕ) :
    (causalSmoothLeftBirth j).charge = 1 ∧
    (causalSmoothRightBirth j).charge = -1 ∧
    (causalSmoothLeftBirth j).purityGap = 0 ∧
    (causalSmoothRightBirth j).purityGap = 0 := by
  simp [causalSmoothLeftBirth, causalSmoothRightBirth, CausalHodgeCell.charge,
    CausalHodgeCell.purityGap, CausalHodgeCell.weight,
    CausalHodgeCell.cosmicAddress, cosmicDegree, cosmicCharge]
  omega

/-- The smooth Hodge left sector is exactly the Tate orbit of its geometric
genus-one basic bidegree. -/
theorem causalSmoothLeftBirth_tate (j : ℕ) :
    causalSmoothLeftBirth j = (causalSmoothLeftBirth 0).tate j := by
  cases j <;>
    simp [causalSmoothLeftBirth, CausalHodgeCell.tate,
      Nat.succ_eq_add_one, Nat.mul_add, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm]

/-- Nodal Hodge birth and smooth Hodge birth arise from DIFFERENT causal
geometries at the same Tate depth and therefore have different signatures. -/
theorem nodal_smooth_causal_genesis_is_nontrivial (j : ℕ) :
    (causalNodalLoopBirth j).purityGap ≠
      (causalSmoothLeftBirth j).purityGap := by
  have hn := (causalNodalLoopBirth_signature j).2
  have hs := (causalSmoothBirth_signatures j).2.2.1
  rw [hn, hs]
  decide


/-! ## ALL-ORDER GST CAUSAL TENSOR GENESIS

A causal birth product does not inherit a fixed ambient dimension.
Its cohomological degree and its TWO Hodge coordinates are independently
generated by the same tensor operation.  This is the graded arithmetic
of the genuine Kunneth realization on products of nodal graph worlds
and projective Tate factors derived in
research/derivations/GST_causal_graph_double_fold_weight_emergence_2026-10-22.tex.
The actual scheme realization and the canonical cycle-class map have
their own geometric types; the tensor law does not manufacture them.
-/

/-- Compose two genuinely born causal cohomology cells. The three
independent coordinates are all determined by the same product. -/
def CausalHodgeCell.tensor (x y : CausalHodgeCell) : CausalHodgeCell :=
  ⟨x.cohomologicalDegree + y.cohomologicalDegree,
   x.leftWeight + y.leftWeight, x.rightWeight + y.rightWeight⟩

/-- The causal tensor product is associative across arbitrarily many worlds. -/
theorem CausalHodgeCell.tensor_assoc (x y z : CausalHodgeCell) :
    (x.tensor y).tensor z = x.tensor (y.tensor z) := by
  cases x with
  | mk k a b =>
    cases y with
    | mk l c d =>
      cases z with
      | mk m e f =>
        simp [CausalHodgeCell.tensor, Nat.add_assoc]

/-- Hodge signed charge is additive under causal tensor products. -/
theorem CausalHodgeCell.charge_tensor (x y : CausalHodgeCell) :
    (x.tensor y).charge = x.charge + y.charge := by
  cases x with
  | mk k a b =>
    cases y with
    | mk l c d =>
      simp [CausalHodgeCell.tensor, CausalHodgeCell.charge,
        CausalHodgeCell.cosmicAddress, cosmicCharge]
      omega

/-- Cohomological degree and weight are produced together, so the
purity gap is additive, not an independently assigned Hodge label. -/
theorem CausalHodgeCell.purityGap_tensor (x y : CausalHodgeCell) :
    (x.tensor y).purityGap = x.purityGap + y.purityGap := by
  cases x with
  | mk k a b =>
    cases y with
    | mk l c d =>
      simp [CausalHodgeCell.tensor, CausalHodgeCell.purityGap,
        CausalHodgeCell.weight, CausalHodgeCell.cosmicAddress,
        cosmicDegree]
      omega

/-- Multiple GST causal graph loops born via independent incidence
identifications, with an arbitrary emergent Tate dimension depth. -/
def causalManyLoopBirth (m j : ℕ) : CausalHodgeCell :=
  ⟨m + 2*j, j, j⟩

/-- The genuine uniform ALL-ORDER causal signature:
m independently realized graph-cohomology loops have CHARGE ZERO
and maximal purity deficit m.  The Hodge type and degree are produced
by the same causal product, not chosen afterwards. -/
theorem causalManyLoopBirth_signature (m j : ℕ) :
    (causalManyLoopBirth m j).charge = 0 ∧
    (causalManyLoopBirth m j).purityGap = -(m : ℤ) := by
  constructor <;>
    simp [causalManyLoopBirth, CausalHodgeCell.charge,
      CausalHodgeCell.purityGap, CausalHodgeCell.weight,
      CausalHodgeCell.cosmicAddress, cosmicDegree, cosmicCharge] <;>
    omega

/-- The previously verified two-world Hodge genesis is the m=2 instance
of the new unlimited causal world-product operation. -/
theorem causalManyLoopBirth_two (j : ℕ) :
    causalManyLoopBirth 2 j = causalDoubleLoopBirth j := by
  simp [causalManyLoopBirth, causalDoubleLoopBirth]
  omega

/-- Causal world multiplication genuinely CREATES the next degree,
rather than adding a new axis to an unrelated pre-existing Hodge space. -/
theorem causalManyLoopBirth_succ (m j : ℕ) :
    causalManyLoopBirth (m+1) j =
      (causalNodalLoopBirth 0).tensor (causalManyLoopBirth m j) := by
  simp [causalManyLoopBirth, causalNodalLoopBirth,
    CausalHodgeCell.tensor]
  omega

/-- Emergent dimension extension commutes with the entire all-order
causal birth operation, while retaining its independently born defect. -/
theorem causalManyLoopBirth_tate (m j : ℕ) :
    causalManyLoopBirth m j = (causalManyLoopBirth m 0).tate j := by
  simp [causalManyLoopBirth, CausalHodgeCell.tate]

/-- The two smooth Hodge branches compose into a PURE diagonal
causal cell. Its rational algebraic realization is the independently
constructed diagonal Chow correspondence in the geometry derivation. -/
theorem causalSmoothOpposite_tensor_pure (j : ℕ) :
    ((causalSmoothLeftBirth 0).tensor (causalSmoothRightBirth 0)).tate j =
      ⟨2 + 2*j, 1+j, 1+j⟩ ∧
    ((causalSmoothLeftBirth 0).tensor (causalSmoothRightBirth 0)).purityGap =
      0 := by
  constructor
  · simp [causalSmoothLeftBirth, causalSmoothRightBirth,
      CausalHodgeCell.tensor, CausalHodgeCell.tate]
  · rw [CausalHodgeCell.purityGap_tensor]
    have hl := (causalSmoothBirth_signatures 0).2.2.1
    have hr := (causalSmoothBirth_signatures 0).2.2.2
    rw [hl, hr]
    norm_num


/-! ## GEOMETRIC CAUSAL MONODROMY WEIGHT DESCENT

The limiting mixed Hodge structure born from the actual Dwork toric
causal degeneration carries an operator N lowering the weight by two.
Its Hodge type is (-1,-1) between graded limit pieces. Unlike a
Tate dimension fold, this operation keeps cohomological degree fixed
while lowering BOTH realized Hodge coordinates. The coherence law
below makes the causal monodromy filtration a part of the same GST
Hodge genesis algebra as the earlier tensor/degree birth theorems.

A partial subtraction is used only on cells with enough Hodge weight;
the hypotheses on coordinates are explicit. This is a graded shadow
of the geometric limit MHS monodromy, not a claim that arbitrary
abstract GST cells or a fixed smooth fiber have a Chow monodromy map.
-/

/-- Monodromy lowers each Hodge-weight coordinate and preserves
cohomological degree of the limiting geometric world. -/
def CausalHodgeCell.monodromyLower (r : ℕ)
    (x : CausalHodgeCell) : CausalHodgeCell :=
  ⟨x.cohomologicalDegree, x.leftWeight - r, x.rightWeight - r⟩

/-- Signed charge remains fixed along the monodromy weight staircase
where the lowering operation is defined without truncation. -/
theorem CausalHodgeCell.charge_monodromyLower
    (r : ℕ) (x : CausalHodgeCell)
    (hl : r ≤ x.leftWeight) (hr : r ≤ x.rightWeight) :
    (x.monodromyLower r).charge = x.charge := by
  cases x with
  | mk k a b =>
    simp [CausalHodgeCell.monodromyLower,
      CausalHodgeCell.charge, CausalHodgeCell.cosmicAddress,
      cosmicCharge] at *
    omega

/-- One r-level step lowers the actual mixed Hodge purity gap
exactly by 2r, without changing the ambient cohomological degree. -/
theorem CausalHodgeCell.purityGap_monodromyLower
    (r : ℕ) (x : CausalHodgeCell)
    (hl : r ≤ x.leftWeight) (hr : r ≤ x.rightWeight) :
    (x.monodromyLower r).purityGap =
      x.purityGap - (2 * (r : ℤ)) := by
  cases x with
  | mk k a b =>
    simp [CausalHodgeCell.monodromyLower,
      CausalHodgeCell.purityGap, CausalHodgeCell.weight,
      CausalHodgeCell.cosmicAddress, cosmicDegree] at *
    omega

/-- Coherent successive causal weight folds agree with one combined
monodromy fold (the nontruncating geometric range is explicit). -/
theorem CausalHodgeCell.monodromyLower_comp
    (r s : ℕ) (x : CausalHodgeCell)
    (hl : r + s ≤ x.leftWeight)
    (hr : r + s ≤ x.rightWeight) :
    (x.monodromyLower r).monodromyLower s =
      x.monodromyLower (r+s) := by
  cases x with
  | mk k a b =>
    simp [CausalHodgeCell.monodromyLower]
    congr 1 <;> omega

#check CausalHodgeCell.charge_monodromyLower
#check CausalHodgeCell.purityGap_monodromyLower
#check CausalHodgeCell.monodromyLower_comp
#print axioms CausalHodgeCell.purityGap_monodromyLower

#check CausalHodgeCell.tensor_assoc
#check CausalHodgeCell.charge_tensor
#check CausalHodgeCell.purityGap_tensor
#check causalManyLoopBirth_signature
#check causalManyLoopBirth_succ
#check causalManyLoopBirth_tate
#check causalSmoothOpposite_tensor_pure
#print axioms causalManyLoopBirth_signature
#print axioms causalManyLoopBirth_succ

#check CausalHodgeCell.cosmicAddress_tate
#check CausalHodgeCell.charge_tate
#check CausalHodgeCell.purityGap_tate
#check causalNodalLoopBirth_signature
#check causalDoubleLoopBirth_signature
#check causalSmoothBirth_signatures
#check nodal_smooth_causal_genesis_is_nontrivial

#print axioms causalDoubleLoopBirth_signature
#print axioms causalSmoothBirth_signatures



/-! ## GST SIGNED CAUSAL DIMENSION BIRTH: OPEN/NODAL ARITY LAW

The mathematical geometric realization is established separately in
research/derivations/GST_signed_causal_purity_spectrum_2026-10-22.tex.

An OPEN algebraic torus loop contributes degree 1 and weight 2,
whereas a NODAL projective graph loop contributes degree 1 and weight 0.
These are independent causal births. Their joint operation therefore shifts
the purity gap by open arity minus nodal arity. It preserves Hodge charge and
commutes with symmetric Tate stabilization.

This is the exact *graded* shadow of actual smooth-open and singular-projective
worlds; it is not a new theorem constructing an arbitrary original-X
Chow representative, nor a formalization of the scheme/MHS comparison.
-/

/-- Independent a open and b nodal loops, without imposing a finite
dimension bound on either causal birth count. -/
def CausalHodgeCell.signedCausalFold (a b : ℕ)
    (x : CausalHodgeCell) : CausalHodgeCell :=
  ⟨x.cohomologicalDegree + a + b, x.leftWeight + a, x.rightWeight + a⟩

/-- Original rational (p,p) Hodge class signature before spatial folds. -/
def CausalHodgeCell.pureDiagonal (p : ℕ) : CausalHodgeCell :=
  ⟨2 * p, p, p⟩

/-- The GST signed Hodge charge is invariant under every pair of causal
birth counts, including mixed positive/negative topology operations. -/
theorem CausalHodgeCell.charge_signedCausalFold
    (a b : ℕ) (x : CausalHodgeCell) :
    (x.signedCausalFold a b).charge = x.charge := by
  cases x with
  | mk k p q =>
    simp [CausalHodgeCell.signedCausalFold,
      CausalHodgeCell.charge, CausalHodgeCell.cosmicAddress,
      cosmicCharge] <;> omega

/-- The signed purity gap is literally (open births - nodal births).
This is stronger than preserving the diagonal charge. -/
theorem CausalHodgeCell.purityGap_signedCausalFold
    (a b : ℕ) (x : CausalHodgeCell) :
    (x.signedCausalFold a b).purityGap =
      x.purityGap + (a : ℤ) - (b : ℤ) := by
  cases x with
  | mk k p q =>
    simp [CausalHodgeCell.signedCausalFold,
      CausalHodgeCell.purityGap, CausalHodgeCell.weight,
      CausalHodgeCell.cosmicAddress, cosmicDegree] <;> omega

/-- Causal birth composition combines both arities without truncation. -/
theorem CausalHodgeCell.signedCausalFold_comp
    (a b c d : ℕ) (x : CausalHodgeCell) :
    (x.signedCausalFold a b).signedCausalFold c d =
      x.signedCausalFold (a + c) (b + d) := by
  cases x with
  | mk k p q =>
    simp only [CausalHodgeCell.signedCausalFold]
    congr 1 <;> omega

/-- Pure original Hodge signatures have charge and purity gap zero. -/
theorem CausalHodgeCell.pureDiagonal_signature (p : ℕ) :
    (CausalHodgeCell.pureDiagonal p).charge = 0 ∧
    (CausalHodgeCell.pureDiagonal p).purityGap = 0 := by
  constructor
  · simp [CausalHodgeCell.pureDiagonal,
      CausalHodgeCell.charge, CausalHodgeCell.cosmicAddress,
      cosmicCharge]
  · simp [CausalHodgeCell.pureDiagonal,
      CausalHodgeCell.purityGap, CausalHodgeCell.weight,
      CausalHodgeCell.cosmicAddress, cosmicDegree] <;> omega

/-- Every original diagonal signature admits exact signed gap a-b while
remaining diagonal: a causal *degree* does not pre-fix Hodge purity. -/
theorem CausalHodgeCell.pureDiagonal_signedFold_signature
    (p a b : ℕ) :
    ((CausalHodgeCell.pureDiagonal p).signedCausalFold a b).charge = 0 ∧
    ((CausalHodgeCell.pureDiagonal p).signedCausalFold a b).purityGap =
       (a : ℤ) - (b : ℤ) := by
  constructor
  · rw [CausalHodgeCell.charge_signedCausalFold]
    exact (CausalHodgeCell.pureDiagonal_signature p).1
  · rw [CausalHodgeCell.purityGap_signedCausalFold]
    rw [(CausalHodgeCell.pureDiagonal_signature p).2]
    ring

/-- Open and nodal births cancel the purity gap at equal multiplicity.
This is a signature equality, NOT a smooth-projective realization theorem. -/
theorem CausalHodgeCell.balancedCausalFold_purity
    (a : ℕ) (x : CausalHodgeCell) :
    (x.signedCausalFold a a).purityGap = x.purityGap := by
  rw [CausalHodgeCell.purityGap_signedCausalFold]
  ring

#check CausalHodgeCell.charge_signedCausalFold
#check CausalHodgeCell.purityGap_signedCausalFold
#check CausalHodgeCell.signedCausalFold_comp
#check CausalHodgeCell.pureDiagonal_signedFold_signature
#check CausalHodgeCell.balancedCausalFold_purity
#print axioms CausalHodgeCell.purityGap_signedCausalFold
#print axioms CausalHodgeCell.pureDiagonal_signedFold_signature


end GSTGradedWorldAlgebra
